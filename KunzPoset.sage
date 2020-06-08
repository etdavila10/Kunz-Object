from sage.combinat.posets.posets import FinitePoset

class KunzPoset:
    def __init__(self, m, cover_relations = None, hyperplane_desc = None, \
            semigroup_gens = None, face_desc = None, hplane_list = None):
        # Set the multiplicity for our KunzPoset
        self.m = m

        # Assuming cover_relations is list of lists
        # Implementation for dictionary later
        if (cover_relations is not None):
            self.cover_relations = [(i,j) for (i,j,k) in \
                    DiGraph(cover_relations).transitive_reduction().edges()]
            self.hyperplane_desc = self._generate_h_desc()

        # Hyperplane description will be a list of lists
        elif (hyperplane_desc is not None):
            self.hyperplane_desc = hyperplane_desc
            self.cover_relations = self._generate_cover_relations()

        # This should just be a list or a tuple
        elif (semigroup_gens is not None):
            self.semigroup_gens = semigroup_gens
            self.cover_relations = self._generate_cover_relations()
            self.hyperplane_desc = self._generate_h_desc()

        ##### EXPERIMENTAL #####
        elif (face_desc is not None and hplane_list is not None):
            self.face_desc = face_desc
            self.hplane_list = hplane_list

            self.hyperplane_desc = []
            for index, equality in enumerate(self.face_desc):
                if(int(equality)):
                    self.hyperplane_desc.append(self.hplane_list[index])
            self.cover_relations = self._generate_cover_relations()

        else:
            print("You did not pass in any data!")
            print("You can pass cover relations,")
            print("A hyperplane description,")
            print("or semigroup generators (Requires semigroup package)")

        # Make the poset
        self.poset = self._generate_poset()

        # atoms of the poset
        self.atoms = [j for (i,j) in self.cover_relations if (i == 0)]

    # When someone puts object in a print statement
    def __repr__(self):
        return "This is a KunzPoset!!"

    def _generate_cover_relations(self):
        # Means we are calling from semigroup_gens if statement
        if (not hasattr(self, "hyperplane_desc")):
            try:
                self.S = NumericalSemigroup(self.semigroup_gens)
            except:
                print("You need NumericalSemigroup package")
                return

            apery_set = self.S.AperySet(self.m)
            covers = []

            for i, a_i in enumerate(apery_set):
                cover = [i]
                for j, a_j in enumerate(apery_set):
                    if (a_j - a_i in self.S and i != j):
                        covers.append([i,j])
            return [(i,j) for (i,j,k) in \
                    DiGraph(covers).transitive_reduction().edges()]

        # Means we are calling from hyperplane_desc if statement
        # Assuming h_desc does not have the zero column
        else:
            relations = []
            for ieq in self.hyperplane_desc:
                relation = []
                for index, element in enumerate(ieq):
                    if (element == 1):
                        relation.append(index + 1)
                    elif (element == 2):
                        relation += 2 * [index + 1]
                    elif (element == -1):
                        result = index + 1

                relation.append(result)
                relations.append(relation)

            rels = [(i,k) for (i,j,k) in relations] + \
                   [(j,k) for (i,j,k) in relations]
            zero = [(0,n) for n in range(1, self.m)]
            rels += zero
            return [(i,j) for (i,j,k) in \
                    DiGraph(rels).transitive_reduction().edges()]


    # Generate the hyperplane description
    # Assuming cover relations have already been computed
    def _generate_h_desc(self):
        relations = copy(self.cover_relations)
        full_relations = []
        seen_relations = []

        while len(relations) > 0:
            if (relations[0][0] == 0):
                relations.pop(0)
            elif (tuple(relations[0]) in seen_relations):
                relations.pop(0)
            else:
                full_relation = (relations[0][0], \
                        (relations[0][1] - relations[0][0]) % self.m, \
                        relations[0][1])
                seen_relations.append(((relations[0][1] - relations[0][0]) \
                        % self.m, relations[0][1]))
                full_relations.append(full_relation)
                relations.pop(0)

            h_desc = []

            for full_relation in full_relations:
                ieq = (self.m - 1) * [0]
                ieq[full_relation[0] - 1] += 1
                ieq[full_relation[1] - 1] += 1
                ieq[full_relation[2] - 1] = -1
                h_desc.append(ieq)

            return h_desc

    # generating the poset
    def _generate_poset(self):
        return FinitePoset(DiGraph(self.cover_relations).transitive_reduction())

    def face(self):
        if (not hasattr(self, "face")):
            self.face = Polyhedron(self.hyperplane_desc)
        return self.face

    def _make_factorizations(self, VERBOSE = False):
        # Need minimal gens and order in which to check elements
        minimal_elements = self.atoms
        order = self.poset.linear_extension()

        # Declare dictionaries
        gen_index = {}
        factorizations = {}

        # Know which index to increment
        for i, gen in enumerate(minimal_elements):
            gen_index.setdefault(gen, i)

        # Main nested for loop
        for element in order:
            factorizations.setdefault(element, [])

            # Check each generator
            for gen in minimal_elements:
                if element == 0:
                    factorizations[element].append([0] * len(minimal_elements))
                    break

                difference = (element - gen) % self.m
                if (self.poset.compare_elements(element, difference) == 1):
                    for factorization in factorizations[difference]:
                        temp = copy(factorization)
                        temp[gen_index[gen]] += 1
                        if (temp not in factorizations[element]):
                            factorizations[element].append(temp)

        self._factorizations = factorizations

    def factorization(self, element = None):
        if (not hasattr(self, "_factorizations")):
            self._make_factorizations()
        return self._factorizations[element] if element is not None else \
                self._factorizations

    # Function needed for find_num_bettis_graph
    def _generate_bin(self, num_list):
        return '0b' + ''.join(['1' if num > 0 else '0' for num in num_list])

    def _find_num_bettis_graph(self, VERBOSE = False):

        bettis = {}

        for element, factorization in self._factorizations.items():
            # Only go through process if more than one factorization exists
            # for an element of the poset
            if (len(factorization) > 1):
                # initialize both representations
                binary_rep = [self._generate_bin(factorization[0])]
                real_rep = [[factorization[0]]]

                # Test each new relation against others
                for rel in factorization[1:]:
                    binary_rel = self._generate_bin(rel)
                    groups_added_to = []
                    i = 0

                    # Compare new relation aginst others already grouped
                    while (i < len(real_rep)):
                        binary_add = int(binary_rep[i],2) & int(binary_rel,2)
                        if (binary_add != 0):
                            groups_added_to.append(i)

                        i += 1

                    # Goes through and connects groups that are now connected
                    # through new relation
                    if (len(groups_added_to) > 1):
                        start = groups_added_to[0]
                        for i in range(len(groups_added_to)-1, 0, -1):
                            index = groups_added_to[i]

                            real_rep[start] += real_rep[index]
                            binary_rep[start] = bin(int(binary_rep[start],2) \
                                                  | int(binary_rep[index],2))

                            real_rep.pop(index)
                            binary_rep.pop(index)

                        real_rep[start] += [rel]
                        binary_rep[start] = bin(int(binary_rep[start],2) | \
                                                int(binary_rel,2))

                    # Adds the relation to the group it belongs to
                    elif (len(groups_added_to) == 1):
                        index = groups_added_to[0]
                        binary_rep[index] = bin(int(binary_rep[index],2) | \
                                                int(binary_rel,2))
                        real_rep[index].append(rel)

                    # Creates a new group since the new relation was not
                    # connected to anything
                    else:
                        binary_rep.append(binary_rel)
                        real_rep.append([rel])

                # Connect the different groups
                if (len(real_rep) > 1):
                    bettis[element] = []
                    for rep in real_rep[1:]:
                        relation = list(map(operator.sub, real_rep[0][0], rep[0]))
                        bettis[element].append(relation)

        self._bettis = bettis
        self._make_relation_matrix()

    def betti(self, element = None):
        if (not hasattr(self, '_factorizations')):
            self._make_factorizations()
        if (not hasattr(self, '_bettis')):
            self._find_num_bettis_graph()

        return self._bettis[element] if element is not None else \
                self._bettis

    def betti_matrix(self):
        if (not hasattr(self, '_factorizations')):
            self._make_factorizations()
        if (not hasattr(self, '_bettis')):
            self._find_num_bettis_graph()

        return self._betti_matrix

    def _make_relation_matrix(self):
        betti_matrix = []
        for betti in self._bettis:
            for relations in self._bettis[betti]:
                betti_matrix.append([rel for rel in relations])

        self._betti_matrix = matrix(betti_matrix)

    def dimension(self):
        if (not hasattr(self, '_factorizations')):
            self._make_factorizations()
        if (not hasattr(self, '_bettis')):
            self._find_num_bettis_graph()

        return len(self.atoms) - self._betti_matrix.rank()
