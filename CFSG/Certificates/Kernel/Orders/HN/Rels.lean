module

public import Init

public section

namespace CFSG.KD.OrdHN

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true)], [(0, false), (0, false), (1, false), (0, true), (0, true), (1, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)], [(0, false), (0, false), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (1, false)], [(2, true), (2, true), (0, true), (0, true)], [(0, false), (2, false), (0, true), (2, true)], [(1, false), (0, false), (1, false), (2, false), (1, true), (0, true), (1, true), (2, true)], [(1, true), (0, true), (1, true), (1, true), (1, true), (2, true), (1, true), (0, true), (1, true), (1, true), (1, true), (2, true), (1, true), (0, true), (1, true), (1, true), (1, true), (2, true)], [(3, true), (3, true)], [(0, true), (3, true), (0, true), (3, true)], [(1, false), (3, false), (1, true), (3, true)], [(1, true), (2, false), (1, false), (2, false), (3, true), (2, true), (1, true), (2, true), (1, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(4, true), (4, true), (4, true), (4, true), (4, true)], [(0, false), (4, true), (0, true), (4, true), (4, true)], [(2, false), (4, true), (2, true), (4, false), (4, false)], [(4, false), (1, false), (4, true), (1, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)]]

end CFSG.KD.OrdHN

end
