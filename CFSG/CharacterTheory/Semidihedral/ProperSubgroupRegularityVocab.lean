module

public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.Semidihedral.ProperSubgroupRegularity

open CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m11Word (w : List (Fin 3)) : NativeSporadic.M11 :=
  (w.map fun i => if i = 0 then m11a else if i = 1 then m11b else m11b⁻¹).prod

@[expose] def m11Rotation : NativeSporadic.M11 :=
  m11Word [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2]

@[expose] def m11Reflection : NativeSporadic.M11 := m11Word [2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]

@[expose] def m11LocalThree : NativeSporadic.M11 :=
  m11Word [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1]

@[expose] def m11TwoCoordinates (x : Fin 8 × Fin 2) : NativeSporadic.M11 :=
  m11Rotation ^ x.1.val * m11Reflection ^ x.2.val

@[expose] def m11CentralizerCoordinates (x : (Fin 8 × Fin 2) × Fin 3) : NativeSporadic.M11 :=
  m11TwoCoordinates x.1 * m11LocalThree ^ x.2.val

@[expose] def m11InvolutionConjugator : Fin 5 → NativeSporadic.M11 := ![m11Word [1, 0, 2, 0, 1],
    m11Word [1, 0, 1, 0, 2, 0, 2],
    m11Word [],
    m11Word [2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1],
    m11Word [1, 1, 0, 1, 0, 1, 1, 0, 1]]

@[expose] def m11CentralizerBase : Fin 4 → Fin 11 := ![0, 2, 5, 1]

abbrev M11CentralizerImages :=
  {a : Fin 4 → Fin 11 // Function.Injective a ∧
    (∀ i : Fin 3, m11gA (a i.castSucc) = a i.castSucc) ∧ m11gA (a 3) ≠ a 3}

end CFSG.Semidihedral.ProperSubgroupRegularity
