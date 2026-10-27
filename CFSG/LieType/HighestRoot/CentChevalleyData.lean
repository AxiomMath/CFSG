module

public import CFSG.LieType.HighestRoot.CentChevalley

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def witF4 : List ℕ :=
  [0, 0, 39048, 35208, 0, 0, 0, 0, 0, 39048, 35208, 35208, 0, 0, 0, 0, 0, 0, 0, 35208, 0, 39048,
    0, 0, 0, 0, 0, 0, 39048, 0, 35208, 0, 0, 0, 35208, 35208, 35208, 0, 35208, 0, 35208, 35208, 0,
    0, 39048, 35208, 0, 39048]

@[expose] def witE6 : List ℕ :=
  [0, 8951944, 0, 8947864, 8951944, 9013384, 0, 0, 8951944, 8947864, 0, 0, 8947864, 8947864,
    8951944, 8951944, 9013384, 0, 0, 8947864, 0, 8947864, 0, 0, 8947864, 8947864, 8951944, 0, 0,
    0, 0, 8947864, 0, 8947864, 0, 0, 8947864, 0, 0, 0, 0, 0, 8947864, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 9996424, 0, 0, 0, 9996424, 0, 9013384, 0, 0, 9013384, 0, 8951944, 8951944, 8947864,
    8947864, 8947864, 8947864]

@[expose] def witE7 : List ℕ :=
  [0, 143169672, 0, 143165592, 143169672, 143231112, 144214152, 0, 0, 143169672, 143165592, 0, 0,
    143165592, 143165592, 143169672, 143169672, 143231112, 143231112, 144214152, 0, 0, 143165592,
    0, 143165592, 0, 0, 143165592, 143165592, 143169672, 143169672, 143231112, 0, 0, 0, 0,
    143165592, 0, 143165592, 0, 0, 143165592, 143165592, 143169672, 0, 0, 0, 0, 0, 143165592, 0,
    0, 143165592, 0, 0, 143165592, 0, 0, 0, 0, 0, 0, 0, 143165592, 0, 0, 0, 0, 0, 0, 144214152, 0,
    0, 0, 0, 0, 0, 144214152, 0, 0, 143231112, 0, 0, 0, 0, 0, 143231112, 0, 0, 143169672,
    143231112, 0, 0, 0, 143169672, 143231112, 0, 143165592, 143169672, 0, 0, 143165592, 143169672,
    0, 143165592, 143165592, 143169672, 143165592, 143165592, 143169672, 143165592, 143165592,
    143165592, 143165592, 143165592, 143165592, 143165592, 143165592, 143165592, 143165592,
    143169672, 143169672, 0, 0, 0, 0]

@[expose] def witE8 : List ℕ :=
  [0, 2290653320, 0, 2290649240, 2290653320, 2290714760, 2291697800, 2307426440, 0, 0, 2290653320,
    2290649240, 0, 0, 2290649240, 2290649240, 2290653320, 2290653320, 2290714760, 2290714760,
    2291697800, 2291697800, 2307426440, 0, 0, 2290649240, 0, 2290649240, 0, 0, 2290649240,
    2290649240, 2290653320, 2290653320, 2290714760, 2290714760, 2291697800, 0, 0, 0, 0,
    2290649240, 0, 2290649240, 0, 0, 2290649240, 2290649240, 2290653320, 2290653320, 2290714760,
    0, 0, 0, 0, 0, 2290649240, 0, 0, 2290649240, 0, 0, 2290649240, 2290649240, 2290653320, 0, 0,
    0, 0, 0, 0, 0, 2290649240, 0, 0, 2290649240, 0, 0, 2290649240, 0, 0, 0, 2291697800, 0, 0, 0,
    0, 0, 2290649240, 0, 0, 0, 0, 2291697800, 0, 0, 0, 2290714760, 0, 0, 0, 0, 0, 0, 0, 0,
    2290714760, 0, 0, 0, 2290653320, 2290714760, 0, 0, 0, 0, 0, 0, 2290653320, 2290714760, 0, 0,
    2290649240, 2290653320, 2290714760, 0, 0, 0, 0, 0, 2290649240, 2290653320, 2290714760, 0, 0,
    2290649240, 2290649240, 2290653320, 2290653320, 0, 0, 0, 2290649240, 2290649240, 2290653320,
    2290653320, 0, 2290649240, 2290649240, 2290649240, 2290653320, 0, 0, 2290649240, 2290649240,
    2290649240, 2290653320, 0, 2290649240, 2290649240, 2290649240, 2290649240, 2290653320,
    2290649240, 2290649240, 2290649240, 2290649240, 2290653320, 2290649240, 2290649240,
    2290649240, 2290649240, 2290649240, 2290649240, 2290649240, 2290649240, 2290653320,
    2290649240, 2290649240, 2290649240, 2290653320, 2290649240, 2290649240, 2290649240, 0,
    2290653320, 2290649240, 2290649240, 0, 2290653320, 2290649240, 2290649240, 0, 0, 2290653320,
    2290649240, 0, 0, 2290653320, 2290649240, 0, 0, 2290653320, 0, 0, 2290653320, 0, 0,
    2290714760, 0, 0, 2290714760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2290649240, 0,
    2290649240, 2290649240, 2290649240, 2290653320, 2290653320, 2290714760, 2290714760,
    2291697800, 2291697800, 2307426440, 2307426440, 2559084680, 2559084680]

abbrev idx0 (τ : Tag) (h : 0 < τ.rank := by decide) : Fin τ.rank := ⟨0, h⟩

theorem isolatedCheck_F4 : isolatedCheck .F4 (idx0 .F4) witF4 = true := by decide +kernel

theorem isolatedCheck_E6 : isolatedCheck .E6 (idx0 .E6) witE6 = true := by decide +kernel

theorem isolatedCheck_E7 : isolatedCheck .E7 (idx0 .E7) witE7 = true := by decide +kernel

theorem isolatedCheck_E8 : isolatedCheck .E8 (idx0 .E8) witE8 = true := by decide +kernel

theorem symmetrizer_le_F4 (j : Fin (Tag.rank .F4)) :
    Tag.symmetrizer .F4 j j ≤ Tag.symmetrizer .F4 (idx0 .F4) (idx0 .F4) := by
  fin_cases j <;> decide

theorem symmetrizer_le_one (τ : Tag) (hτ : τ.symmetrizer = 1) (i j : Fin τ.rank) :
    τ.symmetrizer j j ≤ τ.symmetrizer i i := by
  simp [hτ]

theorem noG2_E6' : NoG2 .E6 := fun _ => Or.inl (by simp [Tag.symmetrizer])

theorem noG2_E7' : NoG2 .E7 := fun _ => Or.inl (by simp [Tag.symmetrizer])

variable {K : Type} [Field K]

theorem centralizer_le_normalizer_F4
    (hK : ringChar K ≠ 2) {z : adjointGroup .F4 K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily .F4) K) (Pi.single (idx0 .F4) 1))
    (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup .F4 K)) ≤
      Subgroup.normalizer
        ((rankOneGroup (adjDatum (rootOperatorFamily .F4) K) (Pi.single (idx0 .F4) 1) :
          Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) :=
  centralizer_le_normalizer_rankOneGroup noG2_F4 hK symmetrizer_le_F4 isolatedCheck_F4 hz h2

theorem centralizer_le_normalizer_E6
    (hK : ringChar K ≠ 2) {z : adjointGroup .E6 K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily .E6) K) (Pi.single (idx0 .E6) 1))
    (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) ≤
      Subgroup.normalizer
        ((rankOneGroup (adjDatum (rootOperatorFamily .E6) K) (Pi.single (idx0 .E6) 1) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) :=
  centralizer_le_normalizer_rankOneGroup noG2_E6' hK (symmetrizer_le_one .E6 rfl _)
    isolatedCheck_E6 hz h2

theorem centralizer_le_normalizer_E7
    (hK : ringChar K ≠ 2) {z : adjointGroup .E7 K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (idx0 .E7) 1))
    (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup .E7 K)) ≤
      Subgroup.normalizer
        ((rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (idx0 .E7) 1) :
          Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) :=
  centralizer_le_normalizer_rankOneGroup noG2_E7' hK (symmetrizer_le_one .E7 rfl _)
    isolatedCheck_E7 hz h2

theorem centralizer_le_normalizer_E8
    (hK : ringChar K ≠ 2) {z : adjointGroup .E8 K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily .E8) K) (Pi.single (idx0 .E8) 1))
    (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup .E8 K)) ≤
      Subgroup.normalizer
        ((rankOneGroup (adjDatum (rootOperatorFamily .E8) K) (Pi.single (idx0 .E8) 1) :
          Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) :=
  centralizer_le_normalizer_rankOneGroup noG2_E8 hK (symmetrizer_le_one .E8 rfl _)
    isolatedCheck_E8 hz h2

end CFSG.LieType.HighestRoot
