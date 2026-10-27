module

public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem inf_le_kerIn_sup {K X M : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (X ⊓ M : Set G))
    (hXn : X ≤ Subgroup.normalizer (X ⊓ M : Set G)) :
    (X ⊓ M : Subgroup G) ≤ CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M (K ⊔ X) := by
  intro x hx
  rw [CFSG.LocalAnalysis.RankThreeUC.WeakClosure.mem_kerIn]
  refine ⟨(le_sup_right : X ≤ K ⊔ X) hx.1, fun h hh => ?_⟩
  have hN : h ∈ Subgroup.normalizer (X ⊓ M : Set G) :=
    (sup_le hK hXn : K ⊔ X ≤ Subgroup.normalizer (X ⊓ M : Set G)) hh
  have h1 : h * x * h⁻¹ ∈ X ⊓ M := ((Subgroup.mem_normalizer_iff.mp hN) x).mp hx
  exact (inf_le_right : X ⊓ M ≤ M) h1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
