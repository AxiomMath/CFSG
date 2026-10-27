module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkL3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkU3

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_pocket_of_isI4PlusIn_component [Finite G] {x : G} {X : Subgroup G}
    (hX : IsComponentIn X (centralizer ({x} : Set G))) (a : ↥X)
    (ha : IsI4PlusIn (⊤ : Subgroup ↥X) a) :
    ∃ (y : G) (K : Subgroup G), orderOf y = 2 ∧ K ≤ X ∧ Sl23Pocket x y K := by
  obtain ⟨hy2, K, hK⟩ := isI4PlusIn_of_top a.2 ha
  have hnorm := conjugate_eq_of_noncomm hX a.2 (exists_noncomm_of_sl23PocketIn hX.isQuasisimple hK)
  exact ⟨a, K, hy2, hK.2.1.trans inf_le_left, hK.of_normal_centralizer hX.le hnorm⟩

theorem asc82PocketExists_of_schur (hS : Asc82SchurU43) : Asc82PocketExists := by
  intro G _ _ x X _ hX hF
  obtain ⟨a, ha⟩ : ∃ a : ↥X, IsI4PlusIn (⊤ : Subgroup ↥X) a := by
    rcases hF with hF | hF
    · exact exists_isI4PlusIn_of_isFGroup hS hF
    · refine exists_isI4PlusIn_of_quotient ?_
      rcases hF with h | h
      · exact exists_isI4PlusIn_of_lieModel_psl33 h
      · exact exists_isI4PlusIn_of_lieModel_psu33 h
  exact exists_pocket_of_isI4PlusIn_component hX a ha

end CFSG.OddStandard.SmallF3.Omega
