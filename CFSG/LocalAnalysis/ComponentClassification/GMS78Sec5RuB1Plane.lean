module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1CentA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Ru
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Sylow

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3.B1Frame

variable {L T L₀ R R₂ : Subgroup G} {y d : G}

omit [Finite G] in
theorem le_centralizer_oddCoreIn (hfr : Sec3.B1Frame L T L₀) :
    L₀ ≤ centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) :=
  le_centralizer_iff.mp hfr.centralizer_eq.ge

theorem R_le
    (hfr : Sec3.B1Frame L T L₀) (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) : R ≤ L₀ := by
  intro r hr
  have hrN : r ∈ L₀ ⊔ AS76b.oddCoreIn (centralizer (L : Set G)) := by
    rw [← hfr.normalizer_eq]
    exact hM.le_normalizer_oddCoreIn_of_szR hS h4 hr
  obtain ⟨k, hk⟩ := hS.isR.isPGroup ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact mem_of_mem_sup_of_pow_two_pow_eq_one (AS76b.odd_card_oddCoreIn _) hfr.inf_eq
    hfr.centralizer_eq.ge hrN hrk

variable {μ : G → ℕ} {ν : G → Fin 8} {f : G} {X : Subgroup G}

end Sec3.B1Frame

end CFSG.ComponentClassification.GMS78
