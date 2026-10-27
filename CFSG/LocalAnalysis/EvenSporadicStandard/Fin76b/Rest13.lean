module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611E

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def Fin76bInnerRest₁₃ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B S : Subgroup G), Hyp69 L z t T₀ E Q x β B S →
    BetaData65 E β →
    (∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩)) →
    Lemma69Out L z t E S → Lemma611Out E S B z t → False

theorem fin76bInnerRest₁₁_of_rest₁₃ (hE : Fin76bEFacts69) (hF : Fin76bFusion69)
    (hE611 : Fin76bEFacts611) (h13 : Fin76bInnerRest₁₃) : Fin76bInnerRest₁₁ := by
  intro G _ _ L z t T₀ E Q x β B hconf hW hBD S hS2 hSC hSmax hzS hD8 hBS hodd h66 h67 h68 h69
    _h610
  have hH : Hyp69 L z t T₀ E Q x β B S :=
    ⟨hconf, hW, hE G L z t T₀ E Q x β B hconf, hS2, hSC, hSmax, hzS, hD8, hBS, hodd, h67, h68,
      hF G L z t T₀ E Q x β B hconf hW hBD h66⟩
  exact (h13 G L z t T₀ E Q x β B S hH hBD h66 h69
    (hH.lemma611 (hE611 G L z t T₀ E Q x β B hconf) h66 hBD)).elim

end CFSG.EvenSporadicStandard.Fin76b
