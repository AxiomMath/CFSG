module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514B1823

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

open CFSG.HardMathSupport.Solomon.LocalBalance in
theorem l514b_input18_3_23_simple (hS : CatalogueRelativeB.CatalogueSchreier)
    (i145 : LocalBalance.Lemma27Ns.Input14_5) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = 3 → orderOf y = 3 → x * y = y * x →
        ∀ J : Subgroup G,
          GLAPComponent 3 (GLAPLayer 3 (Cs x) ⊓ Cs y) J →
            GLAPComponent 3 (GLAPLayer 3 (ncl (GLAPLayer 3 (Cs y)) J ⊓ Cs x)) J ∧
            ∃ hx : x ∈ Cs y,
              IsComponentOf (barX 3 (Cs y) J)
                (barX 3 (Cs y) (ncl (GLAPLayer 3 (Cs y)) J) ⊓
                  Subgroup.centralizer ({(QuotientGroup.mk ⟨x, hx⟩ :
                    ↥(Cs y) ⧸ GLAPPrimeCore 3 ↥(Cs y))} : Set (↥(Cs y) ⧸ GLAPPrimeCore 3 ↥(Cs y)))) := by
  intro G _ _ _ hnab hKP x y hx3 hy3 hxy J hJ
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy3; omega
  have hyc : y ∉ Subgroup.center G := by
    intro hyc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hy1 (Subgroup.mem_bot.1 (h ▸ hyc))
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
  exact l514b_input18_3_23_of_input14_5 hS i145 hKP hx3 hxy hyc hJ

end CFSG.HardMathSupport.Solomon.Coordinator
