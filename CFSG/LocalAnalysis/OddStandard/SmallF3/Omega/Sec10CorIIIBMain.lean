module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIII
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBPocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBArith
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem c3b_card_quot_center_of_inF {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : InF L) :
    Nat.card (L ⧸ center L) = 25920 ∨ Nat.card (L ⧸ center L) = 6065280 ∨
      Nat.card (L ⧸ center L) = 3265920 ∨ Nat.card (L ⧸ center L) = 4585351680 ∨
      Nat.card (L ⧸ center L) = 4952179814400 ∨ Nat.card (L ⧸ center L) = 10151968619520 := by
  obtain ⟨hq, hQ | hQ⟩ := h
  · rcases hQ with h | h | h | h | h | h
    · exact Or.inl (ctrQ_of_psp4 hq h)
    · exact Or.inr (Or.inl (ctrQ_of_l43 hq h))
    · exact Or.inr (Or.inr (Or.inl (ctrQ_of_u43 hq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ctrQ_of_omega7 hq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ctrQ_of_omega8plus hq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ctrQ_of_omega8minus hq h)))))
  · exact Or.inr (Or.inr (Or.inl (ctrQ_of_twoU43 hq hQ)))

theorem c3b_nonabelian_of_inF {G : Type} [Group G] {L : Subgroup G} (h : InF L) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨⟨-, -, a, b, hab⟩, -⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  have hL : a * b = b * a := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]

theorem c3b_center_eq_bot {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center G := by
      rw [h]
      exact mem_top a
    exact absurd (mem_center_iff.mp ha b).symm hab

section M11

theorem c3b_false_of_m11 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G} (hL : InF L)
    (h : NativeSporadic.IsSporadic (CFSG.Open.genFittingFStar G) .M11) : False := by
  obtain ⟨eF⟩ := c3b_nonempty_genFittingFStar_equiv hnab
  obtain ⟨e⟩ := h
  have hG : Nat.card G = 7920 := (Nat.card_congr eF.toEquiv).symm.trans
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11)
  have h1 : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card L :=
    Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
  have h2 : Nat.card L ≤ Nat.card G := card_le_card_group L
  have h3 := c3b_card_quot_center_of_inF hL
  omega

theorem asc82CorIII_of_orders
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) : Asc82CorIII := by
  intro G _ _ t L hS z hz
  haveI : IsSimpleGroup G := hS.simple
  have hnab : ∃ a b : G, a * b ≠ b * a := c3b_nonabelian_of_inF hS.inF
  obtain ⟨hFs, hFnab⟩ := c3b_genFittingFStar_simple hnab
  haveI := hFs
  obtain ⟨eF⟩ := c3b_nonempty_genFittingFStar_equiv hnab
  rcases c3b_oddLieType_or_m11_of_isI4PlusIn hCI hFnab hz with
    ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ | hM11
  · have hmG : LieModel G τ n p f := LieModel.of_mulEquiv eF hm
    by_cases hp3 : p = 3
    · subst hp3
      exact hS.notChev3 ⟨τ, n, f, hadm, hmG⟩
    · rcases c3b_lieModel_of_component hCL1 (c3b_center_eq_bot hnab) hp hp2 hadm hmG
          hS.involution hS.component with ⟨τ', n', f', hadm', hm'⟩ | h3
      · obtain ⟨-, hmul, hfac⟩ := hO _ τ' n' p f' hadm' hm'
        exact c3b_false_of_fOrder hadm' hp2 hp3 hmul hfac (c3b_card_quot_center_of_inF hS.inF)
      · exact hp3 h3
  · exact c3b_false_of_m11 hnab hS.inF hM11

end M11

end CFSG.OddStandard.SmallF3.Omega
