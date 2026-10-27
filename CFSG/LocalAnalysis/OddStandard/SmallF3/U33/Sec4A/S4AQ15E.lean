module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS27
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open CFSG.GH74.GLS.Bg.TwoGroups (E2 Z4Z4 commAut)

theorem q15_card_E2 (n : ℕ) : Nat.card (E2 n) = 2 ^ n := by
  rw [E2, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [Nat.card_zmod]

section Q15E

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q15_hs27 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    t ∉ l41Q1 t x₁ x₂ rho ∧ l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t ∧
      Nat.card (l41Q1 t x₁ x₂ rho) = 2 ^ 8 ∧
      (Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho) (E2 4) ∨
        Sec4SectionIso (l41Q1 t x₁ x₂ rho) (l41Y t x₁ x₂ rho) Z4Z4) := by
  haveI := q14_normal_YQ h
  have hρM : rho ∈ l41M t x₁ x₂ rho := q14_rho_mem_M h.toL41GPh8
  have hρQ : rho ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Q hρM
  have hρY : rho ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Y h hρM
  have hρ3 : rho ^ 3 = 1 := q15_rho_cube h.toL41GPh1
  have hY : l41Y t x₁ x₂ rho ≤ ⁅l41Q t x₁ x₂ rho, zpowers rho⁆ := q15_Y_le h
  have htQ : t ∈ l41Q t x₁ x₂ rho := q14_t_mem_Q h.toL41GPh8
  have htY : t ∉ l41Y t x₁ x₂ rho := fun hty =>
    h.rfacts.t_not_mem ((m13_Y_le_R t x₁ x₂ rho) hty)
  obtain ⟨-, hinf, hsup, -, -, hiso⟩ := Outside.HS27_card32
    (T := q15T t x₁ x₂ rho) q15_quot_isPGroup (q15_orderOf_tbar h) (q15_cent_tbar_E8 h)
    (q15_alpha_ne_one h) (q15_alpha_order h) (q15_alpha_tbar h) (q15_card_quot h)
  have hcardC : Nat.card ↥(commAut (q15Alpha h)) = 16 := by
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, q15_card_E2]
      norm_num
    · rw [Nat.card_congr e.toEquiv]
      exact CFSG.GH74.GLS.Bg.TwoGroups.card_Z4Z4
  have hcardC' : Nat.card ↥(commAut (quotConj (l41Q t x₁ x₂ rho) (l41Y t x₁ x₂ rho) rho hρQ hρY)) =
      16 := hcardC
  refine ⟨q15_t_not_mem hρ3 hρQ hρY hY htQ htY hinf, q15_Q_eq_sup hρ3 hρQ hρY hY htQ hsup, ?_, ?_⟩
  · have h1 := q15_card_commutator hρ3 hρQ hρY hY
    unfold l41Q1
    rw [h1, hcardC', m11_card_Y h]
    norm_num
  · rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl (q15_sectionIso_commutator hρ3 hρQ hρY hY e)
    · exact Or.inr (q15_sectionIso_commutator hρ3 hρQ hρY hY e)

end Q15E

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
