module

public import CFSG.ClassicalInvolution.Uniform.U5Three
public import CFSG.GH74.SmallRanks
public import CFSG.GH74.Generic.S1.KL3SL3
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.UExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement



section Model

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exactMembers_of_ih8Model {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    ExactMembers Ω := by
  have he : e = 1 := M.exp_eq_f hD4
  intro L hL
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  obtain ⟨z, hz⟩ := hΩ.classical _ hL
  obtain ⟨eR⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hR
  have hs : (MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  have hRcard : Nat.card R = 24 := by
    rw [Nat.card_congr eR.toEquiv, he]
    exact natCard_sl2_galoisField_three
  have hdvd : Nat.card ↥(R.map M.ψ) ∣ 24 := hRcard ▸ Subgroup.card_map_dvd R M.ψ
  obtain ⟨eL⟩ := hz.nonempty_equiv_sl2Three hs
  have h24 : Nat.card (↥(R.map M.ψ) ⧸ CFSG.Open.classicalInvolutionOddCore ↥(R.map M.ψ)) = 24 := by
    rw [Nat.card_congr eL.toEquiv]
    exact natCard_sl2Three
  have h24' : 24 ∣ Nat.card ↥(R.map M.ψ) := by
    rw [← h24]
    exact Subgroup.card_quotient_dvd_card _
  exact hz.oddCore_eq_bot_of_natCard_eq hs (Nat.dvd_antisymm hdvd h24')

theorem bounds_of_ih8Model_three [IsSimpleGroup G] {t : StatedLieTag} {k e : ℕ}
    (M : Ih8Model 3 1 Ω t k e) (ht : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) :
    ¬ 2 ^ 6 ∣ Nat.card G ∧ CFSG.Open.twoRank G ≤ 2 := by
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have he : e = 1 := M.exp_eq_f hD4
  subst he
  have hQ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t k 3 1 Nat.prime_three
    M.isFundTag M.admissible
  have hψ1 : ∃ x, M.ψ x ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨x, rfl⟩ := M.surj g
    exact ⟨x, hg⟩
  have hLM := CFSG.ClassicalInvolution.Balance.lieModel_of_surjective hQ.1 M.ψ M.surj hψ1 hQ.2
  have hcen : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hψ1
      apply hx
      have hle : commutator (modelUniv t k 3 1 Nat.prime_three).K ≤ M.ψ.ker := by
        refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have hb : M.ψ b ∈ Subgroup.center G := h ▸ Subgroup.mem_top _
        exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp hb (M.ψ a))
      have hx' : x ∈ commutator (modelUniv t k 3 1 Nat.prime_three).K := hQ.1.1 ▸ Subgroup.mem_top _
      exact hle hx'
  let eq : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hLM' : CFSG.Blueprint.LieModel G t k 3 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eq hLM
  have hdvd := Subgroup.card_dvd_of_surjective M.surj
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hF : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 (by norm_num)]
      norm_num
    have hK : Nat.card (modelUniv .PSL 3 3 1 Nat.prime_three).K = 5616 :=
      CFSG.GH74.Generic.S1.kl3_card_sl3 (F := GaloisField 3 1) hF
    refine ⟨fun h => ?_, CFSG.GH74.twoRank_le_two_of_lieModel_PSL_three_three hLM'⟩
    have := h.trans (hK ▸ hdvd)
    norm_num at this
  · have hF9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
      CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
    have hK : Nat.card (modelUniv .PSU 3 3 1 Nat.prime_three).K = 6048 := by
      have h := CFSG.LieType.Steinberg.card_SU_three (F := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        hF9
      have h6048 : (3 ^ 1) ^ 3 * (((3 : ℕ) ^ 1) ^ 2 - 1) * ((3 ^ 1) ^ 3 + 1) = 6048 := by
        norm_num
      rw [h6048] at h
      exact h
    refine ⟨fun h => ?_, CFSG.GH74.twoRank_le_two_of_lieModel_PSU_three_three hLM'⟩
    have := h.trans (hK ▸ hdvd)
    norm_num at this

theorem ih8ThreeU_proved : Ih8ThreeU := by
  intro G _ _ _ Ω hΩ _ t k e hM ht
  obtain ⟨M⟩ := hM
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hG2 : t ≠ .G2 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hex := exactMembers_of_ih8Model M hΩ hG2 hD4
  obtain ⟨h64, hrank⟩ := bounds_of_ih8Model_three M ht
  have key : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∉ omegaNbr Ω K := fun K hK J _ hnbr =>
    false_of_omegaNbr_of_small hΩ hex h64 hrank hK hnbr
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J hJ h
  · exact key J hJ K hK h

end Model

end CFSG.ClassicalInvolution.Uniform
