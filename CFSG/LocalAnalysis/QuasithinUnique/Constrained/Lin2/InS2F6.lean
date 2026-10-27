module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F5

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_of_sq {E : Subgroup G} (hsq : ∀ e ∈ E, e * e = 1) : IsElemAbelian 2 E :=
  C5.isElemAbelian_two_iff.2 ⟨comm_of_sq hsq, fun a ha => by rw [pow_two]; exact hsq a ha⟩

omit [Finite G] in
theorem sq_of_isElemAbelian {E : Subgroup G} (h : IsElemAbelian 2 E) : ∀ e ∈ E, e * e = 1 :=
  fun e he => by
    have := (C5.isElemAbelian_two_iff.1 h).2 e he
    rwa [pow_two] at this

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem isMax_Q : IsMaxElemAbelian S (blockU L ⊔ conjR (blockU L) t) := by
  have h := O.base.su.isMax_DU
  rw [O.hC, bot_sup_eq] at h
  exact h

theorem four_le_q : 4 ≤ q := by
  have hB := O.base
  have h1 := lin2_card_U hB.hlin
  rw [hB.blockZ_eq_bot O.hC, Subgroup.card_bot, mul_one] at h1
  have h2 := O.UT3_R₁.card_U
  have h3 : 16 ≤ q ^ 2 := by
    rw [← h2, h1]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by have := hB.hn; omega)
  by_contra hlt
  push Not at hlt
  nlinarith

theorem card_Q : Nat.card ↥(blockU L ⊔ conjR (blockU L) t) = q ^ 4 := by
  have hB := O.base
  have hN : conjR (blockU L) t ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha b hb =>
      hB.comm_elem a (blockU_le L ha) b (conjR_mono (blockU_le L) t hb)
  have h := card_sup_mul_card_inf hN
  have hbot : conjR (blockU L) t ⊓ blockU L = ⊥ := by
    rw [eq_bot_iff, ← hB.L_inf_L₂, inf_comm]
    exact inf_le_inf (blockU_le L) (conjR_mono (blockU_le L) t)
  rw [hbot, Subgroup.card_bot, mul_one, sup_comm, card_conjR, O.UT3_R₁.card_U] at h
  rw [h]
  ring

theorem card_lt_q4_of_not_le_S {A : Subgroup G} (hA : A ≤ M₀) (hsq : ∀ e ∈ A, e * e = 1)
    (hAS : ¬ A ≤ S) : Nat.card A < q ^ 4 := by
  have hB := O.base
  obtain ⟨a, haA, haS⟩ : ∃ a ∈ A, a ∉ S := by
    by_contra h
    push Not at h
    exact hAS h
  have h1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
    have e1 : Nat.card A = Nat.card ↥(A ⊓ S) * (A ⊓ S).relIndex A :=
      C5.card_eq_card_mul_relIndex inf_le_left
    have e2 : (A ⊓ S).relIndex A = S.relIndex A := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have e3 : S.relIndex A ≤ S.relIndex M₀ :=
      Subgroup.relIndex_le_of_le_right hA (by rw [hB.h2]; omega)
    rw [hB.h2] at e3
    calc Nat.card A = Nat.card ↥(A ⊓ S) * (A ⊓ S).relIndex A := e1
      _ ≤ Nat.card ↥(A ⊓ S) * 2 := by rw [e2]; exact Nat.mul_le_mul_left _ e3
      _ = 2 * Nat.card ↥(A ⊓ S) := mul_comm _ _
  have h2 : Nat.card ↥(A ⊓ S) ≤ 4 * Nat.card ↥(A ⊓ S ⊓ thompsonJ S) :=
    O.card_le_four_mul inf_le_right (fun e he => hsq e he.1)
  have h3 : Nat.card ↥(A ⊓ S ⊓ thompsonJ S) ≤ Nat.card ↥(A ⊓ thompsonJ S) :=
    Subgroup.card_le_of_le fun x hx => ⟨hx.1.1, hx.2⟩
  have h4 : Nat.card ↥(A ⊓ thompsonJ S) ≤ q ^ 2 := O.card_inf_R_le_sq hA hsq haA haS
  have hq := O.four_le_q
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 2 := by omega
  calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := h1
    _ ≤ 2 * (4 * Nat.card ↥(A ⊓ S ⊓ thompsonJ S)) := Nat.mul_le_mul_left 2 h2
    _ ≤ 2 * (4 * q ^ 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 4 (h3.trans h4))
    _ < q ^ 4 := by nlinarith

theorem card_le_q4 {A : Subgroup G} (hA : A ≤ M₀) (hsq : ∀ e ∈ A, e * e = 1) :
    Nat.card A ≤ q ^ 4 := by
  by_cases hAS : A ≤ S
  · have := O.isMax_Q.2.2 A hAS (isElemAbelian_of_sq hsq)
    rwa [O.card_Q] at this
  · exact (O.card_lt_q4_of_not_le_S hA hsq hAS).le

theorem le_R_of_q4_le_card {A : Subgroup G} (hA : A ≤ M₀) (hsq : ∀ e ∈ A, e * e = 1)
    (hc : q ^ 4 ≤ Nat.card A) : A ≤ thompsonJ S := by
  by_cases hAS : A ≤ S
  · have hmax : IsMaxElemAbelian S A := by
      refine ⟨hAS, isElemAbelian_of_sq hsq, fun B' hB'S hB'e => ?_⟩
      have := O.isMax_Q.2.2 B' hB'S hB'e
      rw [O.card_Q] at this
      exact this.trans hc
    exact GammaExtra.le_thompsonJ hmax
  · exact absurd (O.card_lt_q4_of_not_le_S hA hsq hAS) (not_lt.2 hc)

theorem thompsonJ_M₀ : thompsonJ M₀ = thompsonJ S := by
  have hB := O.base
  apply le_antisymm
  · refine GammaExtra.thompsonJ_le fun A hA => ?_
    have hQ := hA.2.2 (blockU L ⊔ conjR (blockU L) t) (O.isMax_Q.1.trans hB.hSM) O.isMax_Q.2.1
    rw [O.card_Q] at hQ
    exact O.le_R_of_q4_le_card hA.1 (sq_of_isElemAbelian hA.2.1) hQ
  · refine GammaExtra.thompsonJ_le fun A hA => ?_
    have hQ := hA.2.2 (blockU L ⊔ conjR (blockU L) t) O.isMax_Q.1 O.isMax_Q.2.1
    rw [O.card_Q] at hQ
    have hmax : IsMaxElemAbelian M₀ A := by
      refine ⟨hA.1.trans hB.hSM, hA.2.1, fun B' hB'M hB'e => ?_⟩
      exact (O.card_le_q4 hB'M (sq_of_isElemAbelian hB'e)).trans hQ
    exact GammaExtra.le_thompsonJ hmax

end S2Ok

end CFSG.QuasithinUnique.Lin2
