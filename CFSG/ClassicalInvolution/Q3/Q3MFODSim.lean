module

public import CFSG.ClassicalInvolution.Q3.Q3MFODFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

section Field

variable {F : Type} [Field F] [Finite F]

theorem cases_of_card_three (hF : Nat.card F = 3) (x : F) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h := FiniteField.pow_card x
  rw [hc] at h
  have h3 : x * (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

theorem two_ne_zero_of_card_three (hF : Nat.card F = 3) : (2 : F) ≠ 0 :=
  two_ne_zero_of_odd_card (by rw [hF]; decide)

theorem neg_one_ne_one_of_card_three (hF : Nat.card F = 3) : (-1 : F) ≠ 1 := fun h =>
  two_ne_zero_of_card_three hF (by linear_combination (-1 : F) * h)

theorem sq_ne_neg_one_of_card_three (hF : Nat.card F = 3) (x : F) : x ^ 2 ≠ -1 := by
  intro h
  rcases cases_of_card_three hF x with rfl | rfl | rfl
  · simp at h
  · exact neg_one_ne_one_of_card_three hF (by simpa using h.symm)
  · exact neg_one_ne_one_of_card_three hF (by simpa using h.symm)

theorem det_of_sq_neg_one (hF : Nat.card F = 3) {h : Matrix (Fin 2) (Fin 2) F}
    (hh : h * h = -1) : h.det = 1 := by
  have e00 := congrFun (congrFun hh 0) 0
  have e01 := congrFun (congrFun hh 0) 1
  have e10 := congrFun (congrFun hh 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  rw [Matrix.det_fin_two]
  by_cases hs : h 0 0 + h 1 1 = 0
  · have hs' : h 1 1 = -h 0 0 := by linear_combination hs
    rw [hs']
    linear_combination -e00
  · exfalso
    have hq : h 0 1 = 0 := by
      have : h 0 1 * (h 0 0 + h 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hr : h 1 0 = 0 := by
      have : h 1 0 * (h 0 0 + h 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    rw [hq, hr] at e00
    exact sq_ne_neg_one_of_card_three hF (h 0 0) (by linear_combination e00)

end Field

section Schur

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem exists_smul_of_commute_elementary (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ Module.finrank F V) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ h ∈ elementaryGroup Q, g * h = h * g) : ∃ c : F, ∀ x, g x = c • x := by
  have hE : ∀ h ∈ CFSG.ClassicalInvolution.Balance.StrongBalance.Orth.elemOn Q ⊤,
      g * h = h * g := fun h hh =>
    hcomm h (CFSG.ClassicalInvolution.Balance.StrongBalance.Orth.elemOn_le_elementaryGroup hh)
  have h3' : 3 ≤ Module.finrank F (⊤ : Submodule F V) := by rwa [finrank_top]
  obtain ⟨c, hc⟩ := exists_smul_of_commute_elemOn hodd (polarNondegOn_top hQ) h3' hg
    (fun x => by simp) hE
  exact ⟨c, fun x => hc x Submodule.mem_top⟩

end Schur

section Cases

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem sim_cases (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) (fr : Frame Q) {a : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0)
    (hsim : ∀ v, Q (a v) = μ * Q v) (hLa : ∀ A : SL(2, F), a * fr.La A = fr.La A * a)
    (hcomm : ∀ h ∈ elementaryGroup Q, a * a * h = h * (a * a)) :
    (μ = 1 ∧ a * a = 1) ∨ (μ = 1 ∧ ∀ v, a (a v) = -v) ∨ (μ = -1 ∧ a * a = 1) := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_three hF3
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hμ2 : μ * μ = 1 := by
    rcases cases_of_card_three hF3 μ with h | h | h
    · exact absurd h hμ
    · rw [h]; ring
    · rw [h]; ring
  have haO : a * a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [LinearEquiv.mul_apply, hsim, hsim, ← mul_assoc, hμ2, one_mul]
  obtain ⟨c, hc⟩ := exists_smul_of_commute_elementary hodd hQ h3 haO (fun h hh => hcomm h hh)
  have hc' : ∀ v, a (a v) = c • v := fun v => hc v
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 : a (a v) = 0 := by rw [hc', h0, zero_smul]
    exact a.injective (a.injective (by rw [h1, map_zero, map_zero]))
  obtain ⟨h, hh⟩ := exists_mul_of_commute_La h2 fr hLa
  have hdet : h.det = μ := by
    have := hsim (fr.incl 1)
    simp only [hh, one_mul, Frame.Q_incl, Matrix.det_one, mul_one] at this
    exact this
  have hhc : h * h = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e1 : a (a (fr.incl 1)) = fr.incl (1 * h * h) := by rw [hh 1, hh (1 * h)]
    have h1 : fr.incl (1 * h * h) = c • fr.incl (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [← e1, hc']
    have h2' := congrArg fr.coords h1
    rw [Frame.coords_incl, map_smul, Frame.coords_incl] at h2'
    simpa using h2'
  rcases cases_of_card_three hF3 μ with h0 | hμ1 | hμ1
  · exact absurd h0 hμ
  · rcases cases_of_card_three hF3 c with h0 | hc1 | hc1
    · exact absurd h0 hc0
    · left
      refine ⟨hμ1, LinearEquiv.ext fun v => ?_⟩
      rw [LinearEquiv.mul_apply, hc', hc1, one_smul]
      rfl
    · right
      left
      refine ⟨hμ1, fun v => ?_⟩
      rw [hc', hc1, neg_one_smul]
  · rcases cases_of_card_three hF3 c with h0 | hc1 | hc1
    · exact absurd h0 hc0
    · right
      right
      refine ⟨hμ1, LinearEquiv.ext fun v => ?_⟩
      rw [LinearEquiv.mul_apply, hc', hc1, one_smul]
      rfl
    · exfalso
      have hh2 : h * h = -1 := by rw [hhc, hc1, neg_smul, one_smul]
      have h1 := det_of_sq_neg_one hF3 hh2
      rw [hdet, hμ1] at h1
      exact neg_one_ne_one_of_card_three hF3 h1

end Cases

end CFSG.ClassicalInvolution.Q3.Q3MFOD
