module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterTwist
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

structure UnitaryOuterModel (F : Type*) [Group F] (R : Subgroup F) (q : ℕ) : Prop where
  four_le : 4 ≤ q
  card_root : Nat.card R = q ^ 3
  sq_sq : ∀ x ∈ R, (x ^ 2) ^ 2 = 1
  comm_of_sq : ∀ x ∈ R, x ^ 2 = 1 → ∀ y ∈ R, x * y = y * x
  card_sq_one : Nat.card {x : F // x ∈ R ∧ x ^ 2 = 1} = q
  card_sq : ∀ u ∈ R, u ≠ 1 → u ^ 2 = 1 → Nat.card {x : F // x ∈ R ∧ x ^ 2 = u} = q * (q + 1)
  conj_inj : ∀ x ∈ R, MulAut.conj x = 1 → x = 1
  fix : ∀ γ : MulAut F, R.map γ.toMonoidHom = R → γ ^ 2 ∈ R.map MulAut.conj →
    ∀ u ∈ R, u ^ 2 = 1 → γ u = u
  aut_sq : ∀ γ : MulAut F, R.map γ.toMonoidHom = R → (∀ u ∈ R, u ^ 2 = 1 → γ u = u) →
    ∀ u ∈ R, u ^ 2 = 1 → γ ^ 2 = MulAut.conj u → γ ∈ R.map MulAut.conj ∨ γ ^ 2 = 1
  exists_sq_eq_one : ∀ γ : MulAut F, R.map γ.toMonoidHom = R → γ ^ 2 ∈ R.map MulAut.conj →
    ∃ y ∈ R, (MulAut.conj y⁻¹ * γ) ^ 2 = 1
  mul_inv_mem : ∀ Y : Subgroup (MulAut F), IsPGroup 2 Y → ∀ γ₁ ∈ Y, ∀ γ₂ ∈ Y,
    R.map γ₁.toMonoidHom = R → R.map γ₂.toMonoidHom = R → γ₁ ^ 2 ∈ R.map MulAut.conj →
      γ₂ ^ 2 ∈ R.map MulAut.conj → γ₁ ∉ R.map MulAut.conj → γ₂ ∉ R.map MulAut.conj →
        γ₁ * γ₂⁻¹ ∈ R.map MulAut.conj
  card_twist : ∀ γ : MulAut F, R.map γ.toMonoidHom = R → γ ∉ R.map MulAut.conj → γ ^ 2 = 1 →
    Nat.card {x : F // x ∈ R ∧ x * γ x = 1} = q ^ 2

theorem eq_of_card_le_two {Z : Type*} [Finite Z] (h : Nat.card Z ≤ 2) {o a b : Z} (ha : a ≠ o)
    (hb : b ≠ o) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h3 : ({o, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair hab]
  have h4 := Finset.card_le_univ ({o, a, b} : Finset Z)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem two_pow_dvd_two_of_dvd_two_mul_odd {k m : ℕ} (hm : Odd m) (h : 2 ^ k ∣ 2 * m) :
    2 ^ k ≤ 2 := by
  rcases k with _ | _ | k
  · simp
  · simp
  · exfalso
    obtain ⟨c, hc⟩ := h
    have h4 : 4 ∣ 2 * m := ⟨2 ^ k * c, by rw [hc]; ring⟩
    obtain ⟨j, rfl⟩ := hm
    omega

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
