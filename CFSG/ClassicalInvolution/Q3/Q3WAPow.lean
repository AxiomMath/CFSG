module

public import CFSG.ClassicalInvolution.Q3.Q3WL65

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

@[expose] def Pow3 {A : Type*} [Group A] (R : Subgroup A) : Prop := ∀ l ∈ R, l ^ 3 ∈ ⁅R, R⁆

theorem Pow3.map {A B : Type*} [Group A] [Group B] (φ : A →* B) {R : Subgroup A} (h : Pow3 R) :
    Pow3 (R.map φ) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [← map_pow, ← Subgroup.map_commutator]
  exact ⟨_, h l hl, rfl⟩

theorem Pow3.conjSub {A : Type*} [Group A] (g : A) {R : Subgroup A} (h : Pow3 R) :
    Pow3 (CFSG.ClassicalInvolution.Generic.conjSub g R) :=
  h.map _

theorem pow3_range_sl2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {X : Type*}
    [Group X] (χ : SL(2, K) →* X) : Pow3 χ.range := by
  rw [MonoidHom.range_eq_map]
  refine Pow3.map χ ?_
  intro l hl
  exact pow_three_mem_commutator_of_equiv hK (Subgroup.topEquiv (G := SL(2, K))) l hl

theorem pow3_of_stdPair {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {X : Type}
    [Group X] {W U V : Subgroup X} (h : LinearBlockStandardPair K W U V) : Pow3 U ∧ Pow3 V := by
  obtain ⟨θ, c, -, -, hcases⟩ := h
  have h12 : Pow3 (B12 K) := pow3_range_sl2 hK _
  have h23 : Pow3 (B23 K) := pow3_range_sl2 hK _
  have h1 : Pow3 (((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ) := (h12.map _).map _
  have h2 : Pow3 (((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ) := (h23.map _).map _
  rcases hcases with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · rw [← hU, ← hV]
    exact ⟨h1, h2⟩
  · rw [← hU, ← hV]
    exact ⟨h2, h1⟩

theorem le_of_map_le_of_pow3 {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hker : φ.ker ≤ Subgroup.center A) (hcop : ∀ z ∈ φ.ker, ¬ 3 ∣ orderOf z)
    {R R' : Subgroup A} (hR' : Pow3 R') (h : R'.map φ ≤ R.map φ) : R' ≤ R := by
  have hsplit : ∀ a ∈ R', ∃ r ∈ R, r⁻¹ * a ∈ φ.ker := by
    intro a ha
    obtain ⟨r, hr, e⟩ := h ⟨a, ha, rfl⟩
    exact ⟨r, hr, by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]⟩
  have hcomm : ⁅R', R'⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨r₁, hr₁, hz₁⟩ := hsplit a ha
    obtain ⟨r₂, hr₂, hz₂⟩ := hsplit b hb
    have e : ⁅a, b⁆ = ⁅r₁, r₂⁆ := by
      have h1 := commutatorElement_mul_central_left (hker hz₁) r₁ b
      rw [mul_inv_cancel_left] at h1
      have h3 := commutatorElement_mul_central_right (hker hz₂) r₁ r₂
      rw [mul_inv_cancel_left] at h3
      exact h1.trans h3
    rw [e, commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
  intro a ha
  obtain ⟨r, hr, hz⟩ := hsplit a ha
  have ha3 : a ^ 3 ∈ R := hcomm (hR' a ha)
  have hzc : r⁻¹ * a ∈ Subgroup.center A := hker hz
  have haz : a = r * (r⁻¹ * a) := (mul_inv_cancel_left r a).symm
  have hz3 : (r⁻¹ * a) ^ 3 ∈ R := by
    have h1 : a ^ 3 = r ^ 3 * (r⁻¹ * a) ^ 3 := by
      conv_lhs => rw [haz]
      exact Commute.mul_pow (Subgroup.mem_center_iff.mp hzc r) 3
    have h2 : (r⁻¹ * a) ^ 3 = (r ^ 3)⁻¹ * a ^ 3 := by
      rw [h1, inv_mul_cancel_left]
    rw [h2]
    exact R.mul_mem (R.inv_mem (R.pow_mem hr 3)) ha3
  have hzR : r⁻¹ * a ∈ R := by
    set z := r⁻¹ * a with hzdef
    have hcopr : Nat.Coprime 3 (orderOf z) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hcop z hz)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopr
    rw [← hm]
    exact R.pow_mem hz3 m
  have hmem := R.mul_mem hr hzR
  rwa [mul_inv_cancel_left] at hmem

theorem eq_of_map_eq_of_pow3 {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hker : φ.ker ≤ Subgroup.center A) (hcop : ∀ z ∈ φ.ker, ¬ 3 ∣ orderOf z)
    {R R' : Subgroup A} (hR : Pow3 R) (hR' : Pow3 R') (h : R.map φ = R'.map φ) : R = R' :=
  le_antisymm (le_of_map_le_of_pow3 φ hker hcop hR h.le)
    (le_of_map_le_of_pow3 φ hker hcop hR' h.ge)

end CFSG.ClassicalInvolution.Q3.Q3W
