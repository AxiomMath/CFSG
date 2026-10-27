module

public import CFSG.FeitThompson.OddOrder.ComparisonWordFixedVector
import CFSG.FeitThompson.Local.CoprimeSplittingFiniteAbelian

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

section Displacement

variable {A : Type*} [CommGroup A]

private def toAddEnd (τ : MulAut A) : AddMonoid.End (Additive A) :=
  MonoidHom.toAdditive (τ : A →* A)

private theorem toAddEnd_apply (τ : MulAut A) (v : A) :
    toAddEnd τ (Additive.ofMul v) = Additive.ofMul (τ v) := (rfl)

private theorem toAddEnd_pow_apply (τ : MulAut A) (n : ℕ) (v : A) :
    (toAddEnd τ ^ n) (Additive.ofMul v) = Additive.ofMul ((τ ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (toAddEnd τ ^ (n + 1)) (Additive.ofMul v)
          = toAddEnd τ ((toAddEnd τ ^ n) (Additive.ofMul v)) := by rw [pow_succ']; rfl
      rw [h, ih, toAddEnd_apply, pow_succ', MulAut.mul_apply]

private theorem toAddEnd_pow_eq_one {τ : MulAut A} {p : ℕ} (hτ : τ ^ p = 1) :
    toAddEnd τ ^ p = 1 := by
  ext a
  rw [show a = Additive.ofMul (Additive.toMul a) from rfl, toAddEnd_pow_apply, hτ]
  rfl

private def mulDisplacement (τ : MulAut A) : Subgroup A :=
  Subgroup.toAddSubgroup.symm (toAddEnd τ - 1).range

private theorem mem_mulDisplacement_iff {τ : MulAut A} {v : A} :
    v ∈ mulDisplacement τ ↔ Additive.ofMul v ∈ (toAddEnd τ - 1).range := Iff.rfl

private theorem apply_mem_mulDisplacement {τ : MulAut A} {v : A}
    (hv : v ∈ mulDisplacement τ) : τ v ∈ mulDisplacement τ := by
  rw [mem_mulDisplacement_iff, ← toAddEnd_apply]
  exact apply_mem_range_sub_one (Commute.refl _) (mem_mulDisplacement_iff.1 hv)

private theorem mul_inv_apply_mem_mulDisplacement (τ : MulAut A) (u : A) :
    u * (τ u)⁻¹ ∈ mulDisplacement τ := by
  rw [mem_mulDisplacement_iff]
  refine ⟨-Additive.ofMul u, ?_⟩
  change toAddEnd τ (-Additive.ofMul u) - (-Additive.ofMul u) = _
  rw [map_neg, toAddEnd_apply, ofMul_mul, ofMul_inv]
  abel

private theorem mul_inv_pow_mem_mulDisplacement (τ : MulAut A) (u : A) (n : ℕ) :
    u * ((τ ^ n) u)⁻¹ ∈ mulDisplacement τ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : (τ ^ (n + 1)) u = τ ((τ ^ n) u) := by rw [pow_succ', MulAut.mul_apply]
      have key : u * ((τ ^ (n + 1)) u)⁻¹ = (u * (τ u)⁻¹) * τ (u * ((τ ^ n) u)⁻¹) := by
        rw [h, map_mul, map_inv]; group
      rw [key]
      exact mul_mem (mul_inv_apply_mem_mulDisplacement τ u) (apply_mem_mulDisplacement ih)

private theorem mul_inv_zpow_mem_mulDisplacement (τ : MulAut A) (u : A) (k : ℤ) :
    u * ((τ ^ k) u)⁻¹ ∈ mulDisplacement τ := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast]; exact mul_inv_pow_mem_mulDisplacement τ u n
  · set w := (τ ^ (-(n : ℤ))) u with hw
    have hwu : (τ ^ n) w = u := by
      rw [hw, ← MulAut.mul_apply, ← zpow_natCast τ n, ← zpow_add]; simp
    have h1 := mul_inv_pow_mem_mulDisplacement τ w n
    rw [hwu] at h1
    have h2 : u * w⁻¹ = (w * u⁻¹)⁻¹ := by group
    rw [h2]; exact inv_mem h1

private theorem eq_one_of_mem_mulDisplacement_of_apply_eq {p : ℕ}
    (hp : p.Coprime (Nat.card A)) {τ : MulAut A} (hτ : τ ^ p = 1)
    {v : A} (hv : v ∈ mulDisplacement τ) (hfix : τ v = v) : v = 1 := by
  have hcard : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
  have hp' : p.Coprime (Nat.card (Additive A)) := by rw [hcard]; exact hp
  have hker : Additive.ofMul v ∈ (toAddEnd τ - 1 : AddMonoid.End (Additive A)).ker :=
    mem_ker_sub_one_iff.2 (by rw [toAddEnd_apply, hfix])
  have hmem : Additive.ofMul v ∈ (toAddEnd τ - 1 : AddMonoid.End (Additive A)).ker
      ⊓ (toAddEnd τ - 1 : AddMonoid.End (Additive A)).range :=
    ⟨hker, mem_mulDisplacement_iff.1 hv⟩
  rw [inf_ker_range_sub_one_eq_bot hp' (toAddEnd_pow_eq_one hτ), AddSubgroup.mem_bot] at hmem
  exact Additive.ofMul.injective hmem

end Displacement

variable {G : Type*} [Group G]

theorem eq_one_of_mem_commutator_zpowers_of_conj_eq {Q : Subgroup G} [IsMulCommutative ↥Q]
    {p : ℕ} (hcop : p.Coprime (Nat.card Q)) {s : G} (hsp : s ^ p = 1)
    (hs : s ∈ normalizer (Q : Set G)) {x : G} (hx : x ∈ ⁅Q, zpowers s⁆)
    (hfix : s * x * s⁻¹ = x) : x = 1 := by
  let _ : CommGroup ↥Q := IsMulCommutative.instCommGroup
  set τ : MulAut ↥Q := Q.normalizerMonoidHom ⟨s, hs⟩ with hτdef
  have hcoe : ∀ (k : ℤ) (v : ↥Q), (((τ ^ k) v : ↥Q) : G) = s ^ k * (v : G) * (s ^ k)⁻¹ := by
    intro k v
    rw [hτdef, ← map_zpow, Q.normalizerMonoidHom_apply_apply_coe]
    norm_cast
  have hcoe1 : ∀ v : ↥Q, ((τ v : ↥Q) : G) = s * (v : G) * s⁻¹ := fun v => by
    have h := hcoe 1 v; simpa using h
  have hτp : τ ^ p = 1 := by
    rw [hτdef, ← map_pow]
    convert map_one Q.normalizerMonoidHom
    exact Subtype.ext (by push_cast; exact hsp)
  have hle : ⁅Q, zpowers s⁆ ≤ (mulDisplacement τ).map Q.subtype := by
    refine Subgroup.commutator_le.2 fun u hu g hg => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨(⟨u, hu⟩ : ↥Q) * ((τ ^ k) ⟨u, hu⟩)⁻¹,
      mul_inv_zpow_mem_mulDisplacement τ ⟨u, hu⟩ k, ?_⟩
    change ((⟨u, hu⟩ : ↥Q) : G) * (((τ ^ k) ⟨u, hu⟩ : ↥Q) : G)⁻¹ = _
    rw [hcoe]
    group
  obtain ⟨v, hv, rfl⟩ := hle hx
  have hfix' : τ v = v := Subtype.ext (by rw [hcoe1 v]; simpa using hfix)
  have hv1 : v = 1 := eq_one_of_mem_mulDisplacement_of_apply_eq hcop hτp hv hfix'
  rw [hv1]
  rfl

theorem mul_inv_eq_inv_mul_of_comparisonWord_eq_one (s y r₁ r₃ : G)
    (h : comparisonWord s y r₁ r₃ = 1) :
    r₁ * ((y⁻¹ * s * y) * (y⁻¹ * r₁ * y))⁻¹
      = ((y⁻¹ * r₃ * y) * (y⁻¹ * s * y))⁻¹ * r₃ := by
  rw [← mul_inv_eq_one]
  have key : r₁ * ((y⁻¹ * s * y) * (y⁻¹ * r₁ * y))⁻¹
      * (((y⁻¹ * r₃ * y) * (y⁻¹ * s * y))⁻¹ * r₃)⁻¹
      = (r₁ * y⁻¹ * r₁⁻¹ * s⁻¹ * y) * comparisonWord s y r₁ r₃
        * (r₁ * y⁻¹ * r₁⁻¹ * s⁻¹ * y)⁻¹ := by
    rw [comparisonWord_def]; group
  rw [key, h, mul_one, mul_inv_cancel]

section Setup

variable {p q : ℕ} {F : Type*} [Field F] [Finite F]

theorem AppendixCSetup.s_pow_eq_one (S : AppendixCSetup p q F G) : S.s ^ p = 1 := by
  have := S.charP_field
  rw [AppendixCSetup.s_def, ← map_pow, ← ofAdd_nsmul]
  have h : (p : ℕ) • (1 : F) = 0 := by
    rw [nsmul_eq_mul, mul_one]
    exact (CharP.cast_eq_zero_iff F p p).mpr dvd_rfl
  rw [h]
  exact map_one S.pt

theorem comparisonWord_eq_one (S : AppendixCSetup p q F G)
    {Q : Subgroup G} [IsMulCommutative ↥Q] (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hyQ : y ∈ Q)
    (hP₁ : Subgroup.map (MulAut.conj y⁻¹) S.P₀ ≤ normalizer (S.U : Set G))
    (hycomm : y ∈ ⁅Q, S.P₀⁆) {r₁ r₂ r₃ : G} (hr₁ : r₁ ∈ S.P₀) (hr₂ : r₂ ∈ S.P₀)
    (hr₃ : r₃ ∈ S.P₀)
    (hword : (y⁻¹ * S.s * y) * r₂⁻¹ * (y⁻¹ * S.s * y) = r₃ * (y⁻¹ * S.s * y) ^ 2 * r₁)
    (hprod : r₁ * r₂ * r₃ = 1) :
    comparisonWord S.s y r₁ r₃ = 1 := by
  obtain ⟨hmem, hfix⟩ := comparisonWord_mem_commutator_and_conj_eq_self S hQp hQnorm hyQ hP₁
    hycomm hr₁ hr₂ hr₃ hword hprod
  rw [S.P₀_eq_zpowers] at hmem
  exact eq_one_of_mem_commutator_zpowers_of_conj_eq hQp.symm S.s_pow_eq_one
    (hQnorm S.s_mem_P₀) hmem hfix

theorem mul_inv_eq_inv_mul_of_word_relation (S : AppendixCSetup p q F G)
    {Q : Subgroup G} [IsMulCommutative ↥Q] (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hyQ : y ∈ Q)
    (hP₁ : Subgroup.map (MulAut.conj y⁻¹) S.P₀ ≤ normalizer (S.U : Set G))
    (hycomm : y ∈ ⁅Q, S.P₀⁆) {r₁ r₂ r₃ t t₁ t₃ : G} (hr₁ : r₁ ∈ S.P₀) (hr₂ : r₂ ∈ S.P₀)
    (hr₃ : r₃ ∈ S.P₀) (ht : t = y⁻¹ * S.s * y) (ht₁ : t₁ = y⁻¹ * r₁ * y)
    (ht₃ : t₃ = y⁻¹ * r₃ * y)
    (hword : t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁) (hprod : r₁ * r₂ * r₃ = 1) :
    r₁ * (t * t₁)⁻¹ = (t₃ * t)⁻¹ * r₃ := by
  subst ht ht₁ ht₃
  exact mul_inv_eq_inv_mul_of_comparisonWord_eq_one _ _ _ _
    (comparisonWord_eq_one S hQp hQnorm hyQ hP₁ hycomm hr₁ hr₂ hr₃ hword hprod)

end Setup

end

end CFSG.FeitThompson
