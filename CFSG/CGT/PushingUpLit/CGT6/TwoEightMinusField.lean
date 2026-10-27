module

public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Field

variable (n : ℕ)

@[expose] noncomputable def sigR : Fq (2 * n) →+* Fq (2 * n) where
  toFun := frobHalf n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero n two_ne_zero)
  map_add' x y := add_pow_char_pow x y 2 n

theorem sigR_apply (x : Fq (2 * n)) : sigR n x = x ^ 2 ^ n := rfl

theorem sigR_sigR [NeZero n] (x : Fq (2 * n)) : sigR n (sigR n x) = x := by
  have : Fintype (Fq (2 * n)) := Fintype.ofFinite _
  have hc : Fintype.card (Fq (2 * n)) = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n) (by have := NeZero.ne n; omega)]
  rw [sigR_apply, sigR_apply, ← pow_mul, ← pow_add, ← two_mul, ← hc]
  exact FiniteField.pow_card x

@[expose] noncomputable def Fz : Subfield (Fq (2 * n)) :=
  RingHom.eqLocusField (sigR n) (RingHom.id _)

theorem mem_Fz (x : Fq (2 * n)) : x ∈ Fz n ↔ sigR n x = x := Iff.rfl

theorem sigR_Fz (c : Fz n) : sigR n (c : Fq (2 * n)) = c := c.2

theorem Fz_smul (c : Fz n) (x : Fq (2 * n)) : c • x = (c : Fq (2 * n)) * x := rfl

theorem zpow_apply_of_fixed {F : Type*} [Field F] (g : F ≃+* F) {a : F} (hg : g a = a) (k : ℤ) :
    (g ^ k) a = a := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, RingAut.mul_apply, hg, ih]
  | pred k ih =>
    rw [zpow_sub_one, RingAut.mul_apply]
    have : g⁻¹ a = a := (RingEquiv.symm_apply_eq g).mpr hg.symm
    rw [this, ih]

theorem card_Fz [NeZero n] : Nat.card (Fz n) = 2 ^ n := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hF : Nat.card (Fq (2 * n)) = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  obtain ⟨σ, hσ, hord, -, -, h⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := Fq (2 * n)) Nat.prime_two (by omega) hF
  have hpow : ∀ (k : ℕ) (a : Fq (2 * n)), (σ ^ k) a = a ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, RingAut.mul_apply, hσ, map_pow, ih, ← pow_mul, ← pow_succ]
  have hgord : orderOf (σ ^ n) = 2 := by
    rw [orderOf_pow_of_dvd hn0 (by rw [hord]; exact Dvd.intro_left 2 rfl), hord]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn0)
  have hcardA : Nat.card (Subgroup.zpowers (σ ^ n)) = 2 := by rw [Nat.card_zpowers, hgord]
  obtain ⟨-, S, hS, hSc⟩ := h (Subgroup.zpowers (σ ^ n))
  rw [hcardA] at hSc
  have hS2 : S = Fz n := by
    ext a
    have h1 : a ∈ S ↔ ∀ τ ∈ Subgroup.zpowers (σ ^ n), τ a = a := by
      rw [← SetLike.mem_coe, hS]
      rfl
    rw [h1, mem_Fz, sigR_apply]
    constructor
    · intro hτ
      have := hτ (σ ^ n) (Subgroup.mem_zpowers _)
      rwa [hpow] at this
    · intro ha τ hτ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      exact zpow_apply_of_fixed (σ ^ n) (by rw [hpow]; exact ha) k
  rw [← hS2, hSc, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]

theorem three_le_card_Fz [NeZero n] (hn : 2 ≤ n) : 3 ≤ Nat.card (Fz n) := by
  rw [card_Fz]
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem exists_sigR_ne [NeZero n] : ∃ w : Fq (2 * n), sigR n w ≠ w := by
  have hn0 : n ≠ 0 := NeZero.ne n
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card (Fz n) = Nat.card (Fq (2 * n)) :=
    Nat.card_congr (Equiv.ofBijective (fun c : Fz n => (c : Fq (2 * n)))
      ⟨Subtype.val_injective, fun w => ⟨⟨w, hcon w⟩, rfl⟩⟩)
  rw [card_Fz, GaloisField.card 2 (2 * n) (by omega)] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega

end Field

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
