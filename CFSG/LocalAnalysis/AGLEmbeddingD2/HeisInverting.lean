module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2

section Acts

variable {G : Type*} [Group G]

private def ActsAsPow (R Z : Subgroup G) (g : G) (a : ℤ) : Prop :=
  (∀ z ∈ Z, g * z * g⁻¹ ∈ Z) ∧ ∀ x ∈ R, ∃ z ∈ Z, g * x * g⁻¹ = x ^ a * z

private theorem ActsAsPow.one (R Z : Subgroup G) : ActsAsPow R Z 1 1 :=
  ⟨fun z hz => by simpa using hz, fun x _ => ⟨1, Z.one_mem, by simp⟩⟩

private theorem ActsAsPow.mul {R Z : Subgroup G} (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z)
    {g g' : G} {a b : ℤ} (hg : ActsAsPow R Z g a) (hg' : ActsAsPow R Z g' b) :
    ActsAsPow R Z (g * g') (a * b) := by
  refine ⟨fun z hz => ?_, fun x hx => ?_⟩
  · have := hg.1 _ (hg'.1 z hz)
    simpa [mul_assoc] using this
  · obtain ⟨z', hz', hx'⟩ := hg'.2 x hx
    obtain ⟨z, hz, hgx⟩ := hg.2 x hx
    refine ⟨z ^ b * (g * z' * g⁻¹), Z.mul_mem (Z.zpow_mem hz b) (hg.1 z' hz'), ?_⟩
    have hcomm : Commute (x ^ a) z := (hZc z hz (x ^ a) (R.zpow_mem hx a)).symm
    calc g * g' * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹ := by group
      _ = g * (x ^ b * z') * g⁻¹ := by rw [hx']
      _ = (g * x * g⁻¹) ^ b * (g * z' * g⁻¹) := by rw [conj_zpow]; group
      _ = (x ^ a * z) ^ b * (g * z' * g⁻¹) := by rw [hgx]
      _ = x ^ (a * b) * (z ^ b * (g * z' * g⁻¹)) := by
        rw [hcomm.mul_zpow, ← zpow_mul, mul_assoc]

private theorem ActsAsPow.pow {R Z : Subgroup G} (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z)
    {g : G} {a : ℤ} (hg : ActsAsPow R Z g a) (n : ℕ) : ActsAsPow R Z (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using ActsAsPow.one R Z
  | succ n ih => simpa [pow_succ] using ih.mul hZc hg

theorem exists_mul_of_pow_inverts_mod {R Z : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) {ι : G} (hιZ : ∀ z ∈ Z, ι * z * ι⁻¹ ∈ Z)
    (hι : ∀ x ∈ R, ∃ z ∈ Z, ι * x * ι⁻¹ = x⁻¹ * z) {j : ℕ} (hj : Odd j) {x : G} (hx : x ∈ R) :
    ∃ z ∈ Z, ι ^ j * x * (ι ^ j)⁻¹ = x⁻¹ * z := by
  have h1 : ActsAsPow R Z ι (-1) := ⟨hιZ, fun x hx => by simpa using hι x hx⟩
  obtain ⟨-, h2⟩ := h1.pow hZc j
  obtain ⟨z, hz, hz'⟩ := h2 x hx
  exact ⟨z, hz, by simpa [hj.neg_one_pow] using hz'⟩

private theorem zpow_eq_zpow_of_modEq {x : G} {n : ℕ} (hx : x ^ n = 1) {a b : ℤ}
    (hab : a ≡ b [ZMOD n]) : x ^ a = x ^ b := by
  have h1 : (orderOf x : ℤ) ∣ n := Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hx)
  rw [zpow_eq_zpow_iff_modEq]
  exact hab.of_dvd h1

theorem exists_mul_of_pow_scalar_inverts_mod {R Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hexp : ∀ r ∈ R, r ^ p = 1) (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) {g : G}
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) {lam : ℕ} (hlam : orderOf (lam : ZMod p) = p - 1)
    (hscal : ∀ x ∈ R, ∃ z ∈ Z, g * x * g⁻¹ = x ^ lam * z) {j : ℕ} (hj : Odd j) {x : G}
    (hx : x ∈ R) :
    ∃ z ∈ Z, g ^ (j * ((p - 1) / 2)) * x * (g ^ (j * ((p - 1) / 2)))⁻¹ = x⁻¹ * z := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2 : 2 * ((p - 1) / 2) = p - 1 := by
    have : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    omega
  have hlamE : (lam : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have hsq : (lam : ZMod p) ^ ((p - 1) / 2) * (lam : ZMod p) ^ ((p - 1) / 2) = 1 := by
      rw [← pow_add, ← two_mul, h2, ← hlam, pow_orderOf_eq_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have := Nat.le_of_dvd (by omega) (hlam ▸ orderOf_dvd_of_pow_eq_one h1)
      omega
    · exact h1
  have hact : ActsAsPow R Z g (lam : ℤ) := ⟨hgZ, fun x hx => by simpa using hscal x hx⟩
  obtain ⟨-, hact'⟩ := hact.pow hZc (j * ((p - 1) / 2))
  obtain ⟨z, hz, hzx⟩ := hact' x hx
  refine ⟨z, hz, ?_⟩
  have hmod : ((lam : ℤ) ^ (j * ((p - 1) / 2))) ≡ -1 [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [mul_comm, pow_mul, hlamE]
    exact hj.neg_one_pow
  rw [hzx, zpow_eq_zpow_of_modEq (hexp x hx) hmod, zpow_neg_one]

end Acts

end CFSG.AGLEmbeddingD2
