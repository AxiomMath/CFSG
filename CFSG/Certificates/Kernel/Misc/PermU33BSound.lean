module

public import Certificates.Data.Kernel.Misc.PermU33B
public import CFSG.Certificates.Kernel.Misc.KGrpProof
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.Misc.U33B

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos
open CFSG.KC.Misc.KG (andB_iff orB_iff notB_iff impB_iff beq_true_iff exact_cnt_proved)

theorem hn28 : 28 ≤ 32 := by norm_num

theorem enc28 : ClosEnc (pcode (n := 28)) (mul 28) (one 28) := pcode_enc_proved hn28

theorem cubeOne_iff (g : Perm (Fin 28)) : cubeOne (pcode g) = true ↔ g ^ 3 = 1 := by
  rw [cubeOne, cube, beq_true_iff, ← enc28.enc_mul, ← enc28.enc_mul, ← enc28.enc_one]
  rw [pow_three]
  exact ⟨fun h => enc28.inj h, fun h => h ▸ rfl⟩

theorem beq_iff28 (a b : Perm (Fin 28)) : Nat.beq (pcode a) (pcode b) = true ↔ a = b := by
  rw [beq_true_iff]
  exact ⟨fun h => enc28.inj h, fun h => h ▸ rfl⟩

theorem one_eq28 : one 28 = pcode (1 : Perm (Fin 28)) := enc28.enc_one.symm

theorem cntN_eq (N : Nat) (f : Nat → Bool) : cntN N f = CFSG.KC.Misc.KG.cntN N f := rfl

theorem u33b_sound {H : Subgroup (Perm (Fin 28))} {N : ℕ} {E : ℕ → ℕ}
    (hE : ExactList pcode H N E)
    (hN : Nat.card H = N) {iz ix iy : ℕ} (hiz : iz < N) (hix : ix < N) (hiy : iy < N)
    (h1 : ∀ i < N, cubeMulAt E N i = true) (h3 : cntN N (fun k => cubeOne (E k)) = 27)
    (hz : zOK (E iz) (E ix) (E iy) = true) (hs : ∀ i < N, smallAt E N (E iz) i = true) :
    Nat.card H = N ∧
    (∀ x ∈ H, ∀ y ∈ H, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1) ∧
    Nat.card {g // g ∈ H ∧ g ^ 3 = 1} = 27 ∧
    ∃ z ∈ H, z ^ 3 = 1 ∧ z ≠ 1 ∧
      (∃ x ∈ H, ∃ y ∈ H, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z = x * y * x⁻¹ * y⁻¹) ∧
      ∀ a ∈ H, a ^ 3 = 1 → a ≠ 1 → a ≠ z → a⁻¹ ≠ z →
        Nat.card {x // x ∈ H ∧ ¬ x ^ 3 = 1 ∧ (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹)} ≤ 11 := by
  refine ⟨hN, ?_, ?_, ?_⟩
  · intro x hx y hy hx3 hy3
    obtain ⟨i, hi, hxi⟩ := hE.2.1 x hx
    obtain ⟨j, hj, hyj⟩ := hE.2.1 y hy
    have h := h1 i hi
    rw [cubeMulAt, letB_eq, impB_iff, ← hxi, cubeOne_iff] at h
    have h' := (allN_iff _ _).1 (h hx3) j hj
    rw [letB_eq, impB_iff, ← hyj, cubeOne_iff, ← enc28.enc_mul, cubeOne_iff] at h'
    exact h' hy3
  · rw [← h3, cntN_eq]
    exact (exact_cnt_proved hn28 hE (fun c => cubeOne c) _ fun g _ => cubeOne_iff g).symm
  · obtain ⟨gz, hgz, hz'⟩ := hE.1 iz hiz
    obtain ⟨gx, hgx, hx'⟩ := hE.1 ix hix
    obtain ⟨gy, hgy, hy'⟩ := hE.1 iy hiy
    have hzk := hz
    rw [zOK, ← hz', ← hx', ← hy'] at hzk
    simp only [andB_iff, notB_iff, cubeOne_iff] at hzk
    obtain ⟨hz3, hz1, hx3, hy3, hzc⟩ := hzk
    rw [one_eq28, beq_iff28] at hz1
    rw [pcode_inv_proved hn28, pcode_inv_proved hn28, ← enc28.enc_mul, ← enc28.enc_mul,
      ← enc28.enc_mul, beq_iff28] at hzc
    refine ⟨gz, hgz, hz3, hz1, ⟨gx, hgx, gy, hgy, hx3, hy3, hzc⟩, ?_⟩
    intro a ha ha3 ha1 haz hai
    obtain ⟨i, hi, hai'⟩ := hE.2.1 a ha
    have h := hs i hi
    rw [smallAt, letB_eq, letB_eq, ← hai', ← hz', pcode_inv_proved hn28] at h
    simp only [impB_iff, notB_iff, cubeOne_iff, one_eq28, beq_iff28] at h
    have hc := h ha3 ha1 haz hai
    have hle := Nat.le_of_ble_eq_true hc
    have e : cntN N (fun k => letB (E k) fun g => andB (notB (cubeOne g))
        (letB (mul 28 (mul 28 g (pcode a)) (inv 28 g)) fun c =>
          orB (Nat.beq c (pcode a)) (Nat.beq c (pcode a⁻¹)))) =
        Nat.card {x // x ∈ H ∧ ¬ x ^ 3 = 1 ∧ (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹)} := by
      rw [cntN_eq]
      simp only [letB_eq]
      refine exact_cnt_proved hn28 hE (fun c => andB (notB (cubeOne c))
        (orB (Nat.beq (mul 28 (mul 28 c (pcode a)) (inv 28 c)) (pcode a))
          (Nat.beq (mul 28 (mul 28 c (pcode a)) (inv 28 c)) (pcode a⁻¹)))) _ fun g _ => ?_
      rw [andB_iff, notB_iff, cubeOne_iff, orB_iff, pcode_inv_proved hn28, ← enc28.enc_mul,
        ← enc28.enc_mul, beq_iff28, beq_iff28]
    rw [← e]
    exact hle

end CFSG.KC.Misc.U33B

end
