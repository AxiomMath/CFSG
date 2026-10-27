module

public import CFSG.ClassicalInvolution.Asc77.AscIHSL2
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem exists_mul_of_mem_closure {Y₀ : Subgroup G} {F S : Set G} (h1 : (1 : G) ∈ F)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hstep : ∀ f ∈ F, ∀ s ∈ S, ∃ y ∈ Y₀, ∃ f' ∈ F, f * s = y * f')
    {x : G} (hx : x ∈ Subgroup.closure S) : ∃ y ∈ Y₀, ∃ f ∈ F, x = y * f := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨1, Y₀.one_mem, 1, h1, by rw [one_mul]⟩
  | mul_right x _ s hs ih =>
    obtain ⟨y, hy, f, hf, rfl⟩ := ih
    obtain ⟨y', hy', f', hf', he⟩ := hstep f hf s hs
    exact ⟨y * y', Y₀.mul_mem hy hy', f', hf', by rw [mul_assoc, he, mul_assoc]⟩
  | mul_inv_cancel x _ s hs ih =>
    obtain ⟨y, hy, f, hf, rfl⟩ := ih
    obtain ⟨y', hy', f', hf', he⟩ := hstep f hf s⁻¹ (hS s hs)
    exact ⟨y * y', Y₀.mul_mem hy hy', f', hf', by rw [mul_assoc, he, mul_assoc]⟩

theorem mem_closure_pair_iff {z j : G} (hz : z * z = 1) (hj : j * j = 1) (hzj : z * j = j * z)
    {x : G} : x ∈ Subgroup.closure ({z, j} : Set G) ↔ x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  have e1 : ∀ y : G, z * (z * y) = y := fun y => by rw [← mul_assoc, hz, one_mul]
  have e3 : ∀ y : G, j * (z * y) = z * (j * y) := fun y => by
    rw [← mul_assoc, ← hzj, mul_assoc]
  have e4 : j * z = z * j := hzj.symm
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  let H : Subgroup G :=
    { carrier := {1, z, j, z * j}
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [mul_assoc, e1, e3, e4, hz, hj]
      one_mem' := by simp
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl) <;> simp [hzi, hji, e4] }
  constructor
  · intro hx
    have hle : Subgroup.closure ({z, j} : Set G) ≤ H := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem zpowers_zpow_eq_of_odd {v : G} {n : ℕ} (hv : orderOf v = 2 ^ n) {k : ℤ} (hk : Odd k) :
    Subgroup.zpowers (v ^ k) = Subgroup.zpowers v := by
  have h := (Subgroup.zpowers_eq_zpowers_iff' v k 1).mpr ?_
  · simpa using h
  · rw [hv]
    have hc : Nat.Coprime k.natAbs (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hk))
    simp only [Int.gcd, Int.natAbs_natCast, Int.natAbs_one, Nat.gcd_one_left]
    exact hc

theorem zpow_eq_self_of_odd {z : G} (hz : z * z = 1) {i : ℤ} (hi : Odd i) : z ^ i = z := by
  obtain ⟨m, rfl⟩ := hi
  rw [zpow_add, zpow_mul, zpow_ofNat, pow_two, hz, one_zpow, one_mul, zpow_one]

theorem zpow_eq_one_of_even {z : G} (hz : z * z = 1) {i : ℤ} (hi : Even i) : z ^ i = 1 := by
  obtain ⟨m, rfl⟩ := hi
  rw [← two_mul, zpow_mul, zpow_ofNat, pow_two, hz, one_zpow]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
