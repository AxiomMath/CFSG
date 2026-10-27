module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Heis

open Subgroup

variable {G : Type*} [Group G]

structure Rel (e f d : G) : Prop where
  he : e ^ 5 = 1
  hf : f ^ 5 = 1
  hd : d ^ 5 = 1
  hde : d * e = e * d
  hdf : d * f = f * d
  hfe : f * e = d * (e * f)

variable {e f d : G}

theorem Rel.comm (h : Rel e f d) (n a b : ℕ) : d ^ n * (e ^ a * f ^ b) = (e ^ a * f ^ b) * d ^ n :=
  ((Commute.pow_pow (show Commute d e from h.hde) n a).mul_right
    (Commute.pow_pow (show Commute d f from h.hdf) n b)).eq

theorem Rel.fpow_e (h : Rel e f d) (j : ℕ) : f ^ j * e = d ^ j * (e * f ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hfd : Commute (f ^ j) d := (Commute.pow_left (show Commute f d from h.hdf.symm) j)
    calc f ^ (j + 1) * e = f ^ j * (f * e) := by rw [pow_succ, mul_assoc]
      _ = f ^ j * (d * (e * f)) := by rw [h.hfe]
      _ = d * (f ^ j * (e * f)) := hfd.left_comm _
      _ = d * ((f ^ j * e) * f) := by rw [mul_assoc]
      _ = d * ((d ^ j * (e * f ^ j)) * f) := by rw [ih]
      _ = d ^ (j + 1) * (e * f ^ (j + 1)) := by
          rw [pow_succ' d j, pow_succ f j]; simp only [mul_assoc]

theorem Rel.fpow_epow (h : Rel e f d) (i j : ℕ) :
    f ^ j * e ^ i = d ^ (i * j) * (e ^ i * f ^ j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hed : Commute (e ^ i) (d ^ j) :=
      (Commute.pow_pow (show Commute e d from h.hde.symm) i j)
    calc f ^ j * e ^ (i + 1) = (f ^ j * e ^ i) * e := by rw [pow_succ, mul_assoc]
      _ = (d ^ (i * j) * (e ^ i * f ^ j)) * e := by rw [ih]
      _ = d ^ (i * j) * (e ^ i * (f ^ j * e)) := by simp only [mul_assoc]
      _ = d ^ (i * j) * (e ^ i * (d ^ j * (e * f ^ j))) := by rw [h.fpow_e]
      _ = d ^ (i * j) * (d ^ j * (e ^ i * (e * f ^ j))) := by rw [hed.left_comm]
      _ = d ^ ((i + 1) * j) * (e ^ (i + 1) * f ^ j) := by
          rw [← mul_assoc, ← pow_add, pow_succ e i, mul_assoc (e ^ i)]
          congr 2
          ring

theorem Rel.nf_mul (h : Rel e f d) (i j k i' j' k' : ℕ) :
    (e ^ i * f ^ j * d ^ k) * (e ^ i' * f ^ j' * d ^ k') =
      e ^ (i + i') * f ^ (j + j') * d ^ (k + k' + i' * j) := by
  have hc := h.comm k i' j'
  have hc2 := h.comm (i' * j) (i + i') (j + j')
  have hed : Commute (e ^ i) (d ^ (i' * j)) :=
    (Commute.pow_pow (show Commute e d from h.hde.symm) i (i' * j))
  calc (e ^ i * f ^ j * d ^ k) * (e ^ i' * f ^ j' * d ^ k')
      = e ^ i * f ^ j * (d ^ k * (e ^ i' * f ^ j')) * d ^ k' := by simp only [mul_assoc]
    _ = e ^ i * f ^ j * ((e ^ i' * f ^ j') * d ^ k) * d ^ k' := by rw [hc]
    _ = e ^ i * (f ^ j * e ^ i') * f ^ j' * (d ^ k * d ^ k') := by simp only [mul_assoc]
    _ = e ^ i * (d ^ (i' * j) * (e ^ i' * f ^ j)) * f ^ j' * (d ^ k * d ^ k') := by
        rw [h.fpow_epow i' j]
    _ = d ^ (i' * j) * (e ^ (i + i') * f ^ (j + j')) * d ^ (k + k') := by
        rw [pow_add, pow_add, pow_add]
        simp only [mul_assoc]
        rw [hed.left_comm]
    _ = e ^ (i + i') * f ^ (j + j') * d ^ (i' * j) * d ^ (k + k') := by rw [hc2]
    _ = e ^ (i + i') * f ^ (j + j') * d ^ (k + k' + i' * j) := by
        rw [mul_assoc _ (d ^ (i' * j)), ← pow_add]; congr 2; ring

theorem Rel.nf_pow (h : Rel e f d) (i j k n : ℕ) :
    (e ^ i * f ^ j * d ^ k) ^ n =
      e ^ (n * i) * f ^ (n * j) * d ^ (n * k + i * j * n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, h.nf_mul]
    have h2 : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have a1 : n * i + i = (n + 1) * i := by ring
    have a2 : n * j + j = (n + 1) * j := by ring
    have a3 : n * k + i * j * n.choose 2 + k + i * (n * j) =
        (n + 1) * k + i * j * (n + 1).choose 2 := by rw [h2]; ring
    rw [a1, a2, a3]

theorem Rel.nf_pow_five (h : Rel e f d) (i j k : ℕ) : (e ^ i * f ^ j * d ^ k) ^ 5 = 1 := by
  rw [h.nf_pow]
  have h10 : Nat.choose 5 2 = 10 := by decide
  rw [h10]
  have e1 : e ^ (5 * i) = 1 := by rw [pow_mul, h.he, one_pow]
  have e2 : f ^ (5 * j) = 1 := by rw [pow_mul, h.hf, one_pow]
  have e3 : d ^ (5 * k + i * j * 10) = 1 := by
    rw [show 5 * k + i * j * 10 = 5 * (k + 2 * i * j) by ring, pow_mul, h.hd, one_pow]
  rw [e1, e2, e3]; simp

def Rel.nfSubgroup (h : Rel e f d) : Subgroup G where
  carrier := {x | ∃ i j k : ℕ, x = e ^ i * f ^ j * d ^ k}
  one_mem' := ⟨0, 0, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨i + i', j + j', k + k' + i' * j, h.nf_mul i j k i' j' k'⟩
  inv_mem' := by
    rintro x ⟨i, j, k, rfl⟩
    refine ⟨4 * i, 4 * j, 4 * k + i * j * Nat.choose 4 2, ?_⟩
    rw [← h.nf_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h.nf_pow_five i j k)

theorem Rel.closure_le (h : Rel e f d) : closure ({e, f} : Set G) ≤ h.nfSubgroup := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨1, 0, 0, by simp⟩
  · exact ⟨0, 1, 0, by simp⟩

theorem Rel.pow_five (h : Rel e f d) {z : G} (hz : z ∈ closure ({e, f} : Set G)) : z ^ 5 = 1 := by
  obtain ⟨i, j, k, rfl⟩ := h.closure_le hz
  exact h.nf_pow_five i j k

theorem Rel.isPGroup_closure (h : Rel e f d) : IsPGroup 5 ↥(closure ({e, f} : Set G)) := by
  rintro ⟨z, hz⟩
  exact ⟨1, Subtype.ext (by simpa using h.pow_five hz)⟩

theorem conj_closure {x : G} (hd : d ∈ closure ({e, f} : Set G)) (hx1 : x * e * x⁻¹ = f)
    (hx2 : x * f * x⁻¹ = e ^ 4 * f ^ 4 * d ^ 3) {z : G} (hz : z ∈ closure ({e, f} : Set G)) :
    x * z * x⁻¹ ∈ closure ({e, f} : Set G) := by
  have he : e ∈ closure ({e, f} : Set G) := subset_closure (by simp)
  have hf : f ∈ closure ({e, f} : Set G) := subset_closure (by simp)
  have hmem : ∀ y ∈ ({e, f} : Set G), x * y * x⁻¹ ∈ closure ({e, f} : Set G) := by
    intro y hy
    rcases hy with rfl | hy
    · rw [hx1]; exact hf
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, hx2]
      exact mul_mem (mul_mem (pow_mem he 4) (pow_mem hf 4)) (pow_mem hd 3)
  induction hz using Subgroup.closure_induction with
  | mem y hy => exact hmem y hy
  | one => simp
  | mul y z _ _ hy hz =>
    have : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
    rw [this]; exact mul_mem hy hz
  | inv y _ hy =>
    have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hy

theorem obstruction_abs {a u : G} (h : Rel e f d) (hu21 : u ^ 21 = 1) (hu7 : u ^ 7 ≠ 1)
    (hu3 : u ^ 3 ≠ 1) (hau : a * u = u * a) (hd : d = f * e * f⁻¹ * e⁻¹)
    (hxe : u ^ 7 * e * (u ^ 7)⁻¹ = f) (hxf : u ^ 7 * f * (u ^ 7)⁻¹ = e ^ 4 * f ^ 4 * d ^ 3)
    (hfe : f ≠ e) :
    ∃ x s : G, orderOf x = 3 ∧ orderOf s = 7 ∧ a * x = x * a ∧ a * s = s * a ∧ x * s = s * x ∧
      ∃ E : Subgroup G, IsPGroup 5 ↥E ∧ (∀ z ∈ E, x * z * x⁻¹ ∈ E) ∧
        ∃ z ∈ E, x * z * x⁻¹ ≠ z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx3 : (u ^ 7) ^ 3 = 1 := by rw [← pow_mul]; exact hu21
  have hs7 : (u ^ 3) ^ 7 = 1 := by rw [← pow_mul]; exact hu21
  have he : e ∈ closure ({e, f} : Set G) := subset_closure (by simp)
  have hf : f ∈ closure ({e, f} : Set G) := subset_closure (by simp)
  have hdmem : d ∈ closure ({e, f} : Set G) := by
    rw [hd]
    exact mul_mem (mul_mem (mul_mem hf he) (inv_mem hf)) (inv_mem he)
  have hax : a * u ^ 7 = u ^ 7 * a := (Commute.pow_right (show Commute a u from hau) 7).eq
  have has : a * u ^ 3 = u ^ 3 * a := (Commute.pow_right (show Commute a u from hau) 3).eq
  have hxs : u ^ 7 * u ^ 3 = u ^ 3 * u ^ 7 := by rw [← pow_add, ← pow_add, add_comm]
  refine ⟨u ^ 7, u ^ 3, orderOf_eq_prime hx3 hu7, orderOf_eq_prime hs7 hu3, hax, has, hxs,
    closure ({e, f} : Set G), h.isPGroup_closure,
    fun z hz => conj_closure hdmem hxe hxf hz, e, he, ?_⟩
  rw [hxe]
  exact hfe

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Heis
