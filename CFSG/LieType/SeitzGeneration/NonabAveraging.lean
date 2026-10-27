module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Abel

public section

namespace CFSG.LieType.SeitzGeneration

open Finset

section Ring

variable {R : Type*} [Ring R] {p : ℕ}

theorem mul_geom_sum_pow_eq_self {x : R} (hx : x ^ p = 1) :
    x * ∑ i ∈ range p, x ^ i = ∑ i ∈ range p, x ^ i := by
  have h := mul_geom_sum x p
  rw [hx, sub_self, sub_mul, one_mul] at h
  exact sub_eq_zero.mp h

theorem sum_zmod_val_eq_sum_range [NeZero p] (f : ℕ → R) :
    ∑ c : ZMod p, f c.val = ∑ b ∈ range p, f b := by
  refine Finset.sum_nbij ZMod.val (fun c _ => Finset.mem_range.2 (ZMod.val_lt c))
    (fun a _ b _ h => ZMod.val_injective p h) (fun b hb => ?_) (fun _ _ => rfl)
  exact ⟨(b : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.1 hb)⟩

theorem sum_pow_val_mul_eq [Fact p.Prime] {y : R} (hy : y ^ p = 1) {i : ℕ} (hi0 : 0 < i)
    (hip : i < p) : ∑ j : ZMod p, y ^ (j.val * i) = ∑ b ∈ range p, y ^ b := by
  have hi : (i : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff i p).1 h
    exact absurd (Nat.le_of_dvd hi0 this) (by omega)
  have h1 : ∀ j : ZMod p, y ^ (j.val * i) = y ^ ((j * (i : ZMod p)).val) := by
    intro j
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hip, ← pow_eq_pow_mod _ hy]
  simp_rw [h1]
  rw [← sum_zmod_val_eq_sum_range (fun b => y ^ b)]
  exact Fintype.sum_equiv (Equiv.mulRight₀ (i : ZMod p) hi) _ _ (fun j => rfl)

theorem sum_lines_eq [Fact p.Prime] {A B : R} (hAB : Commute A B) (hB : B ^ p = 1) :
    ∑ j : ZMod p, ∑ i ∈ range p, (A * B ^ j.val) ^ i + ∑ i ∈ range p, B ^ i =
      (∑ i ∈ range p, A ^ i) * (∑ b ∈ range p, B ^ b) + (p : R) := by
  have h1 : ∀ (j : ZMod p) (i : ℕ), (A * B ^ j.val) ^ i = A ^ i * B ^ (j.val * i) := fun j i => by
    rw [(hAB.pow_right j.val).mul_pow, ← pow_mul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h0 : ∑ j : ZMod p, B ^ (j.val * 0) = (p : R) := by
    simp [ZMod.card]
  have hrest : ∀ i ∈ (range p).erase 0, A ^ i * ∑ j : ZMod p, B ^ (j.val * i) =
      A ^ i * ∑ b ∈ range p, B ^ b := fun i hi => by
    rw [sum_pow_val_mul_eq hB (Nat.pos_of_ne_zero (Finset.mem_erase.1 hi).1)
      (Finset.mem_range.1 (Finset.mem_erase.1 hi).2)]
  have hp0 : 0 ∈ range p := Finset.mem_range.2 (Fact.out : p.Prime).pos
  rw [← Finset.add_sum_erase _ _ hp0, h0, Finset.sum_congr rfl hrest, ← Finset.sum_mul]
  have hA0 : ∑ i ∈ (range p).erase 0, A ^ i = ∑ i ∈ range p, A ^ i - 1 := by
    rw [eq_sub_iff_add_eq, add_comm, ← pow_zero A, Finset.add_sum_erase _ _ hp0]
  rw [hA0, pow_zero, one_mul, sub_mul, one_mul]
  abel

end Ring

section Module

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {p : ℕ}

theorem pow_apply_mem {S : Submodule F M} {A : Module.End F M} (hA : ∀ x ∈ S, A x ∈ S) (n : ℕ)
    {x : M} (hx : x ∈ S) : (A ^ n) x ∈ S := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hA _ ih

theorem geom_sum_apply_mem {S : Submodule F M} {A : Module.End F M} (hA : ∀ x ∈ S, A x ∈ S)
    (n : ℕ) {x : M} (hx : x ∈ S) : (∑ i ∈ range n, A ^ i) x ∈ S := by
  rw [LinearMap.sum_apply]
  exact S.sum_mem fun i _ => pow_apply_mem hA i hx

theorem exists_decomp_lines [Fact p.Prime] (hpF : (p : F) ≠ 0) {A B : Module.End F M}
    (hAB : Commute A B) (hA : A ^ p = 1) (hB : B ^ p = 1) (m : M) :
    ∃ (u : ZMod p → M) (v : M), (∀ j : ZMod p, (A * B ^ j.val) (u j) = u j) ∧ B v = v ∧
      m = ∑ j, u j + v ∧ ∀ S : Submodule F M, (∀ x ∈ S, A x ∈ S) → (∀ x ∈ S, B x ∈ S) →
        m ∈ S → (∀ j, u j ∈ S) ∧ v ∈ S := by
  set NA : Module.End F M := ∑ i ∈ range p, A ^ i with hNA
  set NB : Module.End F M := ∑ i ∈ range p, B ^ i with hNB
  have hg : ∀ j : ZMod p, (A * B ^ j.val) ^ p = 1 := fun j => by
    rw [(hAB.pow_right j.val).mul_pow, hA, one_mul, ← pow_mul, mul_comm, pow_mul, hB, one_pow]
  refine ⟨fun j => (p : F)⁻¹ • ((∑ i ∈ range p, (A * B ^ j.val) ^ i) m),
    (p : F)⁻¹ • (NB m) - (p : F)⁻¹ • ((NA * NB) m), ?_, ?_, ?_, ?_⟩
  · intro j
    rw [map_smul, ← Module.End.mul_apply, mul_geom_sum_pow_eq_self (hg j)]
  · have h1 : B * NB = NB := mul_geom_sum_pow_eq_self hB
    have h2 : B * (NA * NB) = NA * NB := by
      have hc : Commute B NA := Commute.sum_right _ _ _ fun i _ => (hAB.symm.pow_right i)
      rw [← mul_assoc, hc.eq, mul_assoc, h1]
    rw [map_sub, map_smul, map_smul, ← Module.End.mul_apply, h1, ← Module.End.mul_apply, h2]
  · have hid := sum_lines_eq (p := p) hAB hB
    rw [← hNA, ← hNB] at hid
    have hm := congrArg (fun T : Module.End F M => T m) hid
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.natCast_apply] at hm
    have key : (∑ x : ZMod p, ∑ d ∈ range p, ((A * B ^ x.val) ^ d) m) + (NB m - (NA * NB) m) =
        (p : F) • m := by
      rw [Nat.cast_smul_eq_nsmul]
      calc _ = (∑ x : ZMod p, ∑ d ∈ range p, ((A * B ^ x.val) ^ d) m + NB m) - (NA * NB) m := by
            abel
        _ = ((NA * NB) m + p • m) - (NA * NB) m := by rw [hm]
        _ = p • m := by abel
    simp only [LinearMap.sum_apply]
    rw [← Finset.smul_sum, ← smul_sub, ← smul_add, key, inv_smul_smul₀ hpF]
  · intro S hAS hBS hm
    refine ⟨fun j => S.smul_mem _ (geom_sum_apply_mem (fun x hx => ?_) p hm), ?_⟩
    · rw [Module.End.mul_apply]
      exact hAS _ (pow_apply_mem hBS _ hx)
    · have h1 : NB m ∈ S := geom_sum_apply_mem hBS p hm
      have h2 : (NA * NB) m ∈ S := by
        rw [Module.End.mul_apply]
        exact geom_sum_apply_mem hAS p h1
      exact S.sub_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

end Module

end CFSG.LieType.SeitzGeneration
