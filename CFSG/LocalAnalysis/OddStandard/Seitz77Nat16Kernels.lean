module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Basic
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Polynomial

@[expose] noncomputable def g5 : (ZMod 2)[X] := X ^ 2 + X + 1

@[expose] noncomputable def g7 : (ZMod 2)[X] := X ^ 4 + X ^ 3 + 1

theorem g5_mul : g5 * (g1 * g7) = X ^ 10 + X ^ 5 + 1 := by
  unfold g5 g1 g7
  ring_nf
  reduce_mod_char

theorem coprime_g1_g7 : IsCoprime g1 g7 :=
  ⟨X ^ 3 + X + 1, X ^ 3 + X ^ 2, by
    unfold g1 g7
    ring_nf
    reduce_mod_char⟩

theorem coprime_g5_g1 : IsCoprime g5 g1 :=
  ⟨X ^ 2 + X, 1, by
    unfold g5 g1
    ring_nf
    reduce_mod_char⟩

theorem coprime_g5_g7 : IsCoprime g5 g7 :=
  ⟨X ^ 3 + X ^ 2 + X, X + 1, by
    unfold g5 g7
    ring_nf
    reduce_mod_char⟩

section Kernels

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

variable (H : Module.End (ZMod 2) V)

theorem aeval_g1_eq : aeval H g1 = H ^ 4 + H + 1 := by simp [g1]

theorem aeval_g5_eq : aeval H g5 = H ^ 2 + H + 1 := by simp [g5]

theorem aeval_g7_eq : aeval H g7 = H ^ 4 + H ^ 3 + 1 := by simp [g7]

theorem pow_ten (hH15 : H ^ 15 = 1) (hfpf : ∀ v, (H ^ 5) v = v → v = 0) :
    H ^ 10 + H ^ 5 + 1 = 0 := by
  refine LinearMap.ext fun v => ?_
  have h1 : (H ^ 5) ((H ^ 10) v) = v := by
    rw [← Module.End.mul_apply, ← pow_add, hH15]; rfl
  have h2 : (H ^ 5) ((H ^ 5) v) = (H ^ 10) v := by
    rw [← Module.End.mul_apply, ← pow_add]
  have h : (H ^ 5) ((H ^ 10 + H ^ 5 + 1 : Module.End (ZMod 2) V) v) =
      (H ^ 10 + H ^ 5 + 1 : Module.End (ZMod 2) V) v := by
    simp only [LinearMap.add_apply, map_add, Module.End.one_apply]
    rw [h1, h2]
    abel
  simpa using hfpf _ h

theorem ker_sup_eq_top (h10 : H ^ 10 + H ^ 5 + 1 = 0) :
    LinearMap.ker (aeval H g5) ⊔ (LinearMap.ker (aeval H g1) ⊔ LinearMap.ker (aeval H g7)) = ⊤ := by
  rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime H coprime_g1_g7,
    Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime H
      (IsCoprime.mul_right coprime_g5_g1 coprime_g5_g7), g5_mul]
  rw [eq_top_iff]
  intro v _
  rw [LinearMap.mem_ker]
  simp [h10]

theorem disjoint_ker_g1_g7 :
    Disjoint (LinearMap.ker (aeval H g1)) (LinearMap.ker (aeval H g7)) :=
  Polynomial.disjoint_ker_aeval_of_isCoprime H coprime_g1_g7

theorem disjoint_ker_g5 :
    Disjoint (LinearMap.ker (aeval H g5))
      (LinearMap.ker (aeval H g1) ⊔ LinearMap.ker (aeval H g7)) := by
  rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime H coprime_g1_g7]
  exact Polynomial.disjoint_ker_aeval_of_isCoprime H
    (IsCoprime.mul_right coprime_g5_g1 coprime_g5_g7)



section Weyl

variable (R : Module.End (ZMod 2) V)

theorem hHR_of (hR2 : R * R = 1) (hRH : R * H = H ^ 14 * R) : H * R = R * H ^ 14 := by
  calc H * R = (R * R) * H * R := by rw [hR2, one_mul]
    _ = R * (R * H) * R := by simp only [mul_assoc]
    _ = R * (H ^ 14 * R) * R := by rw [hRH]
    _ = R * H ^ 14 * (R * R) := by simp only [mul_assoc]
    _ = R * H ^ 14 := by rw [hR2, mul_one]

theorem pow_mul_R (hHR : H * R = R * H ^ 14) (n : ℕ) : H ^ n * R = R * (H ^ 14) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc H ^ (n + 1) * R = H * (H ^ n * R) := by rw [pow_succ', mul_assoc]
      _ = H * (R * (H ^ 14) ^ n) := by rw [ih]
      _ = (H * R) * (H ^ 14) ^ n := by rw [mul_assoc]
      _ = R * H ^ 14 * (H ^ 14) ^ n := by rw [hHR]
      _ = R * (H ^ 14) ^ (n + 1) := by rw [pow_succ' (H ^ 14) n, mul_assoc]

theorem poly7_comm (hH15 : H ^ 15 = 1) :
    (H ^ 14) ^ 4 + (H ^ 14) ^ 3 + 1 = H ^ 11 * (H ^ 4 + H + 1) := by
  have e1 : (H ^ 14) ^ 4 = H ^ 11 := by
    rw [← pow_mul, show 14 * 4 = 15 * 3 + 11 from rfl, pow_add, pow_mul, hH15, one_pow, one_mul]
  have e2 : (H ^ 14) ^ 3 = H ^ 11 * H := by
    rw [← pow_mul, show 14 * 3 = 15 * 2 + 12 from rfl, pow_add, pow_mul, hH15, one_pow,
      one_mul, ← pow_succ]
  have e3 : H ^ 11 * H ^ 4 = 1 := by rw [← pow_add]; exact hH15
  rw [e1, e2, mul_add, mul_add, e3, mul_one]
  abel

theorem poly1_comm (hH15 : H ^ 15 = 1) :
    (H ^ 14) ^ 4 + H ^ 14 + 1 = H ^ 11 * (H ^ 4 + H ^ 3 + 1) := by
  have e1 : (H ^ 14) ^ 4 = H ^ 11 := by
    rw [← pow_mul, show 14 * 4 = 15 * 3 + 11 from rfl, pow_add, pow_mul, hH15, one_pow, one_mul]
  have e3 : H ^ 11 * H ^ 4 = 1 := by rw [← pow_add]; exact hH15
  have e4 : H ^ 11 * H ^ 3 = H ^ 14 := by rw [← pow_add]
  rw [e1, mul_add, mul_add, e3, e4, mul_one]
  abel

theorem R_mem_ker_g7 (hH15 : H ^ 15 = 1) (hR2 : R * R = 1) (hRH : R * H = H ^ 14 * R) {v : V}
    (hv : v ∈ LinearMap.ker (aeval H g1)) : R v ∈ LinearMap.ker (aeval H g7) := by
  have hHR := hHR_of H R hR2 hRH
  rw [LinearMap.mem_ker, aeval_g7_eq]
  rw [LinearMap.mem_ker, aeval_g1_eq] at hv
  have h1 : (H ^ 4 + H ^ 3 + 1 : Module.End (ZMod 2) V) * R =
      R * (H ^ 11 * (H ^ 4 + H + 1)) := by
    rw [← poly7_comm H hH15, mul_add, mul_add, mul_one, add_mul, add_mul, one_mul,
      pow_mul_R H R hHR 4, pow_mul_R H R hHR 3]
  calc (H ^ 4 + H ^ 3 + 1 : Module.End (ZMod 2) V) (R v) =
      ((H ^ 4 + H ^ 3 + 1 : Module.End (ZMod 2) V) * R) v := rfl
    _ = (R * (H ^ 11 * (H ^ 4 + H + 1)) : Module.End (ZMod 2) V) v := by rw [h1]
    _ = 0 := by
      rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero, map_zero]

theorem R_mem_ker_g1 (hH15 : H ^ 15 = 1) (hR2 : R * R = 1) (hRH : R * H = H ^ 14 * R) {v : V}
    (hv : v ∈ LinearMap.ker (aeval H g7)) : R v ∈ LinearMap.ker (aeval H g1) := by
  have hHR := hHR_of H R hR2 hRH
  rw [LinearMap.mem_ker, aeval_g1_eq]
  rw [LinearMap.mem_ker, aeval_g7_eq] at hv
  have h1 : (H ^ 4 + H + 1 : Module.End (ZMod 2) V) * R =
      R * (H ^ 11 * (H ^ 4 + H ^ 3 + 1)) := by
    rw [← poly1_comm H hH15, mul_add, mul_add, mul_one, add_mul, add_mul, one_mul,
      pow_mul_R H R hHR 4, hHR]
  calc (H ^ 4 + H + 1 : Module.End (ZMod 2) V) (R v) =
      ((H ^ 4 + H + 1 : Module.End (ZMod 2) V) * R) v := rfl
    _ = (R * (H ^ 11 * (H ^ 4 + H ^ 3 + 1)) : Module.End (ZMod 2) V) v := by rw [h1]
    _ = 0 := by
      rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero, map_zero]

section Dim

variable [Module.Finite (ZMod 2) V]

theorem finrank_K1_eq_K7 (hH15 : H ^ 15 = 1) (hR2 : R * R = 1) (hRH : R * H = H ^ 14 * R) :
    Module.finrank (ZMod 2) (LinearMap.ker (aeval H g1)) =
      Module.finrank (ZMod 2) (LinearMap.ker (aeval H g7)) := by
  have hR2' : R ∘ₗ R = LinearMap.id := by rw [← Module.End.mul_eq_comp, hR2]; rfl
  let Re : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap R R hR2' hR2'
  have hRe : (Re : V →ₗ[ZMod 2] V) = R := rfl
  have h1 : (LinearMap.ker (aeval H g1)).map R ≤ LinearMap.ker (aeval H g7) := by
    rintro _ ⟨v, hv, rfl⟩
    exact R_mem_ker_g7 H R hH15 hR2 hRH hv
  have h2 : (LinearMap.ker (aeval H g7)).map R ≤ LinearMap.ker (aeval H g1) := by
    rintro _ ⟨v, hv, rfl⟩
    exact R_mem_ker_g1 H R hH15 hR2 hRH hv
  have e1 := LinearEquiv.finrank_map_eq Re (LinearMap.ker (aeval H g1))
  have e2 := LinearEquiv.finrank_map_eq Re (LinearMap.ker (aeval H g7))
  rw [hRe] at e1 e2
  exact le_antisymm (e1 ▸ Submodule.finrank_mono h1) (e2 ▸ Submodule.finrank_mono h2)

theorem finrank_sum (hV : Module.finrank (ZMod 2) V = 8) (h10 : H ^ 10 + H ^ 5 + 1 = 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (aeval H g5)) +
      (Module.finrank (ZMod 2) (LinearMap.ker (aeval H g1)) +
        Module.finrank (ZMod 2) (LinearMap.ker (aeval H g7))) = 8 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval H g1))
    (LinearMap.ker (aeval H g7))
  rw [(disjoint_ker_g1_g7 H).eq_bot, finrank_bot] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval H g5))
    (LinearMap.ker (aeval H g1) ⊔ LinearMap.ker (aeval H g7))
  rw [(disjoint_ker_g5 H).eq_bot, finrank_bot, ker_sup_eq_top H h10, finrank_top, hV] at h2
  omega

end Dim

end Weyl

end Kernels


end Nat16

end CFSG.OddStandard.Seitz77
