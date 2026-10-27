module

public import CFSG.ClassicalGroups.Unitary.Action
public import CFSG.Fischer.Classification.Unitary.Basic

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

noncomputable def wd : WittData frob where
  u := 1
  ω := ω
  hu := by rw [map_one, one_mul, neg_K]
  hω := frob_mul_self omega_ne_zero
  hω1 := omega_ne_one

variable {n : ℕ}

noncomputable abbrev v₀ (n : ℕ) : Fin (n + 2) → K := wd.hypA n

noncomputable abbrev u₀ (n : ℕ) : Fin (n + 2) → K := wd.hypB n

@[expose] noncomputable def ι (n : ℕ) : (Fin n → K) →ₗ[K] (Fin (n + 2) → K) :=
  (consL (n + 1)).comp (consL n)

@[expose] noncomputable def π (n : ℕ) : (Fin (n + 2) → K) →ₗ[K] (Fin n → K) :=
  LinearMap.funLeft K K fun i : Fin n => i.succ.succ

theorem π_apply (x : Fin (n + 2) → K) (i : Fin n) : π n x i = x i.succ.succ := rfl

@[simp] theorem ι_apply_zero (z : Fin n → K) : ι n z 0 = 0 := rfl

@[simp] theorem ι_apply_one (z : Fin n → K) : ι n z 1 = 0 := rfl

@[simp] theorem ι_apply_succ_succ (z : Fin n → K) (i : Fin n) : ι n z i.succ.succ = z i := rfl

@[simp] theorem π_ι (z : Fin n → K) : π n (ι n z) = z := rfl

theorem ι_injective : Function.Injective (ι n) := fun z z' h => by
  rw [← π_ι z, h, π_ι]

@[simp] theorem π_v₀ : π n (v₀ n) = 0 := funext fun i => wd.hypA_succ_succ i

@[simp] theorem π_u₀ : π n (u₀ n) = 0 := funext fun i => wd.hypB_succ_succ i

theorem herm_ι_ι (z z' : Fin n → K) : herm frob (ι n z) (ι n z') = herm frob z z' := by
  rw [ι, LinearMap.comp_apply, LinearMap.comp_apply, herm_consL, herm_consL]

theorem herm_v₀_v₀ : herm frob (v₀ n) (v₀ n) = 0 := wd.herm_hypA_hypA

theorem herm_u₀_u₀ : herm frob (u₀ n) (u₀ n) = 0 := wd.herm_hypB_hypB

theorem herm_v₀_u₀ : herm frob (v₀ n) (u₀ n) = 1 := wd.herm_hypA_hypB

theorem herm_u₀_v₀ : herm frob (u₀ n) (v₀ n) = 1 := wd.herm_hypB_hypA frob_frob

theorem herm_v₀_ι (z : Fin n → K) : herm frob (v₀ n) (ι n z) = 0 := by
  rw [wd.herm_hypA_left, ι_apply_zero, ι_apply_one, mul_zero, add_zero]

theorem herm_u₀_ι (z : Fin n → K) : herm frob (u₀ n) (ι n z) = 0 := by
  rw [wd.herm_hypB_left, ι_apply_zero, ι_apply_one, mul_zero, add_zero, mul_zero]

theorem herm_ι_v₀ (z : Fin n → K) : herm frob (ι n z) (v₀ n) = 0 :=
  herm_eq_zero_comm frob frob_frob (herm_v₀_ι z)

theorem herm_ι_u₀ (z : Fin n → K) : herm frob (ι n z) (u₀ n) = 0 :=
  herm_eq_zero_comm frob frob_frob (herm_u₀_ι z)

theorem v₀_ne_zero : v₀ n ≠ 0 := wd.hypA_ne_zero

theorem u₀_ne_zero : u₀ n ≠ 0 := by
  intro h
  have := herm_v₀_u₀ (n := n)
  rw [h, herm_zero_right] at this
  exact zero_ne_one this

theorem eq_ι_π {y : Fin (n + 2) → K} (h0 : y 0 = 0) (h1 : y 1 = 0) : y = ι n (π n y) := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ j =>
    cases j using Fin.cases with
    | zero => exact h1
    | succ k => rfl

theorem decomp (x : Fin (n + 2) → K) :
    x = herm frob (u₀ n) x • v₀ n + herm frob (v₀ n) x • u₀ n + ι n (π n x) := by
  set y := x - herm frob (u₀ n) x • v₀ n - herm frob (v₀ n) x • u₀ n with hy
  obtain ⟨h1, h2⟩ := herm_proj_pair isUnitaryInvolution_frob herm_v₀_v₀ herm_u₀_u₀ herm_v₀_u₀ x
  rw [← hy] at h1 h2
  obtain ⟨y0, y1⟩ := wd.coord_eq_zero_of_perp h1 h2
  have hπ : π n y = π n x := by
    simp only [hy, map_sub, map_smul, π_v₀, π_u₀, smul_zero, sub_zero]
  rw [← hπ, ← eq_ι_π y0 y1, hy]
  abel

theorem herm_ι_left (z : Fin n → K) (x : Fin (n + 2) → K) :
    herm frob (ι n z) x = herm frob z (π n x) := by
  conv_lhs => rw [decomp x]
  rw [herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, herm_ι_v₀, herm_ι_u₀,
    herm_ι_ι, mul_zero, mul_zero, zero_add, zero_add]

theorem herm_ι_right (x : Fin (n + 2) → K) (z : Fin n → K) :
    herm frob x (ι n z) = herm frob (π n x) z := by
  rw [herm_conj frob frob_frob, herm_ι_left, ← herm_conj frob frob_frob]

theorem herm_eq_coords (x y : Fin (n + 2) → K) :
    herm frob x y = frob (herm frob (u₀ n) x) * herm frob (v₀ n) y +
      frob (herm frob (v₀ n) x) * herm frob (u₀ n) y + herm frob (π n x) (π n y) := by
  conv_lhs => rw [decomp x]
  rw [herm_add_left, herm_add_left, herm_smul_left, herm_smul_left, herm_ι_left]

theorem decomp_of_perp {x : Fin (n + 2) → K} (hx : herm frob (v₀ n) x = 0) :
    x = herm frob (u₀ n) x • v₀ n + ι n (π n x) := by
  conv_lhs => rw [decomp x]
  rw [hx, zero_smul, add_zero]

theorem exists_smul_eq_hyp (hn : 1 ≤ n) {a b : Fin (n + 2) → K} (ha0 : a ≠ 0)
    (ha : herm frob a a = 0) (hb : herm frob b b = 0) (hab : herm frob a b = 1) :
    ∃ g : SUid frob (n + 2), g • a = v₀ n ∧ g • b = u₀ n := by
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob (by omega) ha0 ha
    v₀_ne_zero herm_v₀_v₀
  have h1 : herm frob (v₀ n) (t • b) = 1 := by rw [← ht, herm_smul_smul, hab]
  obtain ⟨g, hg1, hg2⟩ := exists_fix_smul_eq isUnitaryInvolution_frob herm_v₀_v₀
    (by rw [herm_smul_smul, hb] : herm frob (t • b) (t • b) = 0) herm_u₀_u₀
    (by rw [h1]; exact one_ne_zero) (by rw [herm_v₀_u₀]; exact one_ne_zero)
  refine ⟨g * t, by rw [mul_smul, ht, hg1], ?_⟩
  rw [mul_smul, hg2, h1, herm_v₀_u₀, div_one, one_smul]

end CFSG.Fischer.Classification.Unitary
