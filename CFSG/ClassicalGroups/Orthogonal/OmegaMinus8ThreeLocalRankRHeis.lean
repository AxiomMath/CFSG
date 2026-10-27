module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalHeisenberg
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankR

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.Open (pRank)

variable {K : Type} [Field K] {b c : K}

theorem rotLE_apply (p : K × K) : rotLE K p = (-p.2, p.1 - p.2) :=
  rfl

theorem rotPow_one : rotPow K 1 = rotLE K := by
  show rotLE K ^ (1 : ZMod 3).val = rotLE K
  have : (1 : ZMod 3).val = 1 := by decide
  rw [this, pow_one]

theorem cmEquiv_one_one_one_pow_apply (k : ℕ) (x : ModelSpace K) :
    (cmEquiv K ![1, 1, 1] ^ k) x = (fun i => (rotLE K ^ k) (x.1 i), x.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, cmEquiv_apply]
    refine Prod.ext (funext fun i => ?_) rfl
    have h1 : (![1, 1, 1] : Fin 3 → ZMod 3) i = 1 := by fin_cases i <;> rfl
    simp only [h1, rotPow_one, pow_succ', LinearEquiv.mul_apply]

theorem cmEquiv_one_one_one_pow_planeVec (k : ℕ) (i : Fin 3) (p : K × K) :
    (cmEquiv K ![1, 1, 1] ^ k) (planeVec i p) = planeVec i ((rotLE K ^ k) p) := by
  rw [cmEquiv_one_one_one_pow_apply]
  refine Prod.ext (funext fun j => ?_) rfl
  by_cases h : j = i
  · subst h
    simp [planeVec]
  · simp [planeVec, Pi.single_apply, h]

theorem cmEquiv_one_one_one_pow_three : cmEquiv K ![1, 1, 1] ^ 3 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [cmEquiv_one_one_one_pow_apply, rotLE_pow_three]
  rfl

theorem polar_rotForm_apply (p p' : K × K) :
    polar (rotForm K) p p' = 2 * p.1 * p'.1 - p.1 * p'.2 - p'.1 * p.2 + 2 * p.2 * p'.2 := by
  simp only [QuadraticMap.polar, rotForm_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem polar_rotForm_rotLE_pow (i j : Fin 3) (p : K × K) :
    polar (rotForm K) ((rotLE K ^ (i : ℕ)) p) ((rotLE K ^ (j : ℕ)) p) =
      (if i = j then 2 else -1) * rotForm K p := by
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, polar_rotForm_apply, rotForm_apply, rotLE_apply] <;> ring

theorem polar_modelForm_planeVec_self (b c : K) (i : Fin 3) (p p' : K × K) :
    polar (modelForm b c) (planeVec i p) (planeVec i p') = polar (rotForm K) p p' := by
  have h : planeVec i p + planeVec i p' = planeVec i (p + p') := by
    simp [planeVec, Pi.single_add]
  simp only [QuadraticMap.polar, h, modelForm_planeVec]

@[expose] def heisE (K : Type) [Field K] (a : K × K) : ModelSpace K :=
  planeVec 0 (1, 0) + planeVec 1 a

@[expose] def heisD (K : Type) [Field K] : ModelSpace K :=
  planeVec 2 (1, 0)

theorem modelForm_heisD (b c : K) : modelForm b c (heisD K) = 1 := by
  rw [heisD, modelForm_planeVec, rotForm_apply]
  simp

theorem heisE_orbit (a : K × K) (k : ℕ) :
    (cmEquiv K ![1, 1, 1] ^ k) (heisE K a) =
      planeVec 0 ((rotLE K ^ k) (1, 0)) + planeVec 1 ((rotLE K ^ k) a) := by
  rw [heisE, map_add, cmEquiv_one_one_one_pow_planeVec, cmEquiv_one_one_one_pow_planeVec]

theorem heisD_orbit (k : ℕ) :
    (cmEquiv K ![1, 1, 1] ^ k) (heisD K) = planeVec 2 ((rotLE K ^ k) (1, 0)) := by
  rw [heisD, cmEquiv_one_one_one_pow_planeVec]

theorem polar_heis_orbit_ee (b c : K) {a : K × K} (ha : rotForm K a = -1) (i j : Fin 3) :
    polar (modelForm b c) ((cmEquiv K ![1, 1, 1] ^ (i : ℕ)) (heisE K a))
      ((cmEquiv K ![1, 1, 1] ^ (j : ℕ)) (heisE K a)) = 0 := by
  rw [heisE_orbit, heisE_orbit, polar_add_left, polar_add_right, polar_add_right,
    polar_modelForm_planeVec_self, polar_modelForm_planeVec_self,
    polar_modelForm_planeVec_planeVec_of_ne b c (by decide : (0 : Fin 3) ≠ 1),
    polar_modelForm_planeVec_planeVec_of_ne b c (by decide : (1 : Fin 3) ≠ 0),
    polar_rotForm_rotLE_pow, polar_rotForm_rotLE_pow, ha]
  have h1 : rotForm K ((1 : K), (0 : K)) = 1 := by rw [rotForm_apply]; simp
  rw [h1]
  ring

theorem polar_heis_orbit_ed (b c : K) (a : K × K) (i j : Fin 3) :
    polar (modelForm b c) ((cmEquiv K ![1, 1, 1] ^ (i : ℕ)) (heisE K a))
      ((cmEquiv K ![1, 1, 1] ^ (j : ℕ)) (heisD K)) = 0 := by
  rw [heisE_orbit, heisD_orbit, polar_add_left,
    polar_modelForm_planeVec_planeVec_of_ne b c (by decide : (0 : Fin 3) ≠ 2),
    polar_modelForm_planeVec_planeVec_of_ne b c (by decide : (1 : Fin 3) ≠ 2), add_zero]

theorem polar_heis_orbit_dd (b c : K) (i j : Fin 3) :
    polar (modelForm b c) ((cmEquiv K ![1, 1, 1] ^ (i : ℕ)) (heisD K))
      ((cmEquiv K ![1, 1, 1] ^ (j : ℕ)) (heisD K)) =
      (if i = j then 2 else -1) * modelForm b c (heisD K) := by
  rw [heisD_orbit, heisD_orbit, polar_modelForm_planeVec_self, polar_rotForm_rotLE_pow,
    modelForm_heisD, rotForm_apply]
  simp

theorem heisE_sum (a : K × K) :
    heisE K a + cmEquiv K ![1, 1, 1] (heisE K a) + (cmEquiv K ![1, 1, 1] ^ 2) (heisE K a) = 0 := by
  have h1 := heisE_orbit a 1
  rw [pow_one] at h1
  rw [h1, heisE_orbit a 2, heisE]
  refine Prod.ext (funext fun i => ?_) ?_
  · fin_cases i <;> refine Prod.ext ?_ ?_ <;>
      simp [planeVec, Pi.single_apply, pow_two, rotLE_apply] <;> ring
  · simp [planeVec]

theorem heisE_indep (a : K × K) (s t : K)
    (h : s • heisE K a + t • cmEquiv K ![1, 1, 1] (heisE K a) = 0) : s = 0 ∧ t = 0 := by
  have h1 := heisE_orbit a 1
  rw [pow_one] at h1
  rw [h1] at h
  have h0 := congrArg (fun x : ModelSpace K => x.1 0) h
  simp [heisE, planeVec, rotLE_apply] at h0
  exact h0

theorem heisData_model [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {a : K × K} (ha : rotForm K a = -1) :
    HeisData (modelForm b c) (cmEquiv K ![1, 1, 1]) (heisE K a) (heisD K) where
  mem := cm_mem_modelO b c (Multiplicative.ofAdd ![1, 1, 1])
  pow_three := cmEquiv_one_one_one_pow_three
  sum_e := heisE_sum a
  orth_ee := polar_heis_orbit_ee b c ha
  orth_ed := polar_heis_orbit_ed b c a
  orth_dd := polar_heis_orbit_dd b c
  ne_d := by rw [modelForm_heisD]; exact one_ne_zero
  indep := heisE_indep a
  nondeg := nondegenerate_polarBilin_modelForm h3 hbc

theorem cmEquiv_apply_heisE (a : K × K) {t : Fin 3 → ZMod 3} (h0 : t 0 = 0) (h1 : t 1 = 0) :
    cmEquiv K t (heisE K a) = heisE K a ∧
      cmEquiv K t (cmEquiv K ![1, 1, 1] (heisE K a)) = cmEquiv K ![1, 1, 1] (heisE K a) := by
  have h1' := heisE_orbit a 1
  rw [pow_one] at h1'
  refine ⟨?_, ?_⟩
  · rw [heisE, map_add, cmEquiv_apply_planeVec, cmEquiv_apply_planeVec, h0, h1, rotPow_zero]
    rfl
  · rw [h1', map_add, cmEquiv_apply_planeVec, cmEquiv_apply_planeVec, h0, h1, rotPow_zero]
    rfl

theorem two_ne_zero_of_charP_ne_two {p : ℕ} (hp : p.Prime) [CharP K p] (hp2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')

theorem exists_heisenberg_pair_model [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p] (hp2 : p ≠ 2) :
    ∃ S T : ModelSpace K ≃ₗ[K] ModelSpace K, S ∈ modelOmega b c ∧ T ∈ modelOmega b c ∧
      orderOf S = p ∧ orderOf T = p ∧ Commute S T ∧ T ∉ Subgroup.zpowers S ∧
      Commute S (cmEquiv K ![1, 1, 1]) ∧ Commute T (cmEquiv K ![1, 1, 1]) ∧
      Commute T (cmEquiv K ![0, 0, 1]) := by
  obtain ⟨a, ha⟩ := exists_rotForm_eq h3 (-1)
  have h := heisData_model (b := b) (c := c) h3 hbc ha
  obtain ⟨S, T, hS, hT, hSo, hTo, hST, hTS, hSg, hTg, hTk⟩ :=
    exists_heisenberg_pair (two_ne_zero_of_charP_ne_two hp hp2) h3 hp h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨S, T, mem_modelOmega_of_odd h3 hbc hS (by rw [hSo]; exact hodd),
    mem_modelOmega_of_odd h3 hbc hT (by rw [hTo]; exact hodd), hSo, hTo, hST, hTS, hSg, hTg, ?_⟩
  obtain ⟨hf1, hf2⟩ := cmEquiv_apply_heisE a (t := ![0, 0, 1]) rfl rfl
  exact hTk _ (cm_mem_modelO b c (Multiplicative.ofAdd ![0, 0, 1])) hf1 hf2

theorem two_le_pRank_centralizer_c₀_u [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p] (hp2 : p ≠ 2) :
    2 ≤ pRank p (Subgroup.centralizer
      ({c₀ h3 hbc (Multiplicative.ofAdd ![1, 1, 1])} : Set ↥(omegaMinus8 K b c))) := by
  obtain ⟨S, T, hS, hT, hSo, hTo, hST, hTS, hSg, hTg, -⟩ :=
    exists_heisenberg_pair_model h3 hbc hp hp2
  have := two_le_pRank_centralizer_c₀_of_model h3 hbc hp
    {Multiplicative.ofAdd ![1, 1, 1]} hS hT hSo hTo hST hTS
    (by rintro s rfl; exact hSg) (by rintro s rfl; exact hTg)
  rwa [Set.image_singleton] at this

theorem one_le_pRank_centralizer_c₀_u_e₂ [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p] (hp2 : p ≠ 2) :
    1 ≤ pRank p (Subgroup.centralizer
      ({c₀ h3 hbc (Multiplicative.ofAdd ![1, 1, 1]),
        c₀ h3 hbc (Multiplicative.ofAdd ![0, 0, 1])} : Set ↥(omegaMinus8 K b c))) := by
  obtain ⟨S, T, hS, hT, hSo, hTo, hST, hTS, hSg, hTg, hTe⟩ :=
    exists_heisenberg_pair_model h3 hbc hp hp2
  have := one_le_pRank_centralizer_c₀_of_model h3 hbc hp
    {Multiplicative.ofAdd ![1, 1, 1], Multiplicative.ofAdd ![0, 0, 1]} hT hTo
    (by rintro s (rfl | rfl); exacts [hTg, hTe])
  rwa [Set.image_pair] at this

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
