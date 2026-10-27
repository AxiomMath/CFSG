module

public import CFSG.Fischer.Classification.Unitary.Basic
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.AS35ZS

open Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

noncomputable abbrev vecK (v : Fin n → F4) : Fin n → K := fun i => eF4 (v i)

@[expose] def herm4 (x y : Fin n → F4) : F4 := ∑ i, x i ^ 2 * y i

@[expose] def tv4 (x v : Fin n → F4) : Fin n → F4 := v + herm4 x v • x

theorem herm_vecK (x y : Fin n → F4) : herm frob (vecK x) (vecK y) = eF4 (herm4 x y) := by
  simp only [herm_def, herm4, map_sum, map_mul, frob_eF4, map_pow]

theorem vecK_add (x y : Fin n → F4) : vecK (x + y) = vecK x + vecK y := by
  funext i
  simp only [vecK, Pi.add_apply, map_add]

theorem vecK_smul (c : F4) (x : Fin n → F4) : vecK (c • x) = eF4 c • vecK x := by
  funext i
  simp only [vecK, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecK_injective : Function.Injective (vecK (n := n)) := fun x y h => by
  funext i
  exact eF4.injective (congrFun h i)

theorem eq_vecK (u : Fin n → K) : u = vecK (fun i => eF4.symm (u i)) := by
  funext i
  simp

theorem tvU_vecK_smul {x : Fin n → F4} (hx : herm4 x x = 0) (v : Fin n → F4) :
    tvU (vecK x) • vecK v = vecK (tv4 x v) := by
  have hx' : herm frob (vecK x) (vecK x) = 0 := by rw [herm_vecK, hx, map_zero]
  rw [tvU_smul hx', tv4, vecK_add, vecK_smul, herm_vecK]

noncomputable abbrev matK (M : Matrix (Fin n) (Fin n) F4) : Matrix (Fin n) (Fin n) K :=
  M.map eF4

@[expose] def ctr4 (M : Matrix (Fin n) (Fin n) F4) : Matrix (Fin n) (Fin n) F4 :=
  (M.map (· ^ 2))ᵀ

theorem conjTr_matK (M : Matrix (Fin n) (Fin n) F4) :
    conjTr frob (matK M) = matK (ctr4 M) := by
  ext i j
  simp only [conjTr, ctr4, Matrix.map_apply, Matrix.transpose_apply, frob_apply, map_pow]

theorem matK_mul (M N : Matrix (Fin n) (Fin n) F4) : matK (M * N) = matK M * matK N :=
  Matrix.map_mul

theorem matK_one : matK (1 : Matrix (Fin n) (Fin n) F4) = 1 := by
  ext i j
  simp [Matrix.one_apply]

theorem det_matK (M : Matrix (Fin n) (Fin n) F4) : (matK M).det = eF4 M.det :=
  (RingHom.map_det (eF4 : F4 →+* K) M).symm

theorem matK_mulVec (M : Matrix (Fin n) (Fin n) F4) (v : Fin n → F4) :
    matK M *ᵥ vecK v = vecK (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (eF4 : F4 →+* K) M v i).symm

@[expose] noncomputable def su4 (M : Matrix (Fin n) (Fin n) F4) (hdet : M.det = 1)
    (hu : ctr4 M * M = 1) : SUid frob n :=
  mkSU frob (matK M) (by rw [det_matK, hdet, map_one]) (fun x y => by
    rw [herm_mulVec, conjTr_matK, ← matK_mul, hu, matK_one, one_mulVec])

theorem su4_smul (M : Matrix (Fin n) (Fin n) F4) (hdet : M.det = 1) (hu : ctr4 M * M = 1)
    (v : Fin n → K) : su4 M hdet hu • v = matK M *ᵥ v := rfl

@[expose] def wordApply : List (Fin n → F4) → (Fin n → F4) → (Fin n → F4)
  | [], v => v
  | x :: l, v => tv4 x (wordApply l v)

@[expose] noncomputable def wordElt : List (Fin n → F4) → SUid frob n
  | [] => 1
  | x :: l => tvU (vecK x) * wordElt l

theorem wordElt_smul (l : List (Fin n → F4)) (hl : ∀ x ∈ l, herm4 x x = 0) (v : Fin n → F4) :
    wordElt l • vecK v = vecK (wordApply l v) := by
  induction l with
  | nil => exact one_smul _ _
  | cons x l ih =>
    rw [wordElt, wordApply, mul_smul, ih (fun y hy => hl y (List.mem_cons_of_mem x hy)),
      tvU_vecK_smul (hl x List.mem_cons_self)]

theorem tvU_mem_T' (x : Fin n → K) : tvU x ∈ T frob n := by
  by_cases hx : herm frob x x = 0
  · exact tvU_mem_T hx
  · have : tvU x = 1 := by
      unfold tvU
      exact dite_eq_right_of_eq_false (eq_false hx) ▸ rfl
    rw [this]
    exact Subgroup.one_mem _

theorem wordElt_mem_T (l : List (Fin n → F4)) : wordElt l ∈ T frob n := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons x l ih => exact Subgroup.mul_mem _ (tvU_mem_T' _) ih

@[expose] def w2 : F4 := F4.ω * F4.ω

@[expose] def hMat (μ : F4) : Matrix (Fin 3) (Fin 3) F4 :=
  if μ = 1 then !![1, 1, 1; 1, F4.ω, w2; 1, w2, F4.ω]
  else if μ = F4.ω then !![1, 1, w2; 1, F4.ω, F4.ω; F4.ω, 1, F4.ω]
  else if μ = w2 then !![1, 1, F4.ω; 1, F4.ω, 1; w2, F4.ω, F4.ω]
  else 1

@[expose] def hVec (μ : F4) : Fin 3 → F4 := if μ = 0 then 0 else ![0, 1, μ]

theorem hMat_facts : ∀ μ : F4, (hMat μ).det = 1 ∧ ctr4 (hMat μ) * hMat μ = 1 ∧
    hMat μ * hMat μ = 1 + vecMulVec (hVec μ) (fun i => hVec μ i ^ 2) ∧
    herm4 (hVec μ) (hVec μ) = 0 := by
  intro μ
  rw [Matrix.det_fin_three]
  revert μ
  decide

@[expose] noncomputable def hElt (μ : F4) : SUid frob 3 :=
  su4 (hMat μ) (hMat_facts μ).1 (hMat_facts μ).2.1

theorem hElt_smul_vecK (μ : F4) (v : Fin 3 → F4) : hElt μ • vecK v = vecK (hMat μ *ᵥ v) :=
  matK_mulVec _ v

theorem matK_tv (w : Fin 3 → F4) :
    matK (1 + vecMulVec w (fun i => w i ^ 2)) = tvMat frob (vecK w) 1 := by
  ext i j
  simp [tvMat, Matrix.one_apply, vecMulVec_apply, frobenius_def, apply_ite eF4]

theorem hElt_sq (μ : F4) : hElt μ ^ 2 = tvU (vecK (hVec μ)) := by
  have hiso : herm frob (vecK (hVec μ)) (vecK (hVec μ)) = 0 := by
    rw [herm_vecK, (hMat_facts μ).2.2.2, map_zero]
  refine ext_smul _ fun v => ?_
  rw [sq, mul_smul, hElt, su4_smul, su4_smul, mulVec_mulVec, ← matK_mul, (hMat_facts μ).2.2.1,
    matK_tv, tvMat_mulVec, one_mul, tvU_smul hiso]

theorem hElt_sq_mem_T (μ : F4) : hElt μ ^ 2 ∈ T frob 3 := by
  rw [hElt_sq]
  exact tvU_mem_T' _

@[expose] def e04 : Fin 3 → F4 := ![1, 0, 0]

theorem e0_eq_vecK : e0 K 2 = vecK e04 := by
  funext i
  fin_cases i <;> simp [vecK, e04, e0]

@[expose] def unitWord (u : Fin 3 → F4) : List (Fin 3 → F4) × F4 :=
  if u 1 = 0 ∧ u 2 = 0 then ([![1, 1, 0], ![1, u 0, 0]], 0)
  else if u 0 = 0 ∧ u 2 = 0 then ([![1, u 1, 0]], 0)
  else if u 0 = 0 ∧ u 1 = 0 then ([![1, 0, u 2]], 0)
  else ([![1, 1, 0], ![1, u 0, 0], ![0, 1, 1], ![0, 1, u 0 * u 1]], u 0 * u 1 * u 2)

theorem unitWord_spec : ∀ u : Fin 3 → F4, herm4 u u = 1 →
    wordApply (unitWord u).1 (hMat (unitWord u).2 *ᵥ e04) = u ∧
      ∀ x ∈ (unitWord u).1, herm4 x x = 0 := by
  decide +kernel

theorem fix_e0_mem_T {g : SUid frob 3} (hg : g • e0 K 2 = e0 K 2) : g ∈ T frob 3 :=
  mem_T_of_blk_mem_T frob_frob hg (by
    rw [T_two_eq_top isUnitaryInvolution_frob]
    exact Subgroup.mem_top _)

theorem sq_mem_T_three (g : SUid frob 3) : g ^ 2 ∈ T frob 3 := by
  set u := g • e0 K 2 with hudef
  have hu : herm frob u u = 1 := by rw [hudef, herm_smul_smul, herm_e0_e0]
  set u4 : Fin 3 → F4 := fun i => eF4.symm (u i) with hu4def
  have hu4 : u = vecK u4 := eq_vecK u
  have hu4' : herm4 u4 u4 = 1 := eF4.injective (by rw [← herm_vecK, ← hu4, hu, map_one])
  obtain ⟨hw, hiso⟩ := unitWord_spec u4 hu4'
  set m := wordElt (unitWord u4).1 with hm
  set h := hElt (unitWord u4).2 with hh
  have hmh : (m * h) • e0 K 2 = u := by
    rw [mul_smul, e0_eq_vecK, hh, hElt_smul_vecK, hm, wordElt_smul _ hiso, hw, hu4]
  have hk : ((m * h)⁻¹ * g) • e0 K 2 = e0 K 2 := by
    rw [mul_smul, ← hudef, ← hmh, inv_smul_smul]
  have hkT := fix_e0_mem_T hk
  set k := (m * h)⁻¹ * g with hkdef
  have hg : g = m * h * k := by rw [hkdef]; group
  have hmT : m ∈ T frob 3 := wordElt_mem_T _
  have hcT : h * (k * m) * h⁻¹ ∈ T frob 3 := (T_normal (σ := frob) (n := 3)).conj_mem _
    (Subgroup.mul_mem _ hkT hmT) h
  rw [hg, show (m * h * k) ^ 2 = m * (h * (k * m) * h⁻¹) * h ^ 2 * k by rw [sq, sq]; group]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hmT hcT)
    (hElt_sq_mem_T _)) hkT

end CFSG.LargeExtraspecial.AS35ZS
