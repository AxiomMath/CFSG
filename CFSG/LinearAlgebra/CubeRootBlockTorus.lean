module

public import CFSG.LinearAlgebra.CubeRootBlock
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K]

theorem orderOf_cubeRootDiag (l : Kˣ) : orderOf (cubeRootDiag l) = orderOf l := by
  let f : Kˣ →* SL(2, K) :=
    { toFun := fun u => cubeRootDiag u
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [cubeRootDiag]
      map_mul' := by
        intro a b
        ext i j
        rw [Matrix.SpecialLinearGroup.coe_mul]
        fin_cases i <;> fin_cases j <;>
          simp [cubeRootDiag, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] }
  have hf : Function.Injective f := by
    intro a b hab
    apply Units.ext
    have hab' : cubeRootDiag a = cubeRootDiag b := hab
    have h := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hab'
    simpa [cubeRootDiag] using h
  have h := orderOf_injective f hf l
  change orderOf (f l) = orderOf l
  exact h

theorem exists_commute_orderOf_eq_cubeRootDiag [Finite K] (ω : Kˣ) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) :
    ∃ z : SL(2, K),
      Commute (z : Matrix (Fin 2) (Fin 2) K) (cubeRootDiag ω : Matrix (Fin 2) (Fin 2) K) ∧
        orderOf z = p := by
  haveI := Fact.mk hp
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨cubeRootDiag l, ?_, ?_⟩
  · rw [commute_iff_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeRootDiag, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  · rw [orderOf_cubeRootDiag, hl]

private theorem card_centralizer_toGL_cubeRootBlock_card_vectors [Finite K] :
    Nat.card {v : Fin 2 → K // v ≠ 0} = Nat.card K ^ 2 - 1 := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fintype {v : Fin 2 → K // v ≠ 0} := Fintype.ofFinite _
  haveI : Fintype {v : Fin 2 → K // v = 0} := Fintype.ofFinite _
  haveI : Unique {v : Fin 2 → K // v = 0} :=
    { default := ⟨0, rfl⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have hzero : Fintype.card {v : Fin 2 → K // v = 0} = 1 := Fintype.card_unique
  have htotal : Fintype.card (Fin 2 → K) = Fintype.card K ^ 2 := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun v : Fin 2 → K => v = 0), htotal, hzero]

private theorem eq_zero_of_sq_add_mul_add_sq_of_not_dvd_card_sub_one [Finite K]
    (h3 : (3 : K) ≠ 0) (hq : ¬ Nat.card K % 3 = 1) {a b : K}
    (h : a ^ 2 + a * b + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [mul_zero, zero_pow two_ne_zero, add_zero] at h
    exact ⟨sq_eq_zero_iff.mp h, rfl⟩
  · exfalso
    have hxroot : (a / b) ^ 2 + a / b + 1 = 0 := by
      field_simp [hb]
      linear_combination h
    have hxne : a / b ≠ 0 := by
      intro hx0
      rw [hx0] at hxroot
      norm_num at hxroot
    have hxunit : IsUnit (a / b) := isUnit_iff_ne_zero.mpr hxne
    let u : Kˣ := hxunit.unit
    have hu : (u : K) = a / b := hxunit.unit_spec
    have huroot : (u : K) ^ 2 + u + 1 = 0 := by rw [hu]; exact hxroot
    exact hq ((exists_unit_sq_add_self_add_one_iff h3).mp ⟨u, huroot⟩)

private noncomputable def card_centralizer_toGL_cubeRootBlock_firstColumn [Finite K] :
    Subgroup.centralizer ({SpecialLinearGroup.toGL (cubeRootBlock K)} : Set (GL (Fin 2) K)) →
      {v : Fin 2 → K // v ≠ 0} :=
  fun z => ⟨(z : GL (Fin 2) K).val *ᵥ ![1, 0], by
    intro hzero
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero
      (Matrix.GeneralLinearGroup.det_ne_zero (z : GL (Fin 2) K)) hzero
    have h1 : (![1, 0] : Fin 2 → K) 0 = 0 := congrFun h0 0
    norm_num at h1⟩

private theorem card_centralizer_toGL_cubeRootBlock_firstColumn_eq_one [Finite K]
    (h3 : (3 : K) ≠ 0) {t : GL (Fin 2) K}
    (htcol : (t : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0])
    (ht : Commute (t : Matrix (Fin 2) (Fin 2) K)
      (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K)) : t = 1 := by
  have hs : IsCubeRootBlock (cubeRootBlock K) := isCubeRootBlock_cubeRootBlock h3
  obtain ⟨x, y, hxy⟩ := hs.commute_iff.mp ht
  have h00 : (t : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h := congrFun htcol 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have h10 : (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h := congrFun htcol 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hx : x = 1 := by
    have h := congrFun (congrFun hxy 0) 0
    simp [cubeRootBlock] at h
    rw [h00] at h
    exact h.symm
  have hy : y = 0 := by
    have h := congrFun (congrFun hxy 1) 0
    simp [cubeRootBlock] at h
    rw [h10] at h
    exact neg_eq_zero.mp h.symm
  apply Units.ext
  rw [hxy, hx, hy]
  simp

private theorem card_centralizer_toGL_cubeRootBlock_firstColumn_injective [Finite K]
    (h3 : (3 : K) ≠ 0) :
    Function.Injective (card_centralizer_toGL_cubeRootBlock_firstColumn (K := K)) := by
  classical
  haveI := Fintype.ofFinite K
  let g : GL (Fin 2) K := SpecialLinearGroup.toGL (cubeRootBlock K)
  intro z w hzw
  have hcol : (z : GL (Fin 2) K).val *ᵥ (![1, 0] : Fin 2 → K) =
      (w : GL (Fin 2) K).val *ᵥ ![1, 0] := congrArg Subtype.val hzw
  let t : GL (Fin 2) K := (z : GL (Fin 2) K)⁻¹ * (w : GL (Fin 2) K)
  have htcol : (t : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
    change (((z : GL (Fin 2) K)⁻¹).val * (w : GL (Fin 2) K).val) *ᵥ ![1, 0] = ![1, 0]
    rw [← Matrix.mulVec_mulVec, ← hcol, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have htz : Commute (z : GL (Fin 2) K) g := by
    rw [commute_iff_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mp z.2
  have htw : Commute (w : GL (Fin 2) K) g := by
    rw [commute_iff_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mp w.2
  have htGL : Commute t g := by
    have := (htz.inv_left).mul_left htw
    simpa [t] using this
  have ht : Commute (t : Matrix (Fin 2) (Fin 2) K)
      (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K) := by
    rw [commute_iff_eq]
    have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) htGL.eq
    simpa [g, SpecialLinearGroup.coe_GL_coe_matrix] using h
  have ht1 : t = 1 :=
    card_centralizer_toGL_cubeRootBlock_firstColumn_eq_one h3 htcol ht
  apply Subtype.ext
  exact inv_mul_eq_one.mp (by simpa [t] using ht1)

private theorem card_centralizer_toGL_cubeRootBlock_firstColumn_surjective [Finite K]
    (h3 : (3 : K) ≠ 0) (hq : ¬ Nat.card K % 3 = 1) :
    Function.Surjective (card_centralizer_toGL_cubeRootBlock_firstColumn (K := K)) := by
  classical
  haveI := Fintype.ofFinite K
  have hs : IsCubeRootBlock (cubeRootBlock K) := isCubeRootBlock_cubeRootBlock h3
  let sMat : Matrix (Fin 2) (Fin 2) K := cubeRootBlock K
  let g : GL (Fin 2) K := SpecialLinearGroup.toGL (cubeRootBlock K)
  have hgval : (g : Matrix (Fin 2) (Fin 2) K) = sMat := rfl
  let e0 : Fin 2 → K := ![1, 0]
  rintro ⟨v, hv⟩
  let M : Matrix (Fin 2) (Fin 2) K :=
    v 0 • (1 : Matrix (Fin 2) (Fin 2) K) + (-(v 1)) • sMat
  have hMdet : M.det ≠ 0 := by
    have hdet : M.det = v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2 := by
      show (v 0 • (1 : Matrix (Fin 2) (Fin 2) K) +
        (-(v 1)) • (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K)).det = _
      rw [hs.det_smul_one_add_smul]
      ring
    intro hzero
    obtain ⟨h0, h1⟩ :=
      eq_zero_of_sq_add_mul_add_sq_of_not_dvd_card_sub_one h3 hq (hdet.symm.trans hzero)
    apply hv
    funext i
    fin_cases i <;> simpa [h0, h1]
  let z : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
  have hzval : (z : Matrix (Fin 2) (Fin 2) K) = M := by simp [z]
  have hMcomm : Commute M sMat := by
    show Commute (v 0 • (1 : Matrix (Fin 2) (Fin 2) K) +
      (-(v 1)) • (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K)) _
    exact ((Commute.one_left _).smul_left (v 0)).add_left
      ((Commute.refl _).smul_left (-(v 1)))
  have hzmem : z ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    show (z : Matrix (Fin 2) (Fin 2) K) * sMat = sMat * (z : Matrix (Fin 2) (Fin 2) K)
    rw [hzval]
    exact hMcomm
  refine ⟨⟨z, hzmem⟩, ?_⟩
  apply Subtype.ext
  change (z : Matrix (Fin 2) (Fin 2) K) *ᵥ e0 = v
  rw [hzval]
  funext i
  fin_cases i <;> simp [M, e0, sMat, cubeRootBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem card_centralizer_toGL_cubeRootBlock [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : ¬ Nat.card K % 3 = 1) :
    Nat.card (Subgroup.centralizer
      ({SpecialLinearGroup.toGL (cubeRootBlock K)} : Set (GL (Fin 2) K))) = Nat.card K ^ 2 - 1 := by
  classical
  haveI := Fintype.ofFinite K
  have hbij : Function.Bijective (card_centralizer_toGL_cubeRootBlock_firstColumn (K := K)) :=
    ⟨card_centralizer_toGL_cubeRootBlock_firstColumn_injective h3,
      card_centralizer_toGL_cubeRootBlock_firstColumn_surjective h3 hq⟩
  calc Nat.card (Subgroup.centralizer
        ({SpecialLinearGroup.toGL (cubeRootBlock K)} : Set (GL (Fin 2) K)))
      = Nat.card {v : Fin 2 → K // v ≠ 0} :=
        Nat.card_congr (Equiv.ofBijective _ hbij)
    _ = Nat.card K ^ 2 - 1 := card_centralizer_toGL_cubeRootBlock_card_vectors

theorem det_eq_one_of_orderOf_eq_of_not_dvd [Finite K] {n : ℕ} {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K - 1) {z : GL (Fin n) K} (hz : orderOf z = p) :
    (z : Matrix (Fin n) (Fin n) K).det = 1 := by
  haveI := Fact.mk hp
  let d : Kˣ := GeneralLinearGroup.det z
  have hzp : z ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hdpow : d ^ p = 1 := by rw [← map_pow, hzp, map_one]
  have hdivp : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one hdpow
  have hdivq : orderOf d ∣ Nat.card K - 1 := by
    have h := orderOf_dvd_natCard d
    rwa [Nat.card_units] at h
  have hord1 : orderOf d = 1 := by
    rcases (Nat.dvd_prime hp).mp hdivp with h1 | hp1
    · exact h1
    · exact absurd (hp1 ▸ hdivq) hpq
  have hd1 : d = 1 := orderOf_eq_one_iff.mp hord1
  have h := congrArg (fun u : Kˣ => (u : K)) hd1
  simpa [d] using h

theorem exists_commute_orderOf_eq_cubeRootBlock [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : ¬ Nat.card K % 3 = 1) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    ∃ z : SL(2, K), Commute (z : Matrix (Fin 2) (Fin 2) K)
      (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K) ∧ orderOf z = p := by
  haveI := Fact.mk hp
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard : p ∣ Nat.card (Subgroup.centralizer
      ({SpecialLinearGroup.toGL (cubeRootBlock K)} : Set (GL (Fin 2) K))) := by
    rw [card_centralizer_toGL_cubeRootBlock h3 hq]
    have hfac : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      simpa using (Nat.sq_sub_sq (Nat.card K) 1)
    rw [hfac]
    exact dvd_mul_of_dvd_left hpq _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hpq' : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hd
      have e : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
      rwa [e] at h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hzGL : orderOf (z : GL (Fin 2) K) = p := by
    rwa [Subgroup.orderOf_coe]
  have hdet : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    det_eq_one_of_orderOf_eq_of_not_dvd hp hpq' hzGL
  let w : SL(2, K) := ⟨((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), hdet⟩
  have hwz : SpecialLinearGroup.toGL w = (z : GL (Fin 2) K) := Units.ext rfl
  have hword : orderOf w = p := by
    rw [← orderOf_injective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective w, hwz, hzGL]
  have hwcomm : Commute (w : Matrix (Fin 2) (Fin 2) K)
      (cubeRootBlock K : Matrix (Fin 2) (Fin 2) K) := by
    rw [commute_iff_eq]
    have h := Subgroup.mem_centralizer_singleton_iff.mp z.2
    have h' := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h
    rw [← hwz] at h'
    simpa [SpecialLinearGroup.coe_GL_coe_matrix] using h'
  exact ⟨w, hwcomm, hword⟩

theorem exists_commute_orderOf_eq_cubeRootBlockStd [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) :
    ∃ z : SL(2, K), Commute (z : Matrix (Fin 2) (Fin 2) K)
      (cubeRootBlockStd K : Matrix (Fin 2) (Fin 2) K) ∧ orderOf z = p := by
  by_cases hq1 : Nat.card K % 3 = 1
  · obtain ⟨ω, _, hblock⟩ := cubeRootBlockStd_eq_cubeRootDiag h3 hq1
    have hpq' : p ∣ Nat.card K - 1 := by simpa [if_pos hq1] using hpq
    obtain ⟨z, hz, hord⟩ := exists_commute_orderOf_eq_cubeRootDiag ω hp hpq'
    exact ⟨z, by rwa [hblock], hord⟩
  · have hpq' : p ∣ Nat.card K + 1 := by simpa [if_neg hq1] using hpq
    obtain ⟨z, hz, hord⟩ := exists_commute_orderOf_eq_cubeRootBlock h3 hq1 hp h5 hpq'
    exact ⟨z, by rwa [cubeRootBlockStd_eq_cubeRootBlock h3 hq1], hord⟩

end CFSG.LinearAlgebra
