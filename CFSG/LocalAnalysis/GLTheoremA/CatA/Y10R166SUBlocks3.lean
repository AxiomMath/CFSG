module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K]

private theorem diagonal_mul_vecMulVec_mul_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (a u v b : n → K) :
    diagonal a * vecMulVec u v * diagonal b =
      vecMulVec (fun i => a i * u i) (fun j => v j * b j) := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [vecMulVec]
  ring

private theorem bar_eq_inv_of_norm_eq_one (h : UnitaryFieldData 2 f K) {c : K}
    (hc : h.norm c = 1) : h.bar c = c⁻¹ := by
  rw [UnitaryFieldData.norm] at hc
  exact eq_inv_of_mul_eq_one_right hc

@[expose] def suRadConjVec (c : K) (d m : Fin 6 → K) : Fin 6 → K :=
  fun i => if i = 2 ∨ i = 3 ∨ i = 4 then c * (d i)⁻¹ * m i else 0

theorem suRadConjVec_bar_suRadVec (h : UnitaryFieldData 2 f K) {c : K} (hc : h.norm c = 1)
    {d : Fin 6 → K} (hd : ∀ i, h.norm (d i) = 1) (m : Fin 6 → K) :
    (fun i => h.bar (suRadConjVec c d m i)) =
      suRadVec (fun i => c⁻¹ * d i * h.bar (m i)) := by
  funext i
  by_cases hi : i = 2 ∨ i = 3 ∨ i = 4
  · simp only [suRadVec, suRadConjVec, hi, if_true]
    rw [map_mul, map_mul, map_inv₀, bar_eq_inv_of_norm_eq_one h hc,
      bar_eq_inv_of_norm_eq_one h (hd i), inv_inv]
  · simp only [suRadVec, suRadConjVec, hi, if_false, map_zero]

theorem suRadVec_suRadConjVec (c : K) (d m : Fin 6 → K) :
    suRadVec (suRadConjVec c d m) = suRadConjVec c d m := by
  funext i
  by_cases hi : i = 2 ∨ i = 3 ∨ i = 4 <;> simp [suRadVec, suRadConjVec, hi]

theorem unitaryRadMatrix_conj_diag (h : UnitaryFieldData 2 f K) {d : Fin 6 → K}
    (hd : ∀ i, h.norm (d i) = 1) (hd0 : d 0 = d 1) (m : Fin 6 → K) (y : K) :
    diagonal d * unitaryRadMatrix h m y * diagonal (fun i => (d i)⁻¹) =
      unitaryRadMatrix h (suRadConjVec (d 0) d m) y := by
  haveI : CharP K 2 := h.charP
  have hdne : ∀ i, d i ≠ 0 := fun i =>
    CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one (hd i)
  have h1 : (fun i => d i * suLineVec i) = d 0 • suLineVec := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, suLineVec]
    split_ifs with hi
    · rcases hi with rfl | rfl <;> simp [hd0]
    · simp
  have h2 : (fun j => suLineVec j * (d j)⁻¹) = (d 0)⁻¹ • suLineVec := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, suLineVec]
    split_ifs with hj
    · rcases hj with rfl | rfl <;> simp [hd0]
    · simp
  have h4 : (fun i => d i * suRadVec (fun i => h.bar (m i)) i) =
      suRadVec (fun i => d i * h.bar (m i)) := by
    funext i
    by_cases hi : i = 2 ∨ i = 3 ∨ i = 4 <;> simp [suRadVec, hi]
  have hU : diagonal d * vecMulVec suLineVec suLineVec * diagonal (fun i => (d i)⁻¹) =
      vecMulVec suLineVec suLineVec := by
    rw [diagonal_mul_vecMulVec_mul_diagonal, h1, h2, smul_vecMulVec, vecMulVec_smul, smul_smul,
      mul_inv_cancel₀ (hdne 0), one_smul]
  have hV : diagonal d * vecMulVec suLineVec (suRadVec m) * diagonal (fun i => (d i)⁻¹) =
      vecMulVec suLineVec (suRadVec (suRadConjVec (d 0) d m)) := by
    rw [diagonal_mul_vecMulVec_mul_diagonal, h1, smul_vecMulVec, ← vecMulVec_smul]
    congr 1
    funext j
    by_cases hj : j = 2 ∨ j = 3 ∨ j = 4
    · simp only [suRadVec, suRadConjVec, hj, if_true, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [suRadVec, hj, Pi.smul_apply, smul_eq_mul]
  have hW : diagonal d * vecMulVec (suRadVec (fun i => h.bar (m i))) suLineVec *
      diagonal (fun i => (d i)⁻¹) =
      vecMulVec (suRadVec (fun i => h.bar (suRadConjVec (d 0) d m i))) suLineVec := by
    rw [diagonal_mul_vecMulVec_mul_diagonal, h4, h2, vecMulVec_smul, ← smul_vecMulVec]
    congr 1
    rw [suRadConjVec_bar_suRadVec h (hd 0) hd m]
    funext i
    by_cases hi : i = 2 ∨ i = 3 ∨ i = 4
    · simp only [suRadVec, hi, if_true, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [suRadVec, hi, Pi.smul_apply, smul_eq_mul]
  have h1d : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => d i * (d i)⁻¹) = fun _ => 1 := by
      funext i; exact mul_inv_cancel₀ (hdne i)
    rw [h, Matrix.diagonal_one]
  simp only [unitaryRadMatrix, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    one_mul]
  rw [h1d, hU, hV, hW]
  try module


theorem diagSU_inv (h : UnitaryFieldData 2 f K) {d : Fin 6 → K}
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) :
    (diagSU h d hd hdet)⁻¹ =
      diagSU h (fun i => (d i)⁻¹) (fun i => by rw [norm_inv_eq h, hd i, inv_one])
        (by rw [Finset.prod_inv_distrib, hdet, inv_one]) := by
  apply mul_left_cancel (a := diagSU h d hd hdet)
  rw [mul_inv_cancel]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagSU, OneMemClass.coe_one, Units.val_one,
    Matrix.diagonal_mul_diagonal]
  have h : (fun i => d i * (d i)⁻¹) = fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one (hd i))
  rw [h, Matrix.diagonal_one]

theorem suRadCocycle_suRadConjVec (h : UnitaryFieldData 2 f K) {c : K} (hc : h.norm c = 1)
    {d : Fin 6 → K} (hd : ∀ i, h.norm (d i) = 1) (m : Fin 6 → K) :
    suRadCocycle h (suRadConjVec c d m) = suRadCocycle h m := by
  have hc0 : c ≠ 0 := CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one hc
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one (hd i)
  simp only [suRadCocycle]
  rw [suRadVec_suRadConjVec]
  simp only [suRadConjVec, suRadVec, Fin.sum_univ_six, Fin.isValue]
  norm_num
  simp only [map_mul, map_inv₀, bar_eq_inv_of_norm_eq_one h hc,
    bar_eq_inv_of_norm_eq_one h (hd 2), bar_eq_inv_of_norm_eq_one h (hd 3),
    bar_eq_inv_of_norm_eq_one h (hd 4), inv_inv]
  try field_simp [hc0, hd0 2, hd0 3, hd0 4]

theorem diagSU_conj_unitaryRadElem (h : UnitaryFieldData 2 f K) {d : Fin 6 → K}
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (hd0 : d 0 = d 1)
    (m : Fin 6 → K) (y : K) (hy : y + h.bar y = suRadCocycle h m) :
    diagSU h d hd hdet * unitaryRadElem h m y hy * (diagSU h d hd hdet)⁻¹ =
      unitaryRadElem h (suRadConjVec (d 0) d m) y
        (by rw [suRadCocycle_suRadConjVec h (hd 0) hd]; exact hy) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryRadElem, coe_diagSU, diagSU_inv]
  rw [unitaryRadMatrix_conj_diag h hd hd0 m y]

theorem diagSU_mem_normalizer_unitaryLineRadical (h : UnitaryFieldData 2 f K) {d : Fin 6 → K}
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (hd0 : d 0 = d 1) :
    diagSU h d hd hdet ∈
      Subgroup.normalizer (unitaryLineRadical h : Set (unitarySU 2 f K 6)) := by
  have hmem : ∀ A ∈ unitaryLineRadical h,
      diagSU h d hd hdet * A * (diagSU h d hd hdet)⁻¹ ∈ unitaryLineRadical h := by
    rintro A ⟨m, y, hy, rfl⟩
    exact ⟨suRadConjVec (d 0) d m, y,
      by rw [suRadCocycle_suRadConjVec h (hd 0) hd]; exact hy,
      diagSU_conj_unitaryRadElem h hd hdet hd0 m y hy⟩
  have hmem' : ∀ A ∈ unitaryLineRadical h,
      (diagSU h d hd hdet)⁻¹ * A * diagSU h d hd hdet ∈ unitaryLineRadical h := by
    rintro A ⟨m, y, hy, rfl⟩
    have hd' : ∀ i, h.norm ((d i)⁻¹) = 1 := fun i => by rw [norm_inv_eq h, hd i, inv_one]
    have hdet' : ∏ i, (d i)⁻¹ = 1 := by
      rw [show (∏ i, (d i)⁻¹) = (∏ i, d i)⁻¹ from by
        simpa using Finset.prod_inv_distrib (s := Finset.univ) d, hdet, inv_one]
    have hd0' : (d 0)⁻¹ = (d 1)⁻¹ := by rw [hd0]
    have hthis := diagSU_conj_unitaryRadElem h hd' hdet' hd0' m y hy
    rw [diagSU_inv] at hthis
    have hfun : (fun i => ((d i)⁻¹)⁻¹) = d := by funext i; rw [inv_inv]
    have heq2 : diagSU h (fun i => ((d i)⁻¹)⁻¹)
        (fun i => by rw [norm_inv_eq h, hd' i, inv_one])
        (by rw [show (∏ i, ((d i)⁻¹)⁻¹) = ∏ i, d i from
          Finset.prod_congr rfl fun i _ => inv_inv _, hdet]) = diagSU h d hd hdet := by
      apply Subtype.ext
      apply Units.ext
      simp only [coe_diagSU, hfun]
    rw [heq2] at hthis
    rw [diagSU_inv, hthis]
    exact ⟨suRadConjVec ((d 0)⁻¹) (fun i => (d i)⁻¹) m, y, _, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro A
  constructor
  · exact hmem A
  · intro hA
    have hA' := hmem' (diagSU h d hd hdet * A * (diagSU h d hd hdet)⁻¹) hA
    rwa [show (diagSU h d hd hdet)⁻¹ *
        (diagSU h d hd hdet * A * (diagSU h d hd hdet)⁻¹) * diagSU h d hd hdet = A from by
      group] at hA'


theorem eq_diagFiveLast_of_mem_centralizer (h : UnitaryFieldData 2 f K) {d : Fin 6 → K}
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (hd0 : d 0 = d 1)
    (hcent : diagSU h d hd hdet ∈
      Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 f K 6))) :
    ∃ (hc : h.norm (d 0) = 1), diagSU h d hd hdet = diagFiveLast h (d 0) hc := by
  haveI : CharP K 2 := h.charP
  obtain ⟨y1, hy1⟩ := h.traceLin_surjective
    ⟨suRadCocycle h (fun _ => (1 : K)), suRadCocycle_bar h _⟩
  have hy1' : y1 + h.bar y1 = suRadCocycle h (fun _ => (1 : K)) := by
    have := congrArg Subtype.val hy1
    simpa [UnitaryFieldData.trace] using this
  have hmem1 : unitaryRadElem h (fun _ => (1 : K)) y1 hy1' ∈ unitaryLineRadical h :=
    ⟨fun _ => 1, y1, hy1', rfl⟩
  have hcomm : diagSU h d hd hdet * unitaryRadElem h (fun _ => (1 : K)) y1 hy1' =
      unitaryRadElem h (fun _ => (1 : K)) y1 hy1' * diagSU h d hd hdet :=
    (Subgroup.mem_centralizer_iff.1 hcent _ hmem1).symm
  have hentry (i : Fin 6) (hi : i = 2 ∨ i = 3 ∨ i = 4) : d i = d 0 := by
    have hmat := congrArg
      (fun z : unitarySU 2 f K 6 =>
        ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hcomm
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    have hi1 : i ≠ 1 := by rintro rfl; simp at hi
    have h0i : ¬(0 = i) := fun hh => hi0 hh.symm
    have h1i : ¬(1 = i) := fun hh => hi1 hh.symm
    have h := congrFun (congrFun hmat 0) i
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagSU, coe_unitaryRadElem,
      unitaryRadMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
      Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, suLineVec, suRadVec,
      hi0, hi1, h0i, h1i, hi, if_true, if_false, Pi.one_apply, smul_eq_mul] at h
    norm_num at h
    exact h.symm
  have e2 : d 2 = d 0 := hentry 2 (by simp)
  have e3 : d 3 = d 0 := hentry 3 (by simp)
  have e4 : d 4 = d 0 := hentry 4 (by simp)
  have hd5 : d 5 = (d 0 ^ 5)⁻¹ := by
    have hprod : ∏ i, d i = d 0 * d 1 * d 2 * d 3 * d 4 * d 5 := Fin.prod_univ_six d
    rw [hprod, hd0.symm, e2, e3, e4] at hdet
    rw [show d 0 * d 0 * d 0 * d 0 * d 0 = d 0 ^ 5 by ring] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  refine ⟨hd 0, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [coe_diagSU, coe_diagFiveLast]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, diagFiveLastEntries, hd0, e2, e3, e4, hd5]


theorem diagFiveLast_pow (h : UnitaryFieldData 2 f K) {ζu : Kˣ} (hζ : h.norm (ζu : K) = 1)
    (n : ℕ) (hζn : h.norm (((ζu ^ n : Kˣ) : K)) = 1) :
    diagFiveLast h (((ζu ^ n : Kˣ) : K)) hζn = (diagFiveLast h (ζu : K) hζ) ^ n := by
  apply Subtype.ext
  apply Units.ext
  simp only [coe_diagFiveLast, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Matrix.diagonal_pow]
  congr 1
  funext i
  by_cases hi : i = (5 : Fin 6)
  · subst hi
    simp only [diagFiveLastEntries, if_pos, Pi.pow_apply, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, inv_pow]
    rw [← pow_mul, ← pow_mul, mul_comm]
  · simp only [diagFiveLastEntries, if_neg hi, Pi.pow_apply]

theorem inf_centralizer_unitaryLineRadical_le_zpowers (h : UnitaryFieldData 2 f K)
    {B : Subgroup (unitarySU 2 f K 6)} {ζu : Kˣ} (hζ : h.norm (ζu : K) = 1)
    (hB : ∀ A ∈ B, ∃ (d : Fin 6 → K) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
      (n : ℕ), A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ n : Kˣ) : K)) :
    B ⊓ Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 f K 6)) ≤
      Subgroup.zpowers (diagFiveLast h (ζu : K) hζ) := by
  rintro A ⟨hAB, hAC⟩
  obtain ⟨d, hd, hdet, n, rfl, hd0, hd0n⟩ := hB A hAB
  obtain ⟨hc, hEq⟩ := eq_diagFiveLast_of_mem_centralizer h hd hdet hd0 hAC
  refine Subgroup.mem_zpowers_iff.2 ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, hEq]
  simp only [hd0n]
  exact (diagFiveLast_pow h hζ n _).symm

theorem inf_unitaryBlock_centralizer_le_zpowers (h : UnitaryFieldData 2 f K)
    {B : Subgroup (unitarySU 2 f K 6)} {ζu : Kˣ} (hζ : h.norm (ζu : K) = 1)
    (hB : ∀ A ∈ B, ∃ (d : Fin 6 → K) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
      (n : ℕ), A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ n : Kˣ) : K))
    (I : Finset (Fin 6)) :
    B ⊓ unitaryBlock h I ⊓
        Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 f K 6)) ≤
      Subgroup.zpowers (diagFiveLast h (ζu : K) hζ) :=
  (inf_le_inf_right _ inf_le_left).trans (inf_centralizer_unitaryLineRadical_le_zpowers h hζ hB)

theorem map_unitaryProj_inf_centralizer_le_zpowers (h : UnitaryFieldData 2 f K)
    {B : Subgroup (unitarySU 2 f K 6)} {ζu : Kˣ} (hζ : h.norm (ζu : K) = 1)
    (hB : ∀ A ∈ B, ∃ (d : Fin 6 → K) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
      (n : ℕ), A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ n : Kˣ) : K)) :
    Subgroup.map (unitaryProj h 6)
        (B ⊓ Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 f K 6))) ≤
      Subgroup.zpowers (unitaryProj h 6 (diagFiveLast h (ζu : K) hζ)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro A hA
  exact Subgroup.mem_zpowers_iff.2
    (let ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
        (inf_centralizer_unitaryLineRadical_le_zpowers h hζ hB hA)
     ⟨k, by rw [← map_zpow, hk]⟩)


end CFSG.LocalAnalysis.GLTheoremA.Y10F
