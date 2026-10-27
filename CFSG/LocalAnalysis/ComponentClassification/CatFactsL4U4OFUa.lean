module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem cP_one (P : GL (Fin 4) K) : cP P (1 : unitarySU p f K 4) = 1 := by
  rw [cP, OneMemClass.coe_one, Units.val_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]

include h in
theorem isBD_of_mem_C (hp2 : p ≠ 2) (P : GL (Fin 4) K) {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K}
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) {g : unitarySU p f K 4}
    (hg : g ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) : IsBD (cP P g) :=
  isBD_of_comm_X1 (two_ne_zero_of_odd h hp2) hl0 ((CSU.mem_C_iff P hAP g).1 hg)

include h in
theorem det_ul_eq_one (hp2 : p ≠ 2) (P : GL (Fin 4) K) {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K}
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) {Z : unitarySU p f K 4}
    (hZ : Z ∈ ⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆) :
    (ul (cP P Z)).det = 1 := by
  set C := (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype with hC
  have hmul : ∀ g ∈ C, ∀ g' ∈ C,
      (ul (cP P (g * g'))).det = (ul (cP P g)).det * (ul (cP P g')).det := by
    intro g hg g' hg'
    rw [cP_mul, ul_mul (isBD_of_mem_C h hp2 P hl0 hAP hg) (isBD_of_mem_C h hp2 P hl0 hAP hg'),
      Matrix.det_mul]
  have hinv : ∀ g ∈ C, (ul (cP P g)).det * (ul (cP P g⁻¹)).det = 1 := by
    intro g hg
    rw [← hmul g hg g⁻¹ (inv_mem hg), mul_inv_cancel, cP_one, ul_one, Matrix.det_one]
  let S : Subgroup (unitarySU p f K 4) :=
    { carrier := {g | g ∈ C ∧ (ul (cP P g)).det = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [hmul a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, by rw [cP_one, ul_one, Matrix.det_one]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hinv a ha.1
        rwa [ha.2, one_mul] at this⟩ }
  have hle : ⁅C, C⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    rw [commutatorElement_def, hmul _ (mul_mem (mul_mem hx hy) (inv_mem hx)) _ (inv_mem hy),
      hmul _ (mul_mem hx hy) _ (inv_mem hx), hmul _ hx _ hy]
    have h1 := hinv x hx
    have h2 := hinv y hy
    linear_combination (ul (cP P y)).det * (ul (cP P y⁻¹)).det * h1 + h2
  exact (hle hZ).2

theorem ul_smul_one (c : K) : ul (c • (1 : Matrix (Fin 4) (Fin 4) K)) = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul]

include h in
theorem mul_self_eq_neg_one_U (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {Z : unitarySU p f K 4}
    (hZ : Z ∈ ⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆)
    (hZ1 : thU p f K Z ≠ 1) (hZ2 : thU p f K Z ^ 2 = 1) :
    ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Z : GL (Fin 4) K) = -1 := by
  have hZC : Z ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype :=
    (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
      ⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
        (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆ ≤
        (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) hZ
  have hBD := isBD_of_mem_C h hp2 P hl0 hAP hZC
  have hdet := det_ul_eq_one h hp2 P hl0 hAP hZ
  have hZs : Z * Z ∈ scal p f K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    change thU p f K Z * thU p f K Z = 1
    rw [← sq, hZ2]
  obtain ⟨c, hc⟩ := val_of_mem_scal hZs
  have hcP : cP P Z * cP P Z = (c : K) • 1 := by
    rw [← cP_mul, cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hul : ul (cP P Z) * ul (cP P Z) = (c : K) • 1 := by
    rw [← ul_mul hBD hBD, hcP, ul_smul_one]
  have hU := unitary_cP h P hP Z
  rcases OFL.eq_neg_one_or_eq_one_or hdet hul with h1 | h1 | h1
  · have e : ((Z * Z : unitarySU p f K 4) : GL (Fin 4) K) =
        ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Z : GL (Fin 4) K) := rfl
    rw [← e, hc, h1, neg_one_smul]
  all_goals exfalso
  all_goals apply hZ1
  all_goals rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · have hM := eq_one_of_ul_eq_one h hBD hU h1
    have : Z = 1 := eq_of_cP_eq P (by rw [hM, cP_one])
    rw [this]
    exact one_mem _
  · have hBD' : IsBD (-cP P Z) := by
      obtain ⟨m02, m03, m12, m13, m20, m21, m30, m31⟩ := hBD
      exact ⟨by simp [m02], by simp [m03], by simp [m12], by simp [m13], by simp [m20],
        by simp [m21], by simp [m30], by simp [m31]⟩
    have hU' : uStar h (-cP P Z) * stdG * (-cP P Z) = stdG := by
      rw [uStar, Matrix.map_neg _ (map_neg h.bar), Matrix.transpose_neg, Matrix.neg_mul,
        Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      exact hU
    have hul' : ul (-cP P Z) = 1 := by
      have e : ul (-cP P Z) = -ul (cP P Z) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ul]
      rw [e, h1, neg_neg]
    have hM := eq_one_of_ul_eq_one h hBD' hU' hul'
    have hZm : ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
      rw [val_eq_cP P Z, ← neg_neg (cP P Z), hM]
      rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    refine ⟨-1, Units.ext ?_⟩
    change Matrix.scalar (Fin 4) ((-1 : Kˣ) : K) = ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [hZm, Units.val_neg, Units.val_one, map_neg, map_one]

@[expose] noncomputable def dU (r : K) : Matrix (Fin 4) (Fin 4) K :=
  !![r, 0, 0, 0; 0, 1, 0, 0; 0, 0, (h.bar r)⁻¹, 0; 0, 0, 0, 1]

theorem unitary_dU {r : K} (hr : r ≠ 0) : uStar h (dU h r) * stdG * dU h r = stdG := by
  have hb : h.bar r ≠ 0 := (h.bar_eq_zero_iff).not.mpr hr
  have hbb : h.bar (h.bar r)⁻¹ = r⁻¹ := by rw [map_inv₀, h.bar_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dU, uStar, stdG, Matrix.mul_apply, Fin.sum_univ_four, hbb, hr, hb]

theorem det_dU (r : K) : (dU h r).det = r / h.bar r := by
  rw [Matrix.det_succ_row_zero]
  simp [dU, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem dU_comm_X1 (r l : K) : dU h r * X1 l = X1 l * dU h r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dU, X1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end OFU

end CFSG.ComponentClassification.CatFactsL4U4
