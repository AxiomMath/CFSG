module

public import CFSG.ClassicalInvolution.Phan.PhanS12Close
public import CFSG.ClassicalInvolution.Phan.PhanS11Col

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

section Alg

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem actK_comb_pi0 {g : spinGroup (quadOdd 3 F)} {M : Matrix (Fin 3) (Fin 3) K}
    (h0 : actK g (vXi D) = M 0 0 • vXi D + M 1 0 • vE2 D + M 2 0 • vE3 D)
    (h1 : actK g (vE2 D) = M 0 1 • vXi D + M 1 1 • vE2 D + M 2 1 • vE3 D)
    (h2 : actK g (vE3 D) = M 0 2 • vXi D + M 1 2 • vE2 D + M 2 2 • vE3 D) (a b c : K) :
    actK g (a • vXi D + b • vE2 D + c • vE3 D) =
      (M 0 0 * a + M 0 1 * b + M 0 2 * c) • vXi D + (M 1 0 * a + M 1 1 * b + M 1 2 * c) • vE2 D +
        (M 2 0 * a + M 2 1 * b + M 2 2 * c) • vE3 D := by
  rw [map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2]
  module

theorem PiDetOne.one : PiDetOne D (1 : spinGroup (quadOdd 3 F)) := by
  refine ⟨1, Matrix.det_one, ?_, ?_, ?_⟩ <;> simp [actK_one]

theorem PiDetOne.mul {g h : spinGroup (quadOdd 3 F)} (hg : PiDetOne D g) (hh : PiDetOne D h) :
    PiDetOne D (g * h) := by
  obtain ⟨Mg, hdg, g0, g1, g2⟩ := hg
  obtain ⟨Mh, hdh, h0, h1, h2⟩ := hh
  refine ⟨Mg * Mh, by rw [Matrix.det_mul, hdg, hdh, one_mul], ?_, ?_, ?_⟩
  · rw [actK_mul, h0, actK_comb_pi0 D g0 g1 g2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [actK_mul, h1, actK_comb_pi0 D g0 g1 g2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [actK_mul, h2, actK_comb_pi0 D g0 g1 g2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]

theorem PiDetOne.inv {g : spinGroup (quadOdd 3 F)} (hg : PiDetOne D g) : PiDetOne D g⁻¹ := by
  obtain ⟨M, hdet, h0, h1, h2⟩ := hg
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (by rw [hdet]; exact isUnit_one)
  have hd : ∀ i : Fin 3, M i 0 * M⁻¹ 0 i + M i 1 * M⁻¹ 1 i + M i 2 * M⁻¹ 2 i = 1 := fun i => by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hMN i) i
  have ho : ∀ i k : Fin 3, i ≠ k →
      M i 0 * M⁻¹ 0 k + M i 1 * M⁻¹ 1 k + M i 2 * M⁻¹ 2 k = 0 := fun i k hik => by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_ne hik] using
      congrFun (congrFun hMN i) k
  have e0 : vXi D = M 0 0 • actK g⁻¹ (vXi D) + M 1 0 • actK g⁻¹ (vE2 D) +
      M 2 0 • actK g⁻¹ (vE3 D) := by
    have := congrArg (actK (K := K) g⁻¹) h0
    rwa [actK_inv_actK, map_add, map_add, map_smul, map_smul, map_smul] at this
  have e1 : vE2 D = M 0 1 • actK g⁻¹ (vXi D) + M 1 1 • actK g⁻¹ (vE2 D) +
      M 2 1 • actK g⁻¹ (vE3 D) := by
    have := congrArg (actK (K := K) g⁻¹) h1
    rwa [actK_inv_actK, map_add, map_add, map_smul, map_smul, map_smul] at this
  have e2 : vE3 D = M 0 2 • actK g⁻¹ (vXi D) + M 1 2 • actK g⁻¹ (vE2 D) +
      M 2 2 • actK g⁻¹ (vE3 D) := by
    have := congrArg (actK (K := K) g⁻¹) h2
    rwa [actK_inv_actK, map_add, map_add, map_smul, map_smul, map_smul] at this
  refine ⟨M⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv, hdet]
    simp
  all_goals generalize actK g⁻¹ (vXi D) = c0 at e0 e1 e2 ⊢
  all_goals generalize actK g⁻¹ (vE2 D) = c1 at e0 e1 e2 ⊢
  all_goals generalize actK g⁻¹ (vE3 D) = c2 at e0 e1 e2 ⊢
  · rw [e0, e1, e2]
    match_scalars
    · linear_combination (-1 : K) * hd 0
    · linear_combination (-1 : K) * ho 1 0 (by decide)
    · linear_combination (-1 : K) * ho 2 0 (by decide)
  · rw [e0, e1, e2]
    match_scalars
    · linear_combination (-1 : K) * hd 1
    · linear_combination (-1 : K) * ho 0 1 (by decide)
    · linear_combination (-1 : K) * ho 2 1 (by decide)
  · rw [e0, e1, e2]
    match_scalars
    · linear_combination (-1 : K) * hd 2
    · linear_combination (-1 : K) * ho 0 2 (by decide)
    · linear_combination (-1 : K) * ho 1 2 (by decide)

def piDetOneSubgroup : Subgroup (spinGroup (quadOdd 3 F)) where
  carrier := {g | PiDetOne D g}
  one_mem' := PiDetOne.one D
  mul_mem' := fun hg hh => PiDetOne.mul D hg hh
  inv_mem' := fun hg => PiDetOne.inv D hg

theorem mem_piDetOneSubgroup {g : spinGroup (quadOdd 3 F)} :
    g ∈ piDetOneSubgroup D ↔ PiDetOne D g := Iff.rfl

end Alg

end CFSG.ClassicalInvolution.PhanB3.S
