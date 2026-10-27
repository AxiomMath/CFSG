module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply polar_quadMinus)

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem PEl.radHyp {g : GL6 F} (hg : PEl b c g) (ht : tc g = 0) (hr : rho g = 1) :
    RadHyp b c g := by
  have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
  refine ⟨hg.iso, fun i => ?_, fun x i => ?_, fun z hz j => ?_⟩
  · rcases hi i with rfl | rfl
    · exact hg.fix0
    · rw [hg.shift, ht, zero_smul, add_zero]
  · rcases hi i with rfl | rfl
    · rw [Pi.sub_apply, hg.y0, sub_self]
    · rw [Pi.sub_apply, hg.y1, ht, zero_mul, add_zero, sub_self]
  · rw [Pi.sub_apply, hg.coordN, hz idx0, hz idx1, hr]
    fin_cases j <;> simp [Matrix.one_apply]

theorem ell_formula (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : F) :
    ∃ A ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OW F,
      gv A x = x + (t * x (Sum.inr (Sum.inl idx0))) • fV F idx1 +
        (t * x (Sum.inl idx1)) • eV F idx0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨A, hA, hAx⟩ := eichler_mem_statedOmega hirr (eV F idx0) (t • fV F idx1)
  refine ⟨A, hA, fun x => ?_⟩
  have hu : quadMinus 3 F b c (eV F idx0) = 0 := quad_eV idx0
  have hw : polar (quadMinus 3 F b c) (eV F idx0) (t • fV F idx1) = 0 := by
    rw [polar_smul_right_eq, polar_f_right]
    simp [eV_ne (i := idx0) (k := idx1) (by decide)]
  show (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x = _
  rw [hAx, eichler_apply hu hw, polar_e_right, polar_smul_right_eq, polar_f_right,
    map_smul_eq_sq, quadMinus_single_inr idx1, mul_zero, zero_mul, add_zero, smul_smul,
    sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

theorem ell_pel (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : F) :
    ∃ A ∈ StatedOmega (StatedQuadMinus 3 F b c), PEl b c A ∧ tc A = t ∧ rho A = 1 := by
  obtain ⟨A, hA, hAx⟩ := ell_formula (b := b) (c := c) hirr t
  have hne01 : idx0 ≠ idx1 := by decide
  have hne10 : idx1 ≠ idx0 := by decide
  have h0 : gv A (eV F idx0) = eV F idx0 := by
    rw [hAx]
    simp [eV_inr, eV_ne (i := idx0) (k := idx1) hne10]
  have h1 : gv A (eV F idx1) = eV F idx1 + t • eV F idx0 := by
    rw [hAx]
    simp [eV_inr, eV_self, eV_ne (i := idx1) (k := idx0) hne01]
  have hel : PEl b c A := PEl.mk' (fun v => quadMinus_mulVec_of_mem_statedOmega hA v) h0 h1
  refine ⟨A, hA, hel, ?_, ?_⟩
  · have := congrFun h1 (Sum.inl idx0)
    simpa [tc, eV_ne (i := idx1) (k := idx0) hne01, eV_self] using this
  · ext k j
    rw [rho_apply, hAx]
    simp [nVec, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem PEl.mem_omega_of_rho (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {g : GL6 F}
    (hg : PEl b c g) (hr : rho g = 1) : g ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨A, hA, hAp, hAt, hAr⟩ := ell_pel (b := b) (c := c) hirr (tc g)
  have hh : PEl b c (A * g) := hAp.mul hg
  have hht : tc (A * g) = 0 := by
    rw [tc_mul_eq hAp hg, hAt]
    linear_combination tc g * h2
  have hhr : rho (A * g) = 1 := by rw [rho_mul hAp hg, hAr, hr, mul_one]
  have hrad := rad_mem_omega hirr (hh.radHyp hht hhr)
  have : g = A⁻¹ * (A * g) := by group
  rw [this]
  exact mul_mem (inv_mem hA) hrad

theorem PEl.comm_aux {g a : GL6 F} (hg : PEl b c g) (ha : PEl b c a) (hcomm : g * a = a * g)
    (j : Fin (3 - 1)) (k : Fin 2) :
    rho g k 0 * mcol a j 0 + rho g k 1 * mcol a j 1 +
      (mcol g idx0 k * fV F j (Sum.inr (Sum.inl idx0)) +
        mcol g idx1 k * (fV F j (Sum.inr (Sum.inl idx1)) + tc a * fV F j (Sum.inr (Sum.inl idx0)))) =
    rho a k 0 * mcol g j 0 + rho a k 1 * mcol g j 1 +
      (mcol a idx0 k * fV F j (Sum.inr (Sum.inl idx0)) +
        mcol a idx1 k * (fV F j (Sum.inr (Sum.inl idx1)) + tc g * fV F j (Sum.inr (Sum.inl idx0)))) := by
  have key : gv g (gv a (fV F j)) (Sum.inr (Sum.inr k)) =
      gv a (gv g (fV F j)) (Sum.inr (Sum.inr k)) := by
    rw [← gv_mul, ← gv_mul, hcomm]
  have hL : gv g (gv a (fV F j)) (Sum.inr (Sum.inr k)) =
      rho g k 0 * mcol a j 0 + rho g k 1 * mcol a j 1 +
      (mcol g idx0 k * fV F j (Sum.inr (Sum.inl idx0)) +
        mcol g idx1 k * (fV F j (Sum.inr (Sum.inl idx1)) + tc a * fV F j (Sum.inr (Sum.inl idx0)))) := by
    rw [hg.coordN (gv a (fV F j)) k, ha.y0 (fV F j), ha.y1 (fV F j)]
    rfl
  have hR : gv a (gv g (fV F j)) (Sum.inr (Sum.inr k)) =
      rho a k 0 * mcol g j 0 + rho a k 1 * mcol g j 1 +
      (mcol a idx0 k * fV F j (Sum.inr (Sum.inl idx0)) +
        mcol a idx1 k * (fV F j (Sum.inr (Sum.inl idx1)) + tc g * fV F j (Sum.inr (Sum.inl idx0)))) := by
    rw [ha.coordN (gv g (fV F j)) k, hg.y0 (fV F j), hg.y1 (fV F j)]
    rfl
  rw [hL, hR] at key
  exact key

theorem PEl.comm_constraint {g a : GL6 F} (hg : PEl b c g) (ha : PEl b c a) (hg0 : tc g = 0)
    (hg1 : rho g = 1) (hcomm : g * a = a * g) (k : Fin 2) :
    rho a k 0 * mcol g idx0 0 + rho a k 1 * mcol g idx0 1 = mcol g idx0 k + tc a * mcol g idx1 k ∧
      rho a k 0 * mcol g idx1 0 + rho a k 1 * mcol g idx1 1 = mcol g idx1 k := by
  have hne01 : idx0 ≠ idx1 := by decide
  have hne10 : idx1 ≠ idx0 := by decide
  have hf00 : fV F idx0 (Sum.inr (Sum.inl idx0)) = 1 := fV_self idx0
  have hf01 : fV F idx0 (Sum.inr (Sum.inl idx1)) = 0 := fV_ne hne10
  have hf10 : fV F idx1 (Sum.inr (Sum.inl idx0)) = 0 := fV_ne hne01
  have hf11 : fV F idx1 (Sum.inr (Sum.inl idx1)) = 1 := fV_self idx1
  have h0 := PEl.comm_aux hg ha hcomm idx0 k
  have h1 := PEl.comm_aux hg ha hcomm idx1 k
  rw [hf00, hf01, hg0] at h0
  rw [hf10, hf11, hg0] at h1
  have r00 : rho g 0 0 = 1 := by rw [hg1, Matrix.one_apply_eq]
  have r11 : rho g 1 1 = 1 := by rw [hg1, Matrix.one_apply_eq]
  have r01 : rho g 0 1 = 0 := by rw [hg1, Matrix.one_apply_ne (by decide)]
  have r10 : rho g 1 0 = 0 := by rw [hg1, Matrix.one_apply_ne (by decide)]
  have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases hk k with rfl | rfl
  · rw [r00, r01] at h0 h1
    exact ⟨by linear_combination -h0, by linear_combination -h1⟩
  · rw [r10, r11] at h0 h1
    exact ⟨by linear_combination -h0, by linear_combination -h1⟩

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
