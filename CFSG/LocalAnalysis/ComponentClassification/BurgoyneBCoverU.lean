module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputsU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem burgoynePropBSU4CoverInput : BurgoynePropBSU4CoverInput := by
  intro p f F _ h hp2 L _ _ α hα c hc g hg
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hF : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  have hG : IsQuasisimple (StatedSU 4 (p ^ f) F) :=
    U.isQuasisimple_statedSU_of_two_le hp2 h.card_eq_sq (by norm_num) (Or.inl (by norm_num))
  set M : StatedSU 4 (p ^ f) F →* Matrix (Fin 4) (Fin 4) F :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) F)).comp (StatedSU 4 (p ^ f) F).subtype with hMdef
  have hMx : ∀ x : StatedSU 4 (p ^ f) F,
      M x = ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun x => rfl
  have hM : Function.Injective M := fun x y hxy =>
    Subtype.ext (Units.ext (by rw [← hMx, ← hMx, hxy]))
  have hZs : ∀ z ∈ center (StatedSU 4 (p ^ f) F), ∃ r : F, r ^ 4 = 1 ∧ M z = r • 1 := by
    intro z hz
    have hcz : ∀ g' ∈ U.uBlock p f F (Finset.univ : Finset (Fin 4)), M z * ((g' : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) = ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M z := by
      intro g' _
      have hgz := mem_center_iff.1 hz g'
      rw [← hMx g']
      calc M z * M g' = M (z * g') := (map_mul M z g').symm
        _ = M (g' * z) := by rw [hgz]
        _ = M g' * M z := map_mul M g' z
    obtain ⟨hoff, hdiag⟩ := U.eq_of_commute_uBlock h (I := Finset.univ) (by simp) hcz
    refine ⟨M z 0 0, ?_, ?_⟩
    · have hzr : M z = M z 0 0 • 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
          exact hdiag i (Finset.mem_univ _) 0 (Finset.mem_univ _)
        · rw [(hoff i (Finset.mem_univ _) j (Ne.symm hij)).1, Matrix.smul_apply, one_apply_ne hij,
            smul_zero]
      have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
      rw [← hMx, hzr, det_smul, det_one, mul_one, Fintype.card_fin] at hdet
      exact hdet
    · ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        exact hdiag i (Finset.mem_univ _) 0 (Finset.mem_univ _)
      · rw [(hoff i (Finset.mem_univ _) j (Ne.symm hij)).1, Matrix.smul_apply, one_apply_ne hij,
          smul_zero]
  have hgc : g ∈ center (StatedSU 4 (p ^ f) F) := by
    rw [mem_center_iff]
    intro x
    apply hM
    rw [map_mul, map_mul, hMx g, hg, neg_one_mul, mul_neg_one]
  obtain ⟨hg2, hZ, hZ1⟩ := center_hyps_of_scalar hF M hM (g := g) (by rw [hMx, hg]) hZs
  exact eq_of_propBHypII hG hgc hg2 hZ hZ1 α hα hc

end CFSG.ComponentClassification.Burgoyne.B
