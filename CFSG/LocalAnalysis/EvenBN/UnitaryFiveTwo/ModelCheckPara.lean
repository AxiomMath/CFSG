module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckLevi
public import CFSG.RankThree.PartOne.U5K.Hyp.Lam

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

@[expose] noncomputable def toGam (g : hypSU hF4 2 1) : CFSG.RankThree.PartOne.U5K.Hyp.Gam hF4 :=
  ⟨SemidirectProduct.inl (g : GL (HypIndex 2 1) F4), 1, one_ne_zero, map_one _, by
    rw [one_smul, SemidirectProduct.left_inl]
    exact (mem_hypSU.1 g.2).1⟩

theorem act_toGam (g v : hypSU hF4 2 1) :
    CFSG.RankThree.PartOne.U5K.Hyp.act hF4 (toGam g) v = g * v * g⁻¹ := by
  apply Subtype.ext
  change (SemidirectProduct.inl (g : GL (HypIndex 2 1) F4)).left *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut
        (SemidirectProduct.inl (g : GL (HypIndex 2 1) F4)).right (v : GL (HypIndex 2 1) F4) *
      (SemidirectProduct.inl (g : GL (HypIndex 2 1) F4)).left⁻¹ = _
  rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply]
  rfl

theorem exists_lev_inv_mul_mem_Ssub {g : hypSU hF4 2 1}
    (hg : ∀ v ∈ CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4,
      g * v * g⁻¹ ∈ CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4) :
    ∃ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det),
      (CFSG.RankThree.PartOne.U5K.Hyp.lev (hK := hF4) A hA)⁻¹ * g ∈
        CFSG.RankThree.PartOne.U5K.Hyp.Ssub hF4 := by
  have hW := CFSG.RankThree.PartOne.U5K.Hyp.isParaW_of_act_mem (x := toGam g) fun v hv => by
    rw [act_toGam]
    exact hg v hv
  have hdet0 := CFSG.RankThree.PartOne.U5K.Hyp.det_blkEE_ne_zero hW
  have hP := CFSG.RankThree.PartOne.U5K.Hyp.isPara_of_paraW hW
  set M : Matrix (HypIndex 2 1) (HypIndex 2 1) F4 := CFSG.RankThree.PartOne.U5K.Hyp.mat g with hMdef
  have hMl : CFSG.RankThree.PartOne.U5K.Hyp.lmat (toGam g) = M := rfl
  rw [hMl] at hP
  have hM := CFSG.RankThree.PartOne.U5K.Hyp.eq_blk3_of_para hP
  set A := blkA M with hAdef
  have hdetA : A.det ≠ 0 := hdet0
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hdetA
  refine ⟨A, hA, ?_⟩
  have hU : (M.map hF4.bar)ᵀ * hypGram 2 1 F4 * M = hypGram 2 1 F4 := (mem_hypSU.1 g.2).1
  rw [hM] at hU
  obtain ⟨u1, -, -, -⟩ := (blk3_gram_iff hF4 _ _ _ _ _ _).1 hU
  have hD : blkD M = barInvT hF4 A := by
    have h1 := conjTranspose_mul_barInvT (h := hF4) hA
    have hu : IsUnit ((A.map hF4.bar)ᵀ).det := by
      rw [det_conjTranspose']
      exact hA.map hF4.bar
    calc blkD M = ((A.map hF4.bar)ᵀ)⁻¹ * ((A.map hF4.bar)ᵀ * blkD M) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = ((A.map hF4.bar)ᵀ)⁻¹ * ((A.map hF4.bar)ᵀ * barInvT hF4 A) := by rw [u1, h1]
      _ = barInvT hF4 A := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  set dA := hF4.bar A.det / A.det with hdA
  have hdetM : M.det = 1 := (mem_hypSU.1 g.2).2
  rw [hM, det_blk3, hD, det_barInvT hA, Matrix.det_fin_one (blkP M)] at hdetM
  have hbar0 : hF4.bar A.det ≠ 0 := (hA.map hF4.bar).ne_zero
  have hm : blkP M 0 0 = dA := by
    rw [hdA, eq_div_iff hdetA]
    field_simp at hdetM
    linear_combination hdetM
  have hd0 : dA ≠ 0 := div_ne_zero hbar0 hdetA
  have hlevinv : CFSG.RankThree.PartOne.U5K.Hyp.mat
      (CFSG.RankThree.PartOne.U5K.Hyp.lev (hK := hF4) A hA)⁻¹ =
      CFSG.ClassicalGroups.UnitaryFlag.oddDiag hF4 A⁻¹ dA⁻¹ := by
    refine CFSG.RankThree.PartOne.U5K.Hyp.mat_inv_eq ?_
    rw [CFSG.RankThree.PartOne.U5K.Hyp.mat_lev, ← hdA,
      CFSG.RankThree.PartOne.U5K.Hyp.oddDiag_mul, Matrix.nonsing_inv_mul _ hA,
      inv_mul_cancel₀ hd0, CFSG.RankThree.PartOne.U5K.Hyp.oddDiag_one]
  set s := (CFSG.RankThree.PartOne.U5K.Hyp.lev (hK := hF4) A hA)⁻¹ * g with hs
  have hsM : CFSG.RankThree.PartOne.U5K.Hyp.mat s = blk3 1 (A⁻¹ * blkX M) (A⁻¹ * blkY M) 1
      ((Matrix.of fun _ _ => dA⁻¹ : Matrix (Fin 1) (Fin 1) F4) * blkQ M) 1 := by
    rw [hs, CFSG.RankThree.PartOne.U5K.Hyp.mat_mul, hlevinv, ← hMdef, hM,
      CFSG.ClassicalGroups.UnitaryFlag.oddDiag, blk3_mul, hD, ← barInvT_mul,
      Matrix.nonsing_inv_mul _ hA]
    congr 1
    · simp only [Matrix.zero_mul, add_zero]
      rfl
    · simp only [Matrix.zero_mul, add_zero]
      rfl
    · ext k l
      fin_cases k
      fin_cases l
      simp [Matrix.mul_apply, hm, inv_mul_cancel₀ hd0]
    · simp only [Matrix.zero_mul, add_zero]
      rfl
    · rw [barInvT_eq (by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
        Matrix.one_mul])]
  have hUs : ((CFSG.RankThree.PartOne.U5K.Hyp.mat s).map hF4.bar)ᵀ * hypGram 2 1 F4 *
      CFSG.RankThree.PartOne.U5K.Hyp.mat s = hypGram 2 1 F4 := (mem_hypSU.1 s.2).1
  rw [hsM] at hUs
  obtain ⟨-, -, u3, -⟩ := (blk3_gram_iff hF4 _ _ _ _ _ _).1 hUs
  refine CFSG.RankThree.PartOne.U5K.Hyp.mem_Ssub_of_mat (x := fun i => (A⁻¹ * blkX M) i 0)
    (C := A⁻¹ * blkY M) ?_
  rw [hsM, CFSG.ClassicalGroups.UnitaryFlag.oddUni]
  congr 1
  · ext i l
    fin_cases l
    rfl
  · ext k j
    obtain rfl : k = 0 := Subsingleton.elim _ _
    have := congrFun (congrFun u3 0) j
    simp only [Matrix.add_apply, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.zero_apply, Matrix.transpose_one, Matrix.map_one, map_zero,
      map_one] at this
    simp only [Matrix.replicateRow_apply]
    linear_combination this

theorem exists_eq_levSU_mul_of_normalizer {n : SU52} (hn : n ∈ normalizer (Fsub : Set SU52)) :
    ∃ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∃ a ∈ A₂sub, n = levSU A hA * a := by
  have hg : ∀ v ∈ CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4,
      ρ n * v * (ρ n)⁻¹ ∈ CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4 := by
    intro v hv
    have hv' : ρ.symm v ∈ Fsub := by
      rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      exact hv
    have := (mem_normalizer_iff.1 hn _).1 hv'
    rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨A, hA, hs⟩ := exists_lev_inv_mul_mem_Ssub hg
  refine ⟨A, hA, ρ.symm ((CFSG.RankThree.PartOne.U5K.Hyp.lev (hK := hF4) A hA)⁻¹ * ρ n), ?_, ?_⟩
  · rw [mem_A₂sub_iff_ρ, MulEquiv.apply_symm_apply]
    exact hs
  · rw [map_mul, map_inv, MulEquiv.symm_apply_apply, levSU, mul_inv_cancel_left]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
