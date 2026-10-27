module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YHBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YEEven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YERank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA TauCeti
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem valid_D4 (q : PrimePower) : (LieTypeIndex.D 4 q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.isDuplicateRepresentative_iff,
    LieTypeIndex.inStandardRange_iff]
  simp

theorem catalogIs_matrixDerived {k : Type} [Field k] [Finite k] [CharP k 2] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ m) :
    catalogIs (matrixDerived (coordinateQuadPlus 4 k)) (isD4pow2 m) := by
  let q : PrimePower := ⟨2, m, Nat.prime_two, hm⟩
  have hv := valid_D4 q
  refine ⟨CFSGIndex.lie ⟨.D 4 q, hv⟩, ⟨q, hv, rfl, rfl, rfl⟩, ?_⟩
  have hmod1 : StatedClassicalModel (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group .POmegaPlus 4 2 m :=
    (CFSG.Models.lieModel_D 4 q hv (MulEquiv.refl _)).statedClassicalModel (by decide)
  have hQne : ∃ v, coordinateQuadPlus 4 k v ≠ 0 :=
    ⟨CFSG.RankThree.PartOne.KCOrthogonalSubfield.stdU k, by
      rw [CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_stdU]
      exact one_ne_zero⟩
  let Λ := CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv (coordinateQuadPlus 4 k) hQne
  have hmod2 : StatedClassicalModel (matrixDerived (coordinateQuadPlus 4 k)) .POmegaPlus 4 2 m :=
    ⟨⟨Nat.prime_two, hm, le_refl 4⟩, k, inferInstance, inferInstance, hk,
      ⟨Λ.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 k)
        (coe_quadPlus 4 k)).symm⟩⟩
  exact CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hmod2 hmod1

theorem nonempty_equiv_om8_two {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2) :
    Nonempty (matrixDerived (coordinateQuadPlus 4 k) ≃*
      CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) := by
  have hQne : ∃ v, coordinateQuadPlus 4 k v ≠ 0 :=
    ⟨CFSG.RankThree.PartOne.KCOrthogonalSubfield.stdU k, by
      rw [CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_stdU]
      exact one_ne_zero⟩
  let Λ := CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv (coordinateQuadPlus 4 k) hQne
  exact CFSG.LocalAnalysis.GLTheoremA.D4XF.equiv_projOmegaPlus_of_statedProj hk
    (Λ.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 k)
      (coe_quadPlus 4 k)).symm)

theorem rank4_om8_two {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2) :
    ∃ E : Subgroup (matrixDerived (coordinateQuadPlus 4 k)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := by
  obtain ⟨e⟩ := nonempty_equiv_om8_two hk
  obtain ⟨D, hD, hDc⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_e81_of_three_lt_pRank
    CFSG.RankThree.PartTwo.Sec4.Census.three_lt_pRank_omegaPlus
  refine ⟨D.map e.symm.toMonoidHom, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map _ hD, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hDc]
  norm_num

theorem rank3_om8_two {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2) :
    ∃ E W : Subgroup (matrixDerived (coordinateQuadPlus 4 k)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧ E ≤ Subgroup.normalizer (W : Set _) := by
  obtain ⟨e⟩ := nonempty_equiv_om8_two hk
  haveI : Finite (CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, W, hE, hEc, hW2, hWne, hEW⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.D4XF.exists_E27_of_three_le_twoLocalPrimeRank
      (G := CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1))
      CFSG.RankThree.PartTwo.Sec4.Census.localRank_omega8PlusTwo
  refine ⟨E.map e.symm.toMonoidHom, W.map e.symm.toMonoidHom,
    CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map _ hE, ?_, hW2.map _,
    fun h => hWne ((Subgroup.map_eq_bot_iff_of_injective W e.symm.injective).1 h), ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEc]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.le_normalizer_map e.symm.toMonoidHom (Subgroup.mem_map_of_mem _ (hEW hy))

end CFSG.LocalAnalysis.GLTheoremA.D4Y
