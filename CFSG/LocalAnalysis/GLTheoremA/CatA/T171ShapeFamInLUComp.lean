module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescProof
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary
open Polynomial

variable {N n : ℕ} {K : Type} [Field K] [Finite K]

theorem projConj_recipe (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) :
    MulAut.congr (CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K).symm
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) = conjAut N K D := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective N K x
  rw [MulAut.congr_apply]
  simp only [MulEquiv.symm_symm, MulEquiv.trans_apply]
  rw [CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv_proj, TableB.projConj_mk]
  rw [show ((LargeEvenSLGroup (Fin N) K).normalizerMonoidHom ⟨D, hD⟩)
      (CFSG.LocalAnalysis.GLTheoremA.I2015.slEquivLargeEven N K g) =
      CFSG.LocalAnalysis.GLTheoremA.I2015.slEquivLargeEven N K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K D g) by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
      CFSG.LocalAnalysis.GLTheoremA.I2015.slEquivLargeEven_coe,
      CFSG.LocalAnalysis.GLTheoremA.I2015.slEquivLargeEven_coe,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]]
  rw [← CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv_proj, MulEquiv.symm_apply_apply,
    conjAut_proj]

theorem specialFactor_of_component
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hS : Setup p L J A d b) (hn : Nat.card K = 2 ^ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hDp : D ^ p = 1)
    (hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) :
    ∃ h : {h : primaryFactors (glA D : Module.End K (Fin N → K)) // IsGoodFactor D h},
      ((J.subgroupOf L).map (piCenterQuot θ)).map
          (CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K).symm.toMonoidHom =
        (specialFactor D h.1.1).map (proj N K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hn)
  haveI := hchar
  have hpk : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro hdvd
    have h2p : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hS.prime).1 hdvd).symm
    exact hS.odd h2p
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
  have hcomp := componentDescent_holds G L hS.qs
    (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) θ d hdN
    (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) hDind J hJc
    ((CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).trans hS.comp.2)
  set e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K with he
  have hφ : MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) =
      conjAut N K D := projConj_recipe D hD
  have hfix : (fixedSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)).map
        e.symm.toMonoidHom = fixedSubgroup (conjAut N K D) := by
    rw [← hφ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩ y = y := hy
      change (MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
        (e.symm y) = e.symm y
      simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply]
      rw [hy']
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      have hx' : (MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
          x = x := hx
      change TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩ (e x) = e x
      simpa only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply] using congrArg e hx'
  have hmap : ((J.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom =
      (J.subgroupOf L).map (e.symm.toMonoidHom.comp (piCenterQuot θ)) := by
    rw [Subgroup.map_map]
  have hK : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (e.symm.toMonoidHom.comp (piCenterQuot θ)))
      (fixedSubgroup (conjAut N K D)) := by
    rw [← hmap, ← hfix]
    exact CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e.symm
      ((CFSG.Assembly.isComponentOf_iff_open).1 hcomp.1)
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by
    simpa using hDp
  obtain ⟨h, hh⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
    (p := p) hpk hDp' _ hK
  rw [Subgroup.map_map]
  exact ⟨h, hh⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
