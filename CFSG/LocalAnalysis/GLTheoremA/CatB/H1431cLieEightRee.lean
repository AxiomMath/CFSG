module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightUni
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LieType.Ree.LargeReeCenterTrivial
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LieType.Ree
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

section Ree


theorem lieSEightNoAt_reeF4 (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => ∃ m, d = .reeF4 m := by
  rintro Y _ _ hY - - ⟨d, hv⟩ ⟨m, rfl⟩ - - ⟨e⟩ α hα hα3 hα1 ⟨J, hJ, hT⟩
  have hm : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hKf, hKfin, hKchar, hK, ⟨e'⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm hR
  let θ : Y ⧸ Subgroup.center Y ≃* ReeTag.F4.reeGamma K m := e.trans e'
  have hinn : innAutDerived ↥(ReeTag.F4.reeGamma K m) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(ReeTag.F4.reeGamma K m) :=
    KD264Lie.innAutDerived_le_inner_excTw_of_mulEquiv e'
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_innAutDerived_le_inner hR)
  have hβ : MulAut.congr θ α ∈ innAutDerived ↥(ReeTag.F4.reeGamma K m) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hα
  have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr θ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr θ).injective (h.trans (map_one _).symm))
  obtain ⟨y, hy, hyp, hy1⟩ := exists_eq_conj_of_mem_range
    (ReeTag.large_Ree_fixed_group_center_trivial m K hK) (hinn hβ) hβ3 hβ1
  have hy3 : orderOf y = 3 := orderOf_eq_prime hyp hy1
  haveI : Finite ↥(ReeTag.F4.reeGamma K m) := Subtype.finite
  have hJ' : GLAPComponent 3 (fixSub (MulAut.conj y)) (J.map θ.toMonoidHom) := by
    rw [← hy]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport θ α hJ
  obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU m K
    hK y hy3
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * m + 1))) = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  haveI : Fintype (GaloisField 2 (2 * (2 * m + 1))) := Fintype.ofFinite _
  have hFfcard : Fintype.card (GaloisField 2 (2 * (2 * m + 1))) = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * m + 1))) (f := 2 * m + 1) hFcard (by omega)).1
  let E : ↥(fixSub (MulAut.conj y)) ≃*
      ↥(StatedSU 3 (2 ^ (2 * m + 1)) (GaloisField 2 (2 * (2 * m + 1)))) :=
    (MulEquiv.subgroupCongr (fixSubgroup_conj y)).trans eC
  have hmq : ((3 : ℕ), 2 ^ (2 * m + 1)) ≠ ((3 : ℕ), 2) := by
    intro h
    have h2 : 2 ^ (2 * m + 1) = 2 := (Prod.mk.inj h).2
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hCq : CFSG.IsQuasisimple ↥(fixSub (MulAut.conj y)) := CFSG.IsQuasisimple.of_mulEquiv E hq
  have hCqO : CFSG.Open.IsQuasisimple ↥(fixSub (MulAut.conj y)) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).1 hCq
  have hXcomp : CFSG.Open.IsComponentOf (fixSub (MulAut.conj y)) (fixSub (MulAut.conj y)) :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hCqO⟩
  have hle : J.map θ.toMonoidHom ≤ GLALayer (fixSub (MulAut.conj y)) :=
    hJ'.1.trans (le_sSup hXcomp)
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hle).1
  have hJC : J.map θ.toMonoidHom = fixSub (MulAut.conj y) :=
    CFSG.HardMathSupport.Solomon.Coordinator.component_eq_of_normal_quasisimple hcomp le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) hCq fun H hH _ => hH
  have hT' : catalogIs (PSimple 3 (J.map θ.toMonoidHom)) S8.L84.isSp48 :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := θ.toMonoidHom)
      θ.injective 3 J _).2 hT
  have hcardJ := lieSEight_card_quot_center hLO hJ' hcomp.2.2 hT'
  rw [hJC] at hcardJ
  refine lieSEight_suQuot_card_ne hLO (E := GaloisField 2 (2 * (2 * m + 1)))
    (Q := 2 ^ (2 * m + 1)) (g := 2 * m + 1) rfl (by norm_num) (by omega) hFfcard hmq
    E.symm.toMonoidHom E.symm.surjective (fun x hx => ?_) hcardJ
  have h1 : x = 1 := E.symm.injective (by simpa using hx)
  rw [h1]
  exact Subgroup.one_mem _

end Ree

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
