module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGmat
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGraphMonster
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.RankThree.Native.BFiveLocal
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open Subgroup CFSG.Blueprint CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
  CFSG.HardMathSupport.Dickson.Sec6.I1431

theorem card_cent_inf_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (a b : K) :
    Nat.card ↥(Subgroup.centralizer ({e a} : Set K') ⊓ Subgroup.centralizer ({e b} : Set K')) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set K) ⊓ Subgroup.centralizer ({b} : Set K)) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e.injective.eq_iff, e.injective.eq_iff]

section Inf


theorem card_cent_inf_xE_le (φ : Gmat ≃* MGriess) {u : Gmat} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hux : u * gw thirteenX = gw thirteenX * u) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
      Subgroup.centralizer ({gw thirteenX} : Set Gmat)) ≤ 936 := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, hnc, hcls, hA, hBz, hgraph⟩ :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hfin
  have ht2 : orderOf (φ tGmat) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact CFSG.Monster.Tri.orderOf_tGmat
  have haconj : IsConj a (φ tGmat) := by
    rcases hcls _ ht2 with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, -, -, -, h17⟩ := hBz _ h
      apply h17
      show 17 ∣ Nat.card (Subgroup.centralizer ({φ tGmat} : Set MGriess))
      rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv_apply φ tGmat,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.natCard_centralizer_tGmat]
      norm_num [monsterBabyOrder]
  have hx : orderOf (φ (gw thirteenX)) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_xE
  have hA1 : ∀ u : MGriess, u * u = 1 → u ≠ 1 → u * φ (gw thirteenX) = φ (gw thirteenX) * u →
      IsConj a u := by
    intro u hu2 hu1 hux
    have hv2 : φ.symm u * φ.symm u = 1 := by rw [← map_mul, hu2, map_one]
    have hv1 : φ.symm u ≠ 1 := fun h1 => hu1 (by simpa using congrArg φ h1)
    have hvx : φ.symm u * gw thirteenX = gw thirteenX * φ.symm u := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hux
    have hvc : IsConj tGmat (φ.symm u) := isConj_tGmat_of_commute_xE hv2 hv1 hvx
    have hc : IsConj (φ tGmat) u := by
      have := (φ : Gmat →* MGriess).map_isConj hvc
      simpa using this
    exact haconj.trans hc
  obtain ⟨c, D⟩ := thirteenGraphData_of_existence ha hA hgraph
  have key : Nat.card ↥(Subgroup.centralizer ({φ u} : Set MGriess) ⊓
      Subgroup.centralizer ({φ (gw thirteenX)} : Set MGriess)) ≤ 936 :=
    card_cent_inf_le D hx hA1 (u := φ u) (by rw [← map_mul, hu2, map_one])
      (fun h1 => hu1 (φ.injective (by rw [h1, map_one])))
      (by rw [← map_mul, ← map_mul, hux])
  rwa [card_cent_inf_mulEquiv φ u (gw thirteenX)] at key

end Inf

end CFSG.HardMathSupport.Dickson.BMRows
