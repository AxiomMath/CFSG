module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeC
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section Residual

@[expose] def CentThreeBNoComp (G : Type) [Group G] : Prop :=
  ∀ k : G, orderOf k = 3 → ¬ InvertedByTwoA k →
    ∀ J : Subgroup G, ¬ GLAPComponent 3 (Subgroup.centralizer ({k} : Set G)) J

theorem CentThreeBNoComp.of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] (e : G ≃* G')
    (h : CentThreeBNoComp G') : CentThreeBNoComp G := by
  intro k hk hinv J hJ
  have hinv' : ¬ InvertedByTwoA (e k) := fun h' => hinv (by
    have := h'.map e.symm
    rwa [MulEquiv.symm_apply_apply] at this)
  have h1 := glaPComponent_map_equiv Nat.prime_three e hJ
  rw [map_centralizer_singleton e k] at h1
  exact h (e k) (by rw [MulEquiv.orderOf_eq]; exact hk) hinv' _ h1

@[expose] def M3ResBNoComp : Prop :=
  ∀ J : Subgroup CFSG.Monster.Generated.Gmat,
    ¬ GLAPComponent 3 (Subgroup.centralizer
      ({CFSG.AGLEmbedding.Norton.MON5_7.tbw} : Set CFSG.Monster.Generated.Gmat)) J

theorem centThreeBNoComp_gmat (hCls : CFSG.HardMathSupport.Dickson.Sec6.BM2.M3BClass)
    (hB : M3ResBNoComp) : CentThreeBNoComp CFSG.Monster.Generated.Gmat := by
  intro x hx hinv J hJ
  obtain ⟨c, hc⟩ := isConj_iff.1 (hCls x hx hinv)
  have h1 := glaPComponent_map_equiv Nat.prime_three (MulAut.conj c) hJ
  rw [map_centralizer_singleton (MulAut.conj c) x] at h1
  have h4 : (MulAut.conj c) x = CFSG.AGLEmbedding.Norton.MON5_7.tbw := by
    simpa [MulAut.conj_apply] using hc
  rw [h4] at h1
  exact hB _ h1

end Residual

section Generic

theorem centShapeRk'_three_of_centNoComp {G : Type} [Group G] (hE : MonsterExistenceStatement G)
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hA : CentThreeA G) (hB : CentThreeBNoComp G) (hC : CentThreeC G) :
    CentShapeRk' 3 (GoodSpor 3 [.Fi24Prime, .Th]) (RkSpor 3 [.Fi24Prime, .Th]) G := by
  haveI : Finite G := (twoA_data_of_existence hE).1
  intro k hk1 hk3
  have hk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  by_cases hinv : InvertedByTwoA k
  · obtain ⟨α, hα2, hαc, hαk, i, hi, hsh⟩ :=
      invertedByTwoA_data_twoA hE Nat.prime_three (by norm_num) hk hinv
    have hi34 : i = 3 ∨ i = 4 := by
      clear hsh
      revert i
      decide
    rcases hi34 with rfl | rfl
    · obtain ⟨hq, ⟨e⟩⟩ := hA k α hk hα2 hαc hαk hsh
      exact tabMThree_shapeRkAt'_of_cover hOut hSpM hBr hk hq e
    · obtain ⟨e⟩ := hsh
      exact tabMThree_shapeRkAt'_of_th hOut hSpM hBr hk hαk inf_le_left inf_le_right e
        (hC k α hk hα2 hαc hαk ⟨e⟩)
  · exact Or.inl fun J hJ => hB k hk hinv J hJ

end Generic

section Native

section Shape

theorem mThreeShape_of_tabNoComp (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hA : CentThreeA (NativeSporadic.Carrier .M))
    (hB : CentThreeBNoComp (NativeSporadic.Carrier .M))
    (hC : CentThreeC (NativeSporadic.Carrier .M)) : MThreeShape := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := (twoA_data_of_existence hE).1
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  exact CentShapeRk'.of_equiv Nat.prime_three (fun T T' _ _ f h => GoodSpor.of_equiv f h)
    (fun T T' _ _ f h => RkSpor.of_equiv f h) e
    (centShapeRk'_three_of_centNoComp hE hOut hSpM hBr (CentThreeA.of_equiv e hA)
      (CentThreeBNoComp.of_equiv e hB) (CentThreeC.of_equiv e hC))

theorem sporPair_M_three_of_tabNoComp (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 3) (hChev : ChevStrong 3)
    (hFi24 : SporStrong .Fi24Prime 3) (hTh : SporStrong .Th 3)
    (hA : CentThreeA (NativeSporadic.Carrier .M))
    (hB : CentThreeBNoComp (NativeSporadic.Carrier .M))
    (hC : CentThreeC (NativeSporadic.Carrier .M)) : SporPair .M 3 :=
  sporPair_M_three_of_shape hOut hSpM hBr hP hChev hFi24 hTh
    (mThreeShape_of_tabNoComp hOut hSpM hBr hA hB hC)

section Tab

theorem centThreeBNoComp_M_of_m3ResBNoComp (hB : M3ResBNoComp) :
    CentThreeBNoComp (NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  haveI : Finite MGriess :=
    (twoA_data_of_existence CFSG.Milestones.cl_lit_monster_existence_griess_conway).1
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  exact CentThreeBNoComp.of_equiv e.symm (CentThreeBNoComp.of_equiv φ
    (centThreeBNoComp_gmat CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds hB))

theorem sporPair_M_three_of_tab' (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 3) (hChev : ChevStrong 3)
    (hFi24 : SporStrong .Fi24Prime 3) (hTh : SporStrong .Th 3)
    (hA : CentThreeA (NativeSporadic.Carrier .M)) (hB : M3ResBNoComp)
    (hC : CentThreeC (NativeSporadic.Carrier .M)) : SporPair .M 3 :=
  sporPair_M_three_of_tabNoComp hOut hSpM hBr hP hChev hFi24 hTh hA
    (centThreeBNoComp_M_of_m3ResBNoComp hB) hC

end Tab

end Shape

end Native

end CFSG.HardMathSupport.Dickson.I271
