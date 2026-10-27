module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveGen
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

@[expose] def CentFiveBNoComp (G : Type) [Group G] : Prop :=
  ∀ k : G, orderOf k = 5 → ¬ InvertedByTwoA k →
    ∀ J : Subgroup G, ¬ GLAPComponent 5 (Subgroup.centralizer ({k} : Set G)) J

theorem CentFiveBNoComp.of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] (e : G ≃* G')
    (h : CentFiveBNoComp G') : CentFiveBNoComp G := by
  intro k hk hinv J hJ
  have hinv' : ¬ InvertedByTwoA (e k) := fun h' => hinv (by
    have := h'.map e.symm
    rwa [MulEquiv.symm_apply_apply] at this)
  have h1 := glaPComponent_map_equiv Nat.prime_five e hJ
  rw [map_centralizer_singleton e k] at h1
  exact h (e k) (by rw [MulEquiv.orderOf_eq]; exact hk) hinv' _ h1

end Residual

section Generic

theorem centShapeRk'_five_of_centNoComp {G : Type} [Group G] (hE : MonsterExistenceStatement G)
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hA : CentFiveA G) (hB : CentFiveBNoComp G) :
    CentShapeRk' 5 (GoodSpor 5 [.HN]) (RkSpor 5 [.HN]) G := by
  haveI : Finite G := (twoA_data_of_existence hE).1
  intro k hk1 hk5
  have hk : orderOf k = 5 := orderOf_eq_prime hk5 hk1
  by_cases hinv : InvertedByTwoA k
  · obtain ⟨-, α, -, hαk, -, i, hi, hsh⟩ :=
      invertedByTwoA_data hE Nat.prime_five (by norm_num) hk hinv
    have hHN : Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓
        Subgroup.centralizer ({k} : Set G)) ≃* NativeSporadic.HN) := by
      fin_cases i <;> first | exact hsh | (exfalso; simp [suborbitClassOrder] at hi)
    obtain ⟨e⟩ := hHN
    set H : Subgroup G := Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)
      with hH
    have hcard : Nat.card ↥H = 273030912000000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HN.card_HN
    have hs : IsSimpleGroup ↥H :=
      @MulEquiv.isSimpleGroup ↥H _ NativeSporadic.HN Units.instGroup
        CFSG.Sporadic.HN.isSimpleGroup_HN e
    have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      letI : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hcon }
      have hpr := IsSimpleGroup.prime_card (α := ↥H)
      rw [hcard] at hpr
      norm_num at hpr
    have hq : CFSG.Open.IsQuasisimple ↥H := tabMFive_quasisimple_of_simple_nonab hnab
    refine tabMFive_shapeRkAt'_of_inverted Nat.prime_five (by norm_num)
      (fun T T' _ _ f h => GoodSpor.of_equiv f h) (fun T T' _ _ f h => RkSpor.of_equiv f h)
      hk hαk inf_le_left inf_le_right hs hnab (by rw [hcard]; norm_num)
      (by rw [hcard]; exact hA k hk hinv) ?_ (rkSpor_HN_five_of_quasisimple hOut hSpM hBr hq)
    exact Or.inr (Or.inr ⟨.HN, List.mem_singleton_self _, ⟨e.trans (hBr .HN).some⟩⟩)
  · exact Or.inl fun J hJ => hB k hk hinv J hJ

end Generic

section Native

theorem mFiveShape_of_tabNoComp (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hA : CentFiveA (NativeSporadic.Carrier .M))
    (hB : CentFiveBNoComp (NativeSporadic.Carrier .M)) : MFiveShape := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := (twoA_data_of_existence hE).1
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  exact CentShapeRk'.of_equiv Nat.prime_five (fun T T' _ _ f h => GoodSpor.of_equiv f h)
    (fun T T' _ _ f h => RkSpor.of_equiv f h) e
    (centShapeRk'_five_of_centNoComp hE hOut hSpM hBr (CentFiveA.of_equiv e hA)
      (CentFiveBNoComp.of_equiv e hB))

theorem sporPair_M_five_of_tabNoComp (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 5) (hChev : ChevStrong 5)
    (hHN : SporStrong .HN 5) (hA : CentFiveA (NativeSporadic.Carrier .M))
    (hB : CentFiveBNoComp (NativeSporadic.Carrier .M)) : SporPair .M 5 :=
  sporPair_M_five_of_shape hOut hSpM hBr hP hChev hHN (mFiveShape_of_tabNoComp hOut hSpM hBr hA hB)

end Native

end CFSG.HardMathSupport.Dickson.I271
