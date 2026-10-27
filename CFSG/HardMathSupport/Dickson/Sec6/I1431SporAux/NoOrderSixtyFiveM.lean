module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGmat
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGraphMonster
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenAssembly
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Co1
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.CentralizerCFive
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

section Abstract

variable {G : Type*} [Group G]

theorem invComm_pow_eq {x : G} (hx : orderOf x = 13) {k : ℕ} (hk : k % 13 ≠ 0) :
    invComm (x ^ k) = invComm x := by
  ext f
  constructor
  · rintro ⟨hf2, hf1, hfx⟩
    exact ⟨hf2, hf1, commute_of_commute_pow_thirteen hx hk hfx⟩
  · rintro ⟨hf2, hf1, hfx⟩
    exact ⟨hf2, hf1, (((show Commute f x from hfx).pow_right k).eq)⟩

theorem ncard_invComm_conj (m s : G) : (invComm (m * s * m⁻¹)).ncard = (invComm s).ncard := by
  have := ncard_invComm_map (MulAut.conj m) s
  rwa [MulAut.conj_apply] at this

end Abstract

section Native


theorem ncard_invComm_xE_le (φ : Gmat ≃* MGriess) : (invComm (gw thirteenX)).ncard ≤ 451 := by
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
  have h := ncard_invComm_le_of_existence ha hA hgraph (x := φ (gw thirteenX)) hx
    (fun u hu2 hu1 hux => by
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
      exact haconj.trans hc)
  rwa [ncard_invComm_map φ] at h

theorem cases_of_orderOf_thirteen (φ : Gmat ≃* MGriess)
    (hle : (invComm (gw thirteenX)).ncard ≤ 451) {x : MGriess} (hx : orderOf x = 13) :
    ¬ 5 ∣ Nat.card (centralizer ({x} : Set MGriess)) ∨ ¬ 5 ∣ (invComm x).ncard := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hs : orderOf (φ.symm x) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen (φ.symm x) hs
  · left
    have hk1 : gw genD13W1 ^ k ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [orderOf_c13] at this
      exact hk (Nat.mod_eq_zero_of_dvd this)
    rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv_apply φ.symm x,
      ← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq m, h,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime orderOf_c13 hk1]
    exact not_five_dvd_card_centralizer_c
  · right
    rw [← ncard_invComm_map φ.symm x, ← ncard_invComm_conj m, h, invComm_pow_eq orderOf_xE hk]
    exact not_five_dvd_invComm_xE hle

theorem noOrder65_M : NoOrder 65 NativeSporadic.M := by
  have hB65 : NoOrder 65 NativeSporadic.B := noOrder65_B
  have hCo65 : NoOrder 65 NativeSporadic.Co1 := fun g =>
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.noOrderSixtyFive_Co1 g
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let φ : Gmat ≃* MGriess :=
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  have hle := ncard_invComm_xE_le φ
  have h := noOrder65_of_cases CFSG.Milestones.cl_lit_monster_existence_griess_conway hB65 hCo65
    (fun x hx => cases_of_orderOf_thirteen φ hle hx)
  exact noOrder_of_mulEquiv e.symm h

end Native

end CFSG.HardMathSupport.Dickson.Sec6.I1431
