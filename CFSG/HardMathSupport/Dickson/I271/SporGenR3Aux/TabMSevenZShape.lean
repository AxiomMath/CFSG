module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZCent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZTwo
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMSeven

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG zG)

section Shape


theorem tabMSeven_shape_of_not_conj_dG
    {z : Gmat} (hz : orderOf z = 7)
    (hzd : ∀ (g : Gmat) (m : ℕ), g * z * g⁻¹ ≠ dG ^ m)
    (htA : ∃ t : Gmat, orderOf t = 2 ∧ t * dG = dG * t ∧
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder)
    (huB : ∃ u : Gmat, orderOf u = 2 ∧ u * dG = dG * u ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) =
        CFSG.Monster.Existence.twoBCentralizerOrder ∧
      35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
        Subgroup.centralizer ({dG} : Set Gmat)))
    (hQ16 : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({z} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4)) :
    ShapeRkAt' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) z := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hO : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({z} : Set Gmat)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_isConj' (isConj_zG_of_not_conj hz hzd).symm gLAPPrimeCoreOf_zG
  obtain ⟨S, hSC, ⟨eS⟩⟩ := hQ16
  have h32 : ¬ 32 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) := by
    have h := tabMSeven_not_two_pow_five_dvd hz hzd htA huB
    norm_num at h
    exact h
  have hQ := tabMSeven_sylow_quat hSC eS h32
  have h7 : 7 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) :=
    (pow_dvd_pow 7 (by norm_num : 5 ≤ 6)).trans (seven_pow_dvd_of_not_conj hz hzd)
  exact Or.inl fun J => tabMSeven_noComp hO hQ h7
    (fun v hv R hR hle => card_isPGroup_seven_le_of_involution hv hR hle) J

end Shape

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
