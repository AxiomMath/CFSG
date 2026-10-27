module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.CentralizerCIsolation
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.IsolatedFive
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

theorem not_five_dvd_card_centralizer_c :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcx : gw genD13W1 * xGmat = xGmat * gw genD13W1 :=
    Subgroup.mem_centralizer_singleton_iff.1 c_mem_cent
  have hxC : xGmat ∈ Subgroup.centralizer ({gw genD13W1} : Set Gmat) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
  have hcore : ∀ K : Subgroup (Subgroup.centralizer ({gw genD13W1} : Set Gmat)), K.Normal →
      Nat.Coprime 13 (Nat.card K) → K = ⊥ := fun K hK hcop =>
    eq_bot_of_normal_of_core_eq_bot (gLAPPrimeCoreOf_c13_eq_bot
      (odd_card_core_thirteen _ orderOf_c13)) K hcop
  have hsmall : ∀ R : Subgroup (Subgroup.centralizer ({gw genD13W1} : Set Gmat)),
      IsPGroup 13 R → Nat.card R ≤ 13 ^ 3 := fun R hR =>
    card_le_of_isPGroup_of_factorization factorization_Gmat_thirteen _ R hR
  have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer
      ({(⟨xGmat, hxC⟩ : Subgroup.centralizer ({gw genD13W1} : Set Gmat))} :
        Set (Subgroup.centralizer ({gw genD13W1} : Set Gmat)))) := by
    have hdvd := card_inf_centralizer_dvd (u := xGmat) (h := 1) (f := gw genD13W1)
      (by rw [one_mul, inv_one, mul_one]) hcx orderOf_c13
    intro h5
    rw [card_centralizer_subtype_eq hxC] at h5
    have := h5.trans hdvd
    omega
  exact not_five_dvd_card_of_zStar hcore hsmall (v := ⟨xGmat, hxC⟩)
    (Subtype.ext xGmat_mul_self') (fun h => xGmat_ne_one' (congrArg Subtype.val h))
    (isolated_of_unique_involution xGmat_mul_self' xGmat_ne_one' hcx.symm hxC
      (fun t ht htx htc => eq_one_or_eq_xGmat_of_involution ht htx htc)) h5

end CFSG.HardMathSupport.Dickson.Sec6.I1431
