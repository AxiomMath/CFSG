module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepOne

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancingLocal

theorem twoComponent_coreQuotient_quasisimple {X : Type*} [Group X] [Finite X] {x : X}
    {L : Subgroup X} (hLx : L ≤ centralizer ({x} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X)))) :
    IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hLx)
    (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hL)

theorem center_isPGroup_two_of_pPrimeCore_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (h : pPrimeCore 2 Q = ⊥) : IsPGroup 2 (center Q) := by
  intro z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  set w : center Q := z ^ 2 ^ k with hw
  have hwm : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  have hle : (zpowers (w : Q)) ≤ pPrimeCore 2 Q := by
    have hc : zpowers (w : Q) ≤ center Q := zpowers_le.mpr w.2
    refine le_sSup ⟨normal_of_le_center hc, ?_⟩
    rw [Nat.card_zpowers, orderOf_submonoid, hwm]
    exact Nat.coprime_two_left.mpr hm
  rw [h, le_bot_iff, zpowers_eq_bot] at hle
  exact Subtype.ext hle

noncomputable def coreQuotientCenterEquiv (L : Type*) [Group L] :
    (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃* L ⧸ Open.fusionZStar L :=
  (QuotientGroup.quotientMulEquivOfEq
      (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 L))
        (center (L ⧸ pPrimeCore 2 L))).symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient _ _ (le_centralPreimage _)).trans
      (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_centralPreimage L).symm))

noncomputable def coreQuotientEquiv_of_center_eq_bot (L : Type*) [Group L]
    (h : center (L ⧸ pPrimeCore 2 L) = ⊥) : L ⧸ pPrimeCore 2 L ≃* L ⧸ Open.fusionZStar L :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans
    (coreQuotientCenterEquiv L)

end CFSG.ComponentClassification.TBLit
