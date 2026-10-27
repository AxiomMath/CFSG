module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwist
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem babyTwistThreeB_of_noPureFour (h : ∀ k, BabyNoPureFourAt k) : BabyTwistThreeB := by
  intro E D T hE _ hDE hDcard hD hT _ hTD
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices hbot : T = ⊥ by
    rw [hbot]
    exact bot_le
  by_contra hne
  have h2 : 2 ∣ Nat.card T :=
    hT.card_eq_or_dvd.resolve_left fun h1 => hne (Subgroup.eq_bot_of_card_eq T h1)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [← Subgroup.orderOf_coe] at ht
  obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 _ ht
  have hDt : D ≤ Subgroup.centralizer ({(t : NativeSporadic.B)} : Set NativeSporadic.B) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (hTD t.2) x hx)
  obtain ⟨x, hxD, hx1, hx⟩ := h k _ hk D hDt (hE.mono hDE) hDcard
  exact hx (hD x hxD hx1)

end CFSG.LocalAnalysis.GLTheoremA.H1017
