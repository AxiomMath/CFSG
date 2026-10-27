module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporModel
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3167
public import Certificates.Certificate4089
public import Certificates.Certificate4102
public import Certificates.Certificate4140

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HSPairs

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_card_vals
    : Nat.card (hsCtx.Y 0) = 512 ∧ Nat.card (hsCtx.Y 1) = 7680 ∧
    Nat.card (hsCtx.Y 2) = 10752 ∧ Nat.card (hsCtx.Y 3) = 1536 ∧ Nat.card (hsCtx.Y 4) = 1536 :=
  ⟨(hs_member_card 0 (by norm_num)).trans rfl, (hs_member_card 1 (by norm_num)).trans rfl,
    (hs_member_card 2 (by norm_num)).trans rfl, (hs_member_card 3 (by norm_num)).trans rfl,
    (hs_member_card 4 (by norm_num)).trans rfl⟩

theorem hs_localPair :
    LocalPair (J hsData) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := hs_card_vals
  have hcard : Nat.card (J hsData) = 44352000 := by rw [hs_card]; norm_num
  refine localPair_of_ctx hsCtx hs_S_sylow 1 2 hs_J1 hs_J2 ?_ ?_ ?_ ?_ ?_ hs_goodLocal_Y1
    hs_goodLocal_Y2
  · intro j hj h
    rw [hs_J] at hj
    interval_cases j <;> omega
  · intro j hj h
    rw [hs_J] at hj
    interval_cases j <;> omega
  · omega
  · omega
  · intro j hj ⟨h1, h2⟩
    rw [hs_J] at hj
    have d1 := Subgroup.card_dvd_of_le h1
    have d2 := Subgroup.card_dvd_of_le h2
    interval_cases j <;> simp only [c0, c1, c2, c3, c4] at d1 d2 <;> omega

theorem hs_equiv
    : Nonempty (NativeSporadic.Carrier .HS ≃* J hsData) :=
  ⟨seedEquiv hs_facts.toBaseFacts⟩

theorem pairsFor_HS :
    PairsFor (TypeSporadic .HS) := by
  obtain ⟨e⟩ := hs_equiv
  have : Finite (J hsData) := inferInstance
  have key := @pairsFor_of_localPair_equiv .HS (J hsData) _ this
  exact key e hs_localPair

end CFSG.QuasithinUnique.Vol2Native.L239.HSPairs
