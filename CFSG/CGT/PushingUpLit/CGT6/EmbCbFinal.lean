module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwo
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOne
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltM4
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltCaseA

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open
open CFSG.ComponentClassification
open CFSG.EvenSmallLie.OddTranspAlt (cls)

private theorem cbf_involution {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {t : ↥G}
    (ht : orderOf t = 2) : (t : MulAut V) ^ 2 = 1 ∧ (t : MulAut V) ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · have h1 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  · have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    omega

theorem altCaseA_holds (hB : TauCetiCatalogBridge)
    (hK3 : RankTwoStandard.RankTwoAlternatingStandard) (hNL : NatLiftStatement) : AltCaseA := by
  intro V _ _ hV G T Y h m hm hodd hY t ht htT c hc hct hcomm
  by_contra hbad
  have h2 : Alt2Rank1 := alt2Rank1_holds hB hK3 hNL
  obtain ⟨ht2, ht1⟩ := cbf_involution ht
  obtain ⟨X, hX⟩ := h.exists_cbLift h2 hV hm hodd hY ht htT hc hct hcomm hbad
  by_cases huniq : ∀ X' : Subgroup (MulAut V), IsCbLift G Y (t : MulAut V) m X' → X' = X
  · exact h.oneLift_false hNL h2 hV hm hodd hY t.2 htT ht2 ht1 hX huniq
  · obtain ⟨X', hne⟩ := not_forall.mp huniq
    obtain ⟨hX', hne⟩ := not_imp.mp hne
    exact h.noTwoLifts h2 hV hm hodd hY t.2 htT ht2 ht1 hX' hX hne

end CFSG.CGT.PushingUpLit.CGT6
