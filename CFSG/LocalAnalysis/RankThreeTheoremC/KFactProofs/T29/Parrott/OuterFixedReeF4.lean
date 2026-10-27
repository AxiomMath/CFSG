module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofRee

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti CFSG.LieType.Ree

section Field


theorem outerFixesE9_reeGamma {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    OuterFixesE9 (ReeTag.F4.reeGamma K m) := by
  intro α hα3 hαo
  have : Finite (ReeTag.F4.reeGamma K m) := Subtype.finite
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.exists_pair_autFix_ree hm hK hα3 hαo
  obtain ⟨hE, hE9⟩ := isElemAbelian_card_sup_zpowers_of_pair hu1 hu3 hv3 huv hvu
  obtain ⟨hE', hE9'⟩ := isElemAbelian_card_map_of_E9 (CFSG.RankThree.PartTwo.Sec4.autFix α).subtype
    (Subgroup.subtype_injective _) hE hE9
  refine ⟨_, hE', hE9', ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end Field

section Index


theorem outerFixedAt_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    OuterFixedAt ⟨.reeF4 m, hv⟩ := by
  refine outerFixedAt_of_model fun K _ _ e => ?_
  obtain ⟨X, _, _, _, hm, hX, -, ⟨f⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  exact ⟨_, _, outerFixesE9_reeGamma hm hX, ⟨e.trans f⟩⟩

end Index

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
