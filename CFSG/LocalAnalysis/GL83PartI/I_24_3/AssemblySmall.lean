module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Main
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeAut
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.Monster.B.TwoA.Fischer.M22Aut
public import CFSG.Sporadic.Bridge.M22

public section

namespace GL83.I243

open CFSG CFSG.Open TauCeti CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.CoverThree
  CFSG.ComponentClassification.OuterAutomorphisms

theorem smallThreeFacts_alternating {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    {n : ℕ} (h67 : n = 6 ∨ n = 7)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    KOutTwoGroup K ∧ 3 ^ 2 ∣ Nat.card (K ⧸ Subgroup.center K) ∧
      ¬ 3 ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hOut : IsPGroup 2 (Outer (alternatingGroup (Fin n))) := by
    rcases h67 with rfl | rfl
    · exact CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
    · exact CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_seven
  refine ⟨kOutTwoGroup_of_isPGroup_outer hK (hOut.of_equiv (equivalence e).symm), ?_⟩
  rw [Nat.card_congr e.toEquiv]
  rcases h67 with rfl | rfl
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]

theorem smallThreeFacts_M22
    {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic .M22).Group) :
    KOutTwoGroup K ∧ 3 ^ 2 ∣ Nat.card (K ⧸ Subgroup.center K) ∧
      ¬ 3 ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hcard : Nat.card (K ⧸ Subgroup.center K) = 443520 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hout : Nat.card (Outer Blueprint.NativeSporadic.M22) = 2 :=
    CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1
  have hOut : IsPGroup 2 (Outer (CFSGIndex.sporadic .M22).Group) :=
    (IsPGroup.of_card (n := 1) (by rw [hout, pow_one])).of_equiv (equivalence b)
  refine ⟨kOutTwoGroup_of_isPGroup_outer hK (hOut.of_equiv (equivalence e).symm), ?_⟩
  rw [hcard]
  norm_num

theorem smallThreeFacts_holds :
    SmallThreeFacts := by
  intro K _ _ hK i hi ⟨e⟩
  rcases hi with ⟨n, hn, h67, rfl⟩ | rfl
  · exact smallThreeFacts_alternating hK h67 e
  · exact smallThreeFacts_M22 hK e

end GL83.I243
