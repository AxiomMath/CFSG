module

public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharAlmostSimple

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP

@[expose] def KFactSeitzOuterCubeRankTwoAtPrime (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    [Fact p.Prime] : Prop :=
  p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
    K.Normal → Subgroup.centralizer (K : Set Y) = ⊥ →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d →
    (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
    ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p K E

theorem kFactSeitzOuterCubeRankTwoAt_of_atPrime {d : TauCeti.ValidLieTypeIndex}
    (h : ∀ (p : ℕ) [Fact p.Prime], KFactSeitzOuterCubeRankTwoAtPrime d p) :
    KFactSeitzOuterCubeRankTwoAt d :=
  fun p _ hp2 Y _ _ K hKn hC he hpd hl hno E hE hc =>
    h p hp2 Y K hKn hC he hpd hl hno E hE hc

theorem kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} [Fact p.Prime]
    (h : p ≠ 2 → p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
      (¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
        Nat.card E = p ^ 3) →
      FieldAutData (TauCeti.CFSGIndex.lie d).Group p ∧
        FixPlaneGen (TauCeti.CFSGIndex.lie d).Group p) :
    KFactSeitzOuterCubeRankTwoAtPrime d p := by
  intro hp2 Y _ _ K hKn hC he hpd hl hno E hE hc
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := he
  have : K.Normal := hKn
  have hnoC : ¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
      Nat.card E = p ^ 3 := by
    rintro ⟨E', hE', hc'⟩
    refine hno ⟨(E'.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE' _) _, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hc']
  obtain ⟨hF, hP⟩ := h hp2 hpd hl hnoC
  exact hyperGen_of_fieldAutData hC hno (hF.of_mulEquiv e hp) (hP.of_mulEquiv e hp) hE hc

end CFSG.AGLEmbedding
