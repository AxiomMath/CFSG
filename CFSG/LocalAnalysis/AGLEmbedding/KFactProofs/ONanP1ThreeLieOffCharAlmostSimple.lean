module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNoInner

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def KFactSeitzOuterCubeRankTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
    K.Normal → Subgroup.centralizer (K : Set Y) = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d →
    (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
    ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p K E

@[expose] def KFactSeitzOuterCubeRankTwoAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
    K.Normal → Subgroup.centralizer (K : Set Y) = ⊥ →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d →
    (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
    ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p K E

theorem kFactSeitzOuterCubeRankTwo_of_at (h : ∀ d, KFactSeitzOuterCubeRankTwoAt d) :
    KFactSeitzOuterCubeRankTwo :=
  fun p _ hp2 Y _ _ K hKn hC d he hpd hl hno E hE hc =>
    h d p hp2 Y K hKn hC he hpd hl hno E hE hc

@[expose] def P1OffCharAlmostSimpleNonNormal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      Subgroup.centralizer (K : Set Y) = ⊥ →
      (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
      K ≤ Y₀ → ¬ (Rb : Subgroup Y) ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p ≠ d.1.characteristic →
        P1ThreeLieList p d

theorem p1OffCharAlmostSimple_of (hS : KFactSeitzOuterCubeRankTwo)
    (hNN : P1OffCharAlmostSimpleNonNormal) : P1OffCharAlmostSimple := by
  intro p _ Y _ _ Rb Y₀ h hcat K hK huniq hnc hC hnoK d hd hpd
  by_contra hlist
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZ : Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzC : (z : Y) ∈ Subgroup.centralizer (K : Set Y) :=
      Subgroup.mem_centralizer_iff.2 fun k hk =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
    rw [hC, Subgroup.mem_bot] at hzC
    exact (Subgroup.mem_bot).2 (Subtype.ext hzC)
  obtain ⟨e⟩ := hd
  have e' : K ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientBot (G := K)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  obtain ⟨E, hER, hEa, hEc⟩ : ∃ E ≤ (Rb : Subgroup Y), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
    obtain ⟨A, hAR, hA, hAcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (Rb : Subgroup Y)
    obtain ⟨C, hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 3)
      (hAcard ▸ pow_dvd_pow p h.three_le_pRank)
    have : IsMulCommutative A := hA.1
    have hC' : IsElemAbelian p C := ⟨inferInstance, fun x _ => Subtype.ext (hA.2 x x.property)⟩
    refine ⟨C.map A.subtype, (Subgroup.map_subtype_le C).trans hAR,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hC' A.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective, hC]
  have hgen := hS p hp2 Y K hKn hC d ⟨e'⟩ hpd hlist hnoK E hEa hEc
  by_cases hN : (Rb : Subgroup Y) ≤ (K ⊔ (Rb : Subgroup Y)).normalCore
  · exact h.false_of_hyperGen hEa hEc hER (hER.trans hN) hgen
  · exact hlist (hNN p Y Rb Y₀ h hcat K hK huniq hnc hC hnoK (h.le_of_hyperGen hEa hEc hER hgen)
      hN d ⟨e⟩ hpd)

section Cubes


theorem p1ThreeLieOffChar_of_cubesV10 (hX : ExcCubeResidualsV4)
    (hGA : GriessMultipliersAllModels) (h3 : P1OffCharCoverThree)
    (hCov : P1OffCharCoverThreeNoInner) (hS : KFactSeitzOuterCubeRankTwo)
    (hNN : P1OffCharAlmostSimpleNonNormal) : P1ThreeLieOffChar :=
  p1ThreeLieOffChar_of_cubesV9 hX hGA h3 hCov (p1OffCharAlmostSimple_of hS hNN)

end Cubes

end CFSG.AGLEmbedding
