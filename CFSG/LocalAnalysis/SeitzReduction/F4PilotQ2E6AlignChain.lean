module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6AlignTw

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma fixedGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6AlignChainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6AlignChainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Defs

variable (K : Type) [Field K]

@[expose] def rootE1mE2Align : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 2]

@[expose] def rootE2pE3Align : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 0]

@[expose] noncomputable def f4RootPairAlign (γ : Fin (Tag.rank .F4) → ℤ) :
    Subgroup (adjointGroup .F4 K) :=
  (Adjoint.f4Datum K).rootGroup γ ⊔ (Adjoint.f4Datum K).rootGroup (-γ)

@[expose] noncomputable def relayAlign (γ : Fin (Tag.rank .F4) → ℤ) : adjointGroup .F4 K :=
  Adjoint.f4Par K (Pi.single 0 1) 1 * Adjoint.f4Par K (-γ) 1

@[expose] noncomputable def relayAlign' (γ : Fin (Tag.rank .F4) → ℤ) : adjointGroup .F4 K :=
  Adjoint.f4Par K (-Pi.single 0 1) 1 * Adjoint.f4Par K γ 1

end Defs

section Aligned

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def alignedSubgroup (e : L ≃* adjointGroup .F4 K) (S : Subgroup G) :
    Subgroup (adjointGroup .F4 K) :=
  (centralizer (S : Set G)).comap (L.subtype.comp e.symm.toMonoidHom)

theorem commute_of_mem_alignedSubgroup {e : L ≃* adjointGroup .F4 K} {S : Subgroup G}
    {l : adjointGroup .F4 K} (hl : l ∈ alignedSubgroup e S) {b : G} (hb : b ∈ S) :
    Commute ((e.symm l : L) : G) b :=
  ((mem_centralizer_iff.1 hl) b hb).symm

theorem commute_of_le_closure_aligned {e : L ≃* adjointGroup .F4 K} {S : Subgroup G}
    {A B : Subgroup (adjointGroup .F4 K)} {u u' : adjointGroup .F4 K}
    (hgen : CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0 ≤
      closure ((A : Set (adjointGroup .F4 K)) ∪ B ∪ {u, u'}))
    (hA : A ≤ alignedSubgroup e S) (hB : B ≤ alignedSubgroup e S)
    (hu : u ∈ alignedSubgroup e S) (hu' : u' ∈ alignedSubgroup e S) :
    ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0),
      ∀ b ∈ S, Commute a b := by
  have hle : CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0 ≤
      alignedSubgroup e S := by
    refine hgen.trans (closure_le _ |>.2 ?_)
    rintro x ((hx | hx) | hx)
    · exact hA hx
    · exact hB hx
    · rcases hx with rfl | rfl
      · exact hu
      · exact hu'
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩ b hb
  exact commute_of_mem_alignedSubgroup (hle hl) hb

end Aligned

@[expose] def TwoA3GenInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0 ≤
        closure ((f4RootPairAlign K rootR : Set (adjointGroup .F4 K)) ∪
          (f4RootPairAlign K (Pi.single 1 1) : Set (adjointGroup .F4 K)) ∪
          {relayAlign K root1242, relayAlign' K root1242}) ∧
      CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0 ≤
        closure ((f4RootPairAlign K rootR : Set (adjointGroup .F4 K)) ∪
          (f4RootPairAlign K rootE1mE2Align : Set (adjointGroup .F4 K)) ∪
          {relayAlign K rootE2pE3Align, relayAlign' K rootE2pE3Align})

@[expose] def TwoE6ChainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ ΦA : e6ScLevi K e6A5Nodes →* G,
        ΦA.range = centralizerPerfectCore (subgroupToG e X₀) →
        ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) →
        (∀ x y : e6ScLevi K e6A5Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) →
        IsLeviNormalizedA e ΦA →
        (f4RootPairAlign K rootR ≤ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ∧
          f4RootPairAlign K (Pi.single 1 1) ≤ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ∧
          relayAlign K root1242 ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ∧
          relayAlign' K root1242 ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range) ∧
        (f4RootPairAlign K rootR ≤ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ∧
          f4RootPairAlign K rootE1mE2Align ≤ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ∧
          relayAlign K rootE2pE3Align ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ∧
          relayAlign' K rootE2pE3Align ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range)

@[expose] def TwoTwistedE6ChainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
        (ε : h.fixedField ≃+* K)
        (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
        ΦX.range = centralizerPerfectCore (subgroupToG e X₀) →
        ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
        (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            t * ΦX x * t⁻¹ = ΦX y) →
        IsLeviNormalizedU h ε e ΦX →
        (f4RootPairAlign K rootR ≤ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range ∧
          f4RootPairAlign K (Pi.single 1 1) ≤
            alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range ∧
          relayAlign K root1242 ∈ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range ∧
          relayAlign' K root1242 ∈ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range) ∧
        (f4RootPairAlign K rootR ≤ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range ∧
          f4RootPairAlign K rootE1mE2Align ≤
            alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range ∧
          relayAlign K rootE2pE3Align ∈ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range ∧
          relayAlign' K rootE2pE3Align ∈ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range)

theorem twoE6AlignInput_of_chainInput (hG : TwoA3GenInput) (hC : TwoE6ChainInput) :
    TwoE6AlignInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn a ha
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨hg1, hg3⟩ := hG K hK2
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ :=
    hC G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  exact ⟨fun b => commute_of_le_closure_aligned hg1 h1 h2 h3 h4 a ha _ ⟨b, rfl⟩,
    fun b => commute_of_le_closure_aligned hg3 h5 h6 h7 h8 a ha _ ⟨b, rfl⟩⟩

theorem twoTwistedE6AlignInput_of_chainInput (hG : TwoA3GenInput)
    (hC : TwoTwistedE6ChainInput) : TwoTwistedE6AlignInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' F _ _ _ h ε ΦX hr hker hconj hn a ha
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨hg1, hg3⟩ := hG K hK2
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ :=
    hC G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' F h ε ΦX hr hker hconj hn
  exact ⟨fun b => commute_of_le_closure_aligned hg3 h5 h6 h7 h8 a ha _ ⟨b, rfl⟩,
    fun b => commute_of_le_closure_aligned hg1 h1 h2 h3 h4 a ha _ ⟨b, rfl⟩⟩

theorem twoE6PairInput_of_chainInput (hG : TwoA3GenInput) (hC : TwoE6ChainInput)
    (hU : TwoE6UniqueInput) : TwoE6PairInput :=
  twoE6PairInput_of_alignInput (twoE6AlignInput_of_chainInput hG hC) hU

end CFSG.SeitzReduction.F4Pilot
