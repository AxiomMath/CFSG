module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayBlock
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6CaseL

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.LieType.Ree (ReeTag)
open scoped MatrixGroups

local instance f4PilotQ2E6RelayMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6RelayMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def TwoE6RelayEdgeInput : Prop :=
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
        (∃ α' : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ →* G,
          Function.Injective α' ∧
          α'.range ≤ centralizerPerfectCore
            (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K (Pi.single 1 1)))) ∧
          (∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
            chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) ∧
          ∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
            (x : Matrix.SpecialLinearGroup (Fin 6) K) ∈
                blockSpecialLinear ({0, 1} : Finset (Fin 6)) →
              Commute ((e.symm (relayAlign K root1242) : L) : G) (α' x) ∧
                Commute ((e.symm (relayAlign' K root1242) : L) : G) (α' x)) ∧
        (∃ α' : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ →* G,
          Function.Injective α' ∧
          α'.range ≤ centralizerPerfectCore
            (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K rootE1mE2Align))) ∧
          (∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
            chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) ∧
          ∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
            (x : Matrix.SpecialLinearGroup (Fin 6) K) ∈
                blockSpecialLinear ({1, 2} : Finset (Fin 6)) →
              Commute ((e.symm (relayAlign K rootE2pE3Align) : L) : G) (α' x) ∧
                Commute ((e.symm (relayAlign' K rootE2pE3Align) : L) : G) (α' x))

theorem twoE6RelayInput_of_edgeInput (h : TwoE6RelayEdgeInput) : TwoE6RelayInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨⟨α₁, h1i, h1r, h1S, h1v⟩, ⟨α₃, h3i, h3r, h3S, h3v⟩⟩ :=
    h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  exact ⟨⟨relay_mem_alignedSubgroup_zero_of_edge hw hr hker hconj hn h1i h1r h1S
      fun x hx => (h1v x hx).1,
    relay_mem_alignedSubgroup_zero_of_edge hw hr hker hconj hn h1i h1r h1S
      fun x hx => (h1v x hx).2⟩,
    ⟨relay_mem_alignedSubgroup_two_of_edge hw hr hker hconj hn h3i h3r h3S
      fun x hx => (h3v x hx).1,
    relay_mem_alignedSubgroup_two_of_edge hw hr hker hconj hn h3i h3r h3S
      fun x hx => (h3v x hx).2⟩⟩

theorem twoE6PairInput_of_edgeInput (h : TwoE6RelayEdgeInput) : TwoE6PairInput :=
  twoE6PairInput_of_relayInput (twoE6RelayInput_of_edgeInput h) twoE6UniqueInput_holds

end CFSG.SeitzReduction.F4Pilot
