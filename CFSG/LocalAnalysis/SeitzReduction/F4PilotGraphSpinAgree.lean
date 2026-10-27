module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinComm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphSpinAgreeNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotGraphSpinAgreeNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Inputs

@[expose] def E6RowPieceCommInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∀ g ∈ pieceCore e {0}, ∀ g' ∈ pieceCore e {3}, Commute g g'

@[expose] def E6GraphRowSpinAgreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) (hw : F4Work L K t f) (hf : 2 ≤ f),
    ∀ N₁ N₂ : AmalgamNeighbour, (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X) →
    HR8Kind e t f N₁ .linear6 → HR8Kind e t f N₂ .omegaPlus8 →
    ∀ e₁ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₁ N₁ →
    ∀ e₂ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₂ N₂ →
    ∀ ΦA : e6ScLevi K e6A5Nodes →* G, ΦA.range = neighbourCore e N₁ →
      ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) →
      (∀ x y : e6ScLevi K e6A5Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) →
      IsLeviNormalizedA e₁ ΦA →
    ∃ ε : K ≃+* K, ∀ ΦY : spinGroup (quadPlus 4 K) →* G, ΦY.range = neighbourCore e N₂ →
      Function.Injective ΦY → (∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g)) →
      (∀ s, ΦY (spinIota hw.card_eq hf s) = levi6Hom e₂ ε s) →
      (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
            e6A3Nodes_subset_e6D4Nodes x) ∨
        (∀ x y : e6ScLevi K e6A3Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
            scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
              scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
                e6A3Nodes_subset_e6D4Nodes y)

end Inputs

section Reduction

theorem e6GraphRowSpinLeviInput_of_agree_pieceComm (hA : E6GraphRowSpinAgreeInput)
    (hP : E6RowPieceCommInput) : E6GraphRowSpinLeviInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ ΦA hrA hkA hcA hnA
  obtain ⟨ε, H⟩ := hA G L K e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ ΦA hrA hkA hcA hnA
  have hk : E6RowKinds e t f := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl ⟨h6, h8⟩, Or.inr ⟨h8, h6⟩]
  refine ⟨ε, 1, fun ΦY hrY hiY hc hn => ?_⟩
  have hn' : ∀ s, ΦY (spinIota hw.card_eq hf s) = levi6Hom e₂ ε s := by
    intro s
    rw [hn s, one_mul, inv_one, mul_one]
  exact ⟨H ΦY hrY hiY hc hn', comm_of_pieceComm hw.card_eq hf hN he₁ he₂ hrA hnA hrY hn'
    (hP G L K e t f hw hf hk)⟩

end Reduction

end CFSG.SeitzReduction.F4Pilot
