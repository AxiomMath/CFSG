module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamANorm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)

local instance f4PilotGraphParamFinalNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Inputs

@[expose] def E6GraphRowSpinNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N₁ N₂ : AmalgamNeighbour, (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X) →
    HR8Kind e t f N₁ .linear6 → HR8Kind e t f N₂ .omegaPlus8 →
    ∀ e₁ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₁ N₁ →
    ∀ ΦA : e6ScLevi K e6A5Nodes →* G, ΦA.range = neighbourCore e N₁ →
      ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) →
      (∀ x y : e6ScLevi K e6A5Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) →
      IsLeviNormalizedA e₁ ΦA →
    ∀ ΦY : spinGroup (quadPlus 4 K) →* G, ΦY.range = neighbourCore e N₂ →
      Function.Injective ΦY →
    ∃ α : MulAut (spinGroup (quadPlus 4 K)),
      (∀ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∀ c : K,
        t * ΦY (α (SpinPlus.x 4 K three_le_rank_D4 γ c)) * t⁻¹ =
          ΦY (α (SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c))) ∧
      ((∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
            e6A3Nodes_subset_e6D4Nodes x) ∨
        (∀ x y : e6ScLevi K e6A3Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
            scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
              scLeviRestrict ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
                e6A3Nodes_subset_e6D4Nodes y)) ∧
      (∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute
        (scLeviRestrict ((ΦY.comp α.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
          one_subset_e6D4Nodes a)
        (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b))

end Inputs

end CFSG.SeitzReduction.F4Pilot
