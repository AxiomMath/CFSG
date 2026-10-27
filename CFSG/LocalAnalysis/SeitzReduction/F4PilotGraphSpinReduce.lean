module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinNormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamFinal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.EvenSmallLie
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphSpinReduceNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Inputs

@[expose] def E6GraphRowSpinTwistInput : Prop :=
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
      (∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g)) →
    ∃ δ : MulAut (spinGroup (quadPlus 4 K)), (∀ g, δ (spinD4Graph K g) = spinD4Graph K (δ g)) ∧
      ((∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict ((ΦY.comp δ.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
            e6A3Nodes_subset_e6D4Nodes x) ∨
        (∀ x y : e6ScLevi K e6A3Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
            scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
              scLeviRestrict ((ΦY.comp δ.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
                e6A3Nodes_subset_e6D4Nodes y)) ∧
      (∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute
        (scLeviRestrict ((ΦY.comp δ.toMonoidHom).comp (spinEquivD4 K).symm.toMonoidHom)
          one_subset_e6D4Nodes a)
        (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b))

end Inputs

theorem comp_trans_toMonoidHom {G : Type} [Group G] {K : Type} [Field K]
    (ΦY : spinGroup (quadPlus 4 K) →* G) (α₀ δ : MulAut (spinGroup (quadPlus 4 K))) :
    ΦY.comp (δ.trans α₀).toMonoidHom = (ΦY.comp α₀.toMonoidHom).comp δ.toMonoidHom :=
  MonoidHom.ext fun _ => rfl

section Reduction

theorem e6GraphRowSpinNormInput_of_twistInput (h : E6GraphRowSpinTwistInput) :
    E6GraphRowSpinNormInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ ΦA hrA hkA hcA hnA ΦY hrY hiY
  have hN₂ : N₂ ≠ .X' := by
    rcases hN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨α₀, hα₀⟩ := exists_conj_spinD4Graph hw hf e hN₂ h8 hrY hiY
  have hr₀ : (ΦY.comp α₀.toMonoidHom).range = neighbourCore e N₂ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 α₀.surjective, ← MonoidHom.range_eq_map,
      hrY]
  have hi₀ : Function.Injective (ΦY.comp α₀.toMonoidHom) := hiY.comp α₀.injective
  obtain ⟨δ, hδ, htw, hcomm⟩ := h G L K e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ ΦA hrA hkA hcA hnA
    (ΦY.comp α₀.toMonoidHom) hr₀ hi₀ (fun g => hα₀ g)
  refine ⟨δ.trans α₀, conj_x_of_conj_spinD4Graph (conj_spinD4Graph_comp hα₀ hδ), ?_, ?_⟩
  · rw [comp_trans_toMonoidHom]
    exact htw
  · rw [comp_trans_toMonoidHom]
    exact hcomm

end Reduction

end CFSG.SeitzReduction.F4Pilot
