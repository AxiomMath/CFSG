module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinReduce

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphSpinMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Inputs

@[expose] def E6GraphRowSpinLeviInput : Prop :=
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
    ∃ (ε : K ≃+* K) (s₀ : StatedSp 3 K), ∀ ΦY : spinGroup (quadPlus 4 K) →* G,
      ΦY.range = neighbourCore e N₂ → Function.Injective ΦY →
      (∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g)) →
      (∀ s, ΦY (spinIota hw.card_eq hf s) = levi6Hom e₂ ε (s₀ * s * s₀⁻¹)) →
      ((∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
            e6A3Nodes_subset_e6D4Nodes x) ∨
        (∀ x y : e6ScLevi K e6A3Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
            scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
              scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
                e6A3Nodes_subset_e6D4Nodes y)) ∧
      (∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute
        (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes a)
        (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b))

end Inputs

theorem exists_isNeighbourFrame {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour}
    (hN : N ≠ .X') : ∃ e₂ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₂ N := by
  cases N with
  | X => exact ⟨e, rfl⟩
  | Y =>
    have hc : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    exact ⟨e.trans (graphAutF4 K).symm, hc, rfl⟩
  | X' => exact absurd rfl hN

section Reduction

theorem e6GraphRowSpinTwistInput_of_leviInput (h : E6GraphRowSpinLeviInput) :
    E6GraphRowSpinTwistInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ ΦA hrA hkA hcA hnA ΦY hrY hiY hc
  have hN₂ : N₂ ≠ .X' := by
    rcases hN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨e₂, he₂⟩ := exists_isNeighbourFrame e hN₂
  obtain ⟨ε, s₀, H⟩ := h G L K e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ ΦA hrA hkA hcA hnA
  obtain ⟨δ, hδ, hn⟩ := exists_comm_spinD4Graph_normalized hw hf e he₂ ε hrY hiY hc
  set c : MulAut (spinGroup (quadPlus 4 K)) := MulAut.conj (spinIota hw.card_eq hf s₀) with hcdef
  have hγs : spinD4Graph K (spinIota hw.card_eq hf s₀) = spinIota hw.card_eq hf s₀ :=
    (mem_range_spinIota_iff hw.card_eq hf _).1 ⟨s₀, rfl⟩
  have hcγ : ∀ g, c (spinD4Graph K g) = spinD4Graph K (c g) := by
    intro g
    rw [hcdef, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hγs]
  have hδc : ∀ g, (c.trans δ) (spinD4Graph K g) = spinD4Graph K ((c.trans δ) g) := by
    intro g
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hcγ, hδ]
  have hc' : ∀ g, t * ΦY ((c.trans δ) g) * t⁻¹ = ΦY ((c.trans δ) (spinD4Graph K g)) := by
    intro g
    rw [hδc, hc]
  have hr' : (ΦY.comp (c.trans δ).toMonoidHom).range = neighbourCore e N₂ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (c.trans δ).surjective,
      ← MonoidHom.range_eq_map, hrY]
  have hn' : ∀ s, (ΦY.comp (c.trans δ).toMonoidHom) (spinIota hw.card_eq hf s) =
      levi6Hom e₂ ε (s₀ * s * s₀⁻¹) := by
    intro s
    change ΦY (δ (c (spinIota hw.card_eq hf s))) = _
    rw [hcdef, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hn]
  obtain ⟨htw, hcomm⟩ := H (ΦY.comp (c.trans δ).toMonoidHom) hr'
    (hiY.comp (c.trans δ).injective) (fun g => hc' g) hn'
  exact ⟨c.trans δ, hδc, htw, hcomm⟩

theorem e6GraphRowSpinNormInput_of_leviInput (h : E6GraphRowSpinLeviInput) :
    E6GraphRowSpinNormInput :=
  e6GraphRowSpinNormInput_of_twistInput (e6GraphRowSpinTwistInput_of_leviInput h)

end Reduction

end CFSG.SeitzReduction.F4Pilot
