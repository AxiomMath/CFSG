module

public import CFSG.GH74.Generic.S45.LPump
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup

section Vert

variable {G : Type} [Group G]

theorem exists_J_of_vertical {v : G} {W : Subgroup G} (hWH : W ≤ centralizer ({v} : Set G))
    {J : Subgroup (CentralizerBar v)} (hWJ : barSub v W ≤ J) :
    ∃ J₁ : Subgroup G, W ≤ J₁ ∧ J₁ ≤ centralizer ({v} : Set G) ∧ barSub v J₁ = J := by
  refine ⟨(J.comap (proj v)).map (centralizer ({v} : Set G)).subtype, ?_,
    Subgroup.map_subtype_le _, ?_⟩
  · intro w hw
    exact ⟨⟨w, hWH hw⟩, hWJ (proj_mem_barSub (hWH hw) hw), rfl⟩
  · unfold barSub
    rw [show ((J.comap (proj v)).map (centralizer ({v} : Set G)).subtype).subgroupOf
        (centralizer ({v} : Set G)) = J.comap (proj v) from
      Subgroup.comap_map_eq_self_of_injective (centralizer ({v} : Set G)).subtype_injective _]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J

end Vert

@[expose] def B_S45_vertical : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T →
      ∀ v : G, v ∈ T → v ∈ Pre x K → v ≠ 1 →
      ∀ W : Subgroup G, W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) →
        (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal →
        IsSimpleGroup ↥W → (∃ a b : ↥W, a * b ≠ b * a) → HasL2Model ↥W Odd →
        ∃ J : Subgroup (CentralizerBar v), IsComponent J ∧ barSub v W ≤ J

@[expose] def B_S45_pumpStructV : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T →
      ∀ v : G, v ∈ T → v ∈ Pre x K → v ≠ 1 →
        ∃ W : Subgroup G,
          W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) ∧
          (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal ∧
          IsSimpleGroup ↥W ∧ (∃ a b : ↥W, a * b ≠ b * a) ∧ HasL2Model ↥W Odd ∧
          ∃ J : Subgroup (CentralizerBar v), IsComponent J ∧ barSub v W ≤ J

theorem b_S45_pumpStructV_of_leaves
    (hl : B_S45_lift) (hv : B_S45_vertical) :
    B_S45_pumpStructV := by
  intro G _ _ hsimple hnab hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1
  obtain ⟨K₀, h1, h2, h3, h4, h5⟩ := hl G hsimple hnab hgen hKGH x hx K hKc hj hnot T hT
  have hvC : v ∈ centralizer ({x} : Set G) := hvK.1
  have hvK' : piC x v ∈ K := hvK.2
  have hv2 : v * v = 1 := hT.sq v hvT
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hvK₀ : v ∈ K₀ := mem_lift_of_involution h1 h2 h4 h5 hvC hvK' hv2
  obtain ⟨W, hWY, hWn, hWs, hWnab, hWL⟩ :=
    exists_W_of_lift (kCent_of_isJ1OrRee hj) h1 h2 h3 h4 h5 hvK₀ hvord
  obtain ⟨J, hJ, hWJ⟩ :=
    hv G hsimple hnab hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1 W hWY hWn hWs hWnab hWL
  exact ⟨W, hWY, hWn, hWs, hWnab, hWL, J, hJ, hWJ⟩

end CFSG.GH74.Generic.S45
