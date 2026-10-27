module

public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.IVK33D
public import CFSG.GH74.GLS.Stage2.Local.IVK33E

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

@[expose] def IVK33Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (k = Kind.mcl ∨ k = Kind.ly) → Prop21h z

theorem ivk33_of_rest (hrest : IVK33Rest) : IVK_3_3_lift := by
  intro G _ _ z k S hctx
  have hdata := hctx.data
  cases hdata with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, hshape⟩ := h.shape
    exact prop21h_of_g2 hshape
  | m12 h =>
    have hz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hctx.central.1, pow_two] at this
    exact prop21h_of_m12 hz h
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hP⟩ := h
    exact prop21h_of_pair hP.pair
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hP⟩ := h
    exact prop21h_of_pair hP.pair
  | mcl h => exact hrest G z _ S hctx (Or.inl rfl)
  | ly h => exact hrest G z _ S hctx (Or.inr rfl)

theorem ivk33_rest : IVK33Rest := by
  intro G _ _ z k S hctx hk
  have hdata := hctx.data
  cases hdata with
  | g2 h => rcases hk with h' | h' <;> cases h'
  | m12 h => rcases hk with h' | h' <;> cases h'
  | psp4 h => rcases hk with h' | h' <;> cases h'
  | l4 ε h => rcases hk with h' | h' <;> cases h'
  | mcl h =>
    obtain ⟨n, hn, hS⟩ := h
    exact prop21h_of_sporadic (by omega) hS
  | ly h =>
    obtain ⟨n, hn, hS⟩ := h
    exact prop21h_of_sporadic (by omega) hS

theorem ivk33 : IVK_3_3_lift := ivk33_of_rest ivk33_rest

end CFSG.GH74.GLS.Stage2.Local
