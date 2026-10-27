module

public import CFSG.GH74.GLS.C3.Layer1.St1P89E

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.P89

@[expose] def B_prop89_realize : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Prop51 G → St1Thm5 G → ∀ (x : G) (S U : Subgroup G) (u : G) (K W : Subgroup G),
      Config8 x S U u K W → HasL2Model (kBar K) (fun q => q = 9) →
        pRank 2 ↥(W ⊓ CxK u K) = 1 →
          ∃ (T P Q : Subgroup G) (z f r s a : G),
            P = T ⊓ K ∧ Q = T ⊓ CxK u K ∧ Cfg89T G T P Q u z x f r s ∧ Cfg89S G T u S a ∧
              ((∀ q ∈ Q, q = 1 ∨ q = u) → ∃ n1 n2 : G, n1 ∈ K ∧ n2 ∈ K ∧
                n1 * u * n1⁻¹ = u ∧ n1 * f * n1⁻¹ = f ∧ n1 * z * n1⁻¹ = s ∧ n1 * s * n1⁻¹ = z ∧
                n2 * u * n2⁻¹ = u ∧ n2 * f * n2⁻¹ = f ∧ n2 * z * n2⁻¹ = z ∧ n2 * s * n2⁻¹ = z * s)

theorem b_st1_prop89_of_realize (h : B_prop89_realize) : B_st1_prop89 := by
  intro G _ _ hG hN T7 P41 P51 T5 x S U u K W hc hK hQ
  obtain ⟨T, P, Q, z, f, r, s, a, -, -, c, sc, hsmall⟩ := h G hG hN T7 P41 P51 T5 x S U u K W hc hK hQ
  refine c.false_of_cfg89 sc ?_
  intro hQ'
  obtain ⟨n1, n2, -, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsmall hQ'
  exact ⟨n1, n2, h1, h2, h3, h4, h5, h6, h7, h8⟩

end CFSG.GH74.GLS
