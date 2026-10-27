module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma111a
public import CFSG.GH74.GLS.Stage4.T6X.T6Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6X

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Order

variable {N : T2N3 G} {u : G} {p m n : ℕ}

theorem K₁_sec_X₂R₂ (h : T6CtxW N u p) :
    (∀ k ∈ N.K₁, ∀ a ∈ R₂ N p, k * a * k⁻¹ ∈ R₂ N p) ∧
      ∀ k ∈ N.K₁, ∀ b ∈ N.X₂, k * b * k⁻¹ ∈ N.X₂ :=
  ⟨fun k hk a ha => R₂_norm N p (K₁_le_M₂ h hk) ha,
    fun k hk b hb => by rw [K₁_cent_X₂ h hk hb]; exact hb⟩

end Order

end CFSG.GH74.GLS.Stage4.Rest.T6X
