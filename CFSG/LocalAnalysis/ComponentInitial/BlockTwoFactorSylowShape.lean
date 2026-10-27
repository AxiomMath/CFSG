module

public import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactor

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

variable {G : Type*} [Group G]

section Tools

variable [Finite G]

omit [Finite G] in
@[expose] noncomputable def equivMapOfInfKerEqBot {A : Type*} [Group A] (f : G →* A)
    {W : Subgroup G} (hW : W ⊓ f.ker = ⊥) : W ≃* W.map f :=
  (MonoidHom.ofInjective (f := f.domRestrict W) (by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ W ⊓ f.ker := Subgroup.mem_inf.2 ⟨x.2, hx⟩
    rw [hW, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range]))

omit [Finite G] in
theorem quotientActionHom_apply_mk {X N : Subgroup G} (hN : N ≤ normalizer (X : Set G)) (n : N)
    (x : X) : quotientActionHom X hN n (QuotientGroup.mk' (center X) x) =
      QuotientGroup.mk' (center X) (normalizerConjHom X (Subgroup.inclusion hN n) x) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ x

end Tools

end CFSG.LocalAnalysis.ComponentInitial
