module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalFamilyKernel
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
set_option allowUnsafeReducibility true in
attribute [local reducible] Tag.rank

set_option backward.isDefEq.respectTransparency false in
theorem TwE6ToralCoords.iform_eq_zero_of_original_reflections_commute
    {n : ℕ} {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ)
    {r s : MulAut Bs} {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hne : α ≠ β) (hneg : α ≠ -β)
    (hr : ∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b)))
    (hs : ∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β (Multiplicative.toAdd (κ b)))
    (hcomm : r * s = s * r) : iform α β = 0 := by
  apply KGL.iform_eq_zero_of_commute hα hβ
  · intro h
    exact hne (KGL.kgExpVec_injective_of_isRoot hα hβ h)
  · intro h
    exact hneg (KGL.kgExpVec_injective_of_isRoot hα (IsRoot.neg hβ)
      (h.trans (KGL.kgExpVec_neg β).symm))
  · intro x hx
    have hxrange : ∃ b : ↥Bs, κ b = Multiplicative.ofAdd x := by
      rcases hκ.range with hall | hhyp
      · exact hall x
      · exact (hhyp x).2 hx
    obtain ⟨b, hb⟩ := hxrange
    have hb' : Multiplicative.toAdd (κ b) = x := congrArg Multiplicative.toAdd hb
    have hbs : r (s b) = s (r b) := congrArg (fun t : MulAut Bs => t b) hcomm
    have hcoord := congrArg (fun c : Bs => Multiplicative.toAdd (κ c)) hbs
    rw [hr, hs, hs, hr, hb'] at hcoord
    simpa only [ExcSplitRootGen.excRefl, KGL.adAct_rootReflection_eq_rootRefl hα,
      KGL.adAct_rootReflection_eq_rootRefl hβ] using hcoord

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
