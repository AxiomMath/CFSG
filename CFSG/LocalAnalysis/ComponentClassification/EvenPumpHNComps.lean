module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNLeaf
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAutCore
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy transportAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.SolMax (fixedSubgroup_conj_eq)

@[expose] def CompNotHN (Y : Type) [Group Y] : Prop :=
  Nat.card (Y ⧸ center Y) ≠ 273030912000000

theorem not_isHNType_of_comps
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ σ : MulAut S, orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hin : ∀ t : S, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set S)) CompNotHN)
    (hout : ∀ α : MulAut S, α * α = 1 → α ∉ inner S →
      CompsSatisfy (Sporadic.Schreier.fixSub α) CompNotHN)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsHNType (P ⧸ Open.fusionZStar P) := by
  intro hH
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨hcomp, -⟩ := h.isComponent_of_oddCore (hcore σ hσ2)
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  obtain ⟨-, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hcomp.1
  have hLc : Nat.card (L ⧸ center L) = 273030912000000 := by
    rw [← Nat.card_congr eZ.toEquiv, card_of_isHNType hH]
  have key : ∀ {X : Type} [Group X] (φ : ↥(fixedSubgroup σ) ≃* X),
      ¬ CompNotHN ↥(L.map φ.toMonoidHom) := by
    intro X _ φ hne
    let ψ : ↥L ≃* ↥(L.map φ.toMonoidHom) := L.equivMapOfInjective φ.toMonoidHom φ.injective
    apply hne
    rw [← hLc]
    exact (Nat.card_congr
      (QuotientGroup.congr (center L) (center _) ψ (Subgroup.map_center_eq ψ)).toEquiv).symm
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    exact key φ (hin t ht2 _ (isComponent_map_mulEquiv φ hcomp))
  · have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    exact key φ (hout σ hσσ hout' _ (isComponent_map_mulEquiv φ hcomp))

theorem outer_compNotHN_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ α : MulAut (NativeSporadic.Carrier s), α ∈ inner (NativeSporadic.Carrier s))
    {G : Type} [Group G] (e : G ≃* NativeSporadic.Carrier s) (α : MulAut G)
    (hα : α ∉ inner G) : CompsSatisfy (Sporadic.Schreier.fixSub α) CompNotHN :=
  absurd (hinner (transportAut e α)) (RestrictedStd.Spor.transportAut_not_mem_inner e hα)

end CFSG.ComponentClassification.EvenPump
