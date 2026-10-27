module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Leaf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy transportAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def CompNotA10 (Y : Type) [Group Y] : Prop :=
  Nat.card (Y ⧸ center Y) ≠ 1814400

theorem not_isA10Type_of_comps {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ σ : MulAut S, orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hin : ∀ t : S, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set S)) CompNotA10)
    (hout : ∀ α : MulAut S, α * α = 1 → α ∉ inner S →
      CompsSatisfy (Sporadic.Schreier.fixSub α) CompNotA10)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsA10Type (P ⧸ Open.fusionZStar P) := by
  intro hA
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore (hcore σ hσ2)
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hLc : Nat.card (L ⧸ center L) = 1814400 := by
    rw [← Nat.card_congr eZ.toEquiv, card_of_isA10Type hA]
  have key : ∀ {X : Type} [Group X] (φ : ↥(fixedSubgroup σ) ≃* X),
      ¬ CompNotA10 ↥(L.map φ.toMonoidHom) := by
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
      exact SolMax.fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    exact key φ (hin t ht2 _ (isComponent_map_mulEquiv φ hcomp))
  · have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    exact key φ (hout σ hσσ hout' _ (isComponent_map_mulEquiv φ hcomp))

@[expose] def A10SporClauseFor (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    ¬ IsA10Type (↥P ⧸ Open.fusionZStar ↥P)

theorem a10SporClauseFor_of_comps {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) CompNotA10)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) CompNotA10) :
    A10SporClauseFor s := by
  intro S _ _ _ hna ⟨e⟩ σ P h
  exact not_isA10Type_of_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ)
    (hin S inferInstance hna ⟨e⟩) (hout S inferInstance hna ⟨e⟩) h

theorem outer_compNotA10_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ α : MulAut (NativeSporadic.Carrier s), α ∈ inner (NativeSporadic.Carrier s))
    (G : Type) [Group G] [Finite G] (_ : IsSimpleGroup G) (_ : ∃ x y : G, x * y ≠ y * x)
    (hG : Nonempty (G ≃* NativeSporadic.Carrier s)) (α : MulAut G) (_ : α * α = 1)
    (hα : α ∉ inner G) : CompsSatisfy (Sporadic.Schreier.fixSub α) CompNotA10 := by
  obtain ⟨e⟩ := hG
  exact absurd (hinner (transportAut e α)) (RestrictedStd.Spor.transportAut_not_mem_inner e hα)

theorem a10SporClauseFor_of_card {s : TauCeti.SporadicName}
    (hs : ¬ 1814400 ∣ Nat.card (NativeSporadic.Carrier s)) : A10SporClauseFor s := by
  intro S _ _ _ _ ⟨e⟩ σ P _ hA
  obtain ⟨eA⟩ := hA
  apply hs
  have h1 := card_dvd_of_fusionZStar_equiv eA.toEquiv
  rw [card_of_isA10Type ⟨MulEquiv.refl _⟩, Nat.card_congr e.toEquiv] at h1
  exact h1

end CFSG.ComponentClassification.EvenPump
