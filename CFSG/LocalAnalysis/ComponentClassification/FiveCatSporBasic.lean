module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenTwo
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporData

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def NoFive (Y : Type) [Group Y] : Prop := IsEmpty (Y ≃* alternatingGroup (Fin 5))

@[expose] def FiveSporClauseFor (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) → False

theorem fivePumpSporClause_of_clauseFor {s : TauCeti.SporadicName} (h : FiveSporClauseFor s) :
    FivePumpSporClause s := by
  intro S _ _ hs hna e σ P hP hZ eP _
  haveI := hs
  exact (h S hna e σ P hP hZ eP).elim

theorem fiveTwoLayerSporClause_of_clauseFor {s : TauCeti.SporadicName} (h : FiveSporClauseFor s) :
    FiveTwoLayerSporClause s := by
  intro S _ _ hs hna e σ P₁ P₂ h₁ _ _ hZ₁ _ e₁ _ _
  haveI := hs
  exact (h S hna e σ P₁ h₁ hZ₁ e₁).elim

theorem false_of_noFive_comps {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ σ : MulAut S, orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hin : ∀ t : S, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set S)) NoFive)
    (hout : ∀ α : MulAut S, α * α = 1 → α ∉ inner S →
      CompsSatisfy (Sporadic.Schreier.fixSub α) NoFive)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h (hcore σ hσ2) hex
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    exact (hin t ht2 _ (LocalCores.isComponent_map_mulEquiv φ hcomp)).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))
  · have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    exact (hout σ hσσ hout' _ (LocalCores.isComponent_map_mulEquiv φ hcomp)).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))

theorem fiveSpor_of_comps {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) NoFive)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) NoFive) :
    FiveSporClauseFor s := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex ⟨eP⟩
  exact false_of_noFive_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ)
    (hin S inferInstance hna ⟨e⟩) (hout S inferInstance hna ⟨e⟩) h hex eP

theorem smallCentralQuotient_of_equiv_alt_five {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : RestrictedStd.SmallCentralQuotient Y := by
  have hZ : center Y = ⊥ := Even.center_eq_bot_of_equiv_alt_five e
  let f : Y ⧸ center Y ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  refine Or.inl ⟨5, 1, Nat.prime_five, by norm_num, le_rfl, by norm_num, ?_⟩
  exact Or.inl ⟨by decide,
    LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _ ⟨f⟩⟩

theorem noFive_of_not_smallCentralQuotient {Y : Type} [Group Y]
    (h : ¬ RestrictedStd.SmallCentralQuotient Y) : NoFive Y :=
  ⟨fun e => h (smallCentralQuotient_of_equiv_alt_five e)⟩

theorem fiveSpor_of_sporCompData {s : TauCeti.SporadicName}
    (h : HarrisLit.SporCompData s) : FiveSporClauseFor s :=
  fiveSpor_of_comps h.oddCore
    (fun G _ _ hG hna e t ht =>
      (h.inner G hG hna e t ht).mono fun Y _ hY => noFive_of_not_smallCentralQuotient hY)
    (fun G _ _ hG hna e α hα2 hα =>
      (h.outer G hG hna e α hα2 hα).mono fun Y _ hY => noFive_of_not_smallCentralQuotient hY)

theorem false_of_not_dvd_fixed_card {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5))
    (hc : ¬ 60 ∣ Nat.card (fixedSubgroup σ)) : False := by
  apply hc
  have h1 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 60 := by
    rw [Nat.card_congr eP.toEquiv]
    exact Even.card_alt_five (MulEquiv.refl _)
  rw [← h1]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.2.1)

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
