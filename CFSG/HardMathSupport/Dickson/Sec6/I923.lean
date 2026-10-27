module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Spor
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldHolds

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Y923_LieRest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    CFSG.Open.GLAPPrimeCore 3 Y = ⊥ → (∀ s : ℕ, ¬ IsTypeL2 s Y) →
    ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits →
      LieModel (Y ⧸ Subgroup.center Y) t n p f →
      ∀ α : MulAut Y, α ^ 3 = 1 → α ∉ innAutDerived Y →
        ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J →
          ∀ r0 : ℕ, 10 ≤ r0 → ¬ IsTypeL2 r0 (barOf 3 J)


theorem y923_of_lieRest (h : Y923_LieRest) : Y923 := by
  intro Y _ _ hq hK hcore α h3 hnot J hJ r0 hr0 hT
  by_cases hL2 : ∃ s, IsTypeL2 s Y
  · obtain ⟨s, hs⟩ := hL2
    exact y923_of_typeL2 CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds l2Aut3Classification_holds l2FieldFixed_holds
      l2CentreThree_holds hq hcore hs h3 hnot hJ hr0 hT
  · exfalso
    have hL2' : ∀ s, ¬ IsTypeL2 s Y := fun s hs => hL2 ⟨s, hs⟩
    haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
    have hnab := exists_not_comm_of_quasisimple hq
    have hcat : Catalog (Y ⧸ Subgroup.center Y) :=
      CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge _ hnab (inCatalog_of_quasisimple hK hq)
    have hlie : ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits →
        LieModel (Y ⧸ Subgroup.center Y) t n p f → False := fun t n p f hadm ht hm =>
      h Y hq hcore hL2' t n p f hadm ht hm α h3 hnot J hJ r0 hr0 hT
    rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hexc | ⟨s, ⟨e⟩⟩
    ·
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    ·
      by_cases h6 : n = 6
      · subst h6
        exact hnot (mem_innAutDerived_of_card_outer hq e not_three_dvd_card_outer_alt_six h3)
      · exact hnot (mem_innAutDerived_alt_ne_six hq hn h6 e h3)
    ·
      have htag : t ∈ classicalTags := by
        have := CFSG.Milestones.statedClassicalModel_tag_mem _ t n p f hm
        simpa [classicalTags] using this
      exact hlie t n p f hm.1 (by rintro rfl; simp [classicalTags] at htag) (Or.inl ⟨htag, hm⟩)
    ·
      rcases hexc with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
      · exact hlie t 0 p f hm.1 (by rintro rfl; simp [chevalleyExceptionalTags] at ht)
          (Or.inr (Or.inl ⟨rfl, ht, hm⟩))
      · by_cases htits : t = .Tits
        · subst htits
          exact hnot (mem_innAutDerived_of_card_outer hq (MulEquiv.refl _)
            (not_three_dvd_card_outer_tits hm) h3)
        · exact hlie t 0 p f hm.1 htits (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)))
      · obtain ⟨hp2, a, ha, -, -, -, hf, -⟩ := id hm
        subst hp2
        exact hlie .twistedB2 0 2 f ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, hf⟩, by omega⟩
          (by simp) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩)))
    ·
      exact hnot (mem_innAutDerived_of_card_outer hq (MulEquiv.refl _)
        (not_three_dvd_card_outer_sporadic hnab e) h3)

theorem input9_2_3_of_lieRest (h : Y923_LieRest) : Input9_2_3 innAutDerivedVocab :=
  input9_2_3_of_Y (y923_of_lieRest h)

end CFSG.HardMathSupport.Dickson.Sec6.I923
