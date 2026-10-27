module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Alt
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Descent
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts

@[expose] def I1431SporRest : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (NativeSporadic.SporadicRep S ∨ ∃ p f : ℕ, ReeTitsModel S .Tits p f) →
    ∀ ψ : MulAut S, ψ ^ 3 = 1 → ψ ≠ 1 → ∀ A : Subgroup S, GLAPComponent 3 (fixSub ψ) A →
      ∀ q0 : ℕ, 4 ≤ q0 → ¬ IsTypeL2 (q0 ^ 3) (barOf 3 A)

@[expose] def I1431LieRest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y)
    (q : ℕ), Y1431Cfg d4Vocab Y Â ξ J q →
    (∃ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f ∧ t ≠ .Tits ∧
      LieModel (Y ⧸ Subgroup.center Y) t n p f) →
    ∀ q0 : ℕ, 4 ≤ q0 → q = q0 ^ 3 → Y1431Concl Y Â ξ J q

@[expose] def I1431D4Rest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y)
    (q : ℕ), Y1431Cfg innAutDerivedVocab Y Â ξ J q → IsD4Type Y → ∀ e ∈ Â, e ∈ innerAut Y

theorem residual_of_d4 (h : I1431D4Rest) : Input14_31_4Residual innAutDerivedVocab d4Vocab := by
  intro G _ _ I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq hq3 hq8 hfld hA' a ha
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf (inf_le_left : I ⊓ Cs x ≤ I) hJ
  have haN : a ∈ Subgroup.normalizer (I : Set G) := hB (hAB ha)
  refine ⟨haN, ?_⟩
  obtain ⟨hh, hmem⟩ := hA' a ha
  by_cases hd : IsD4Type (barOf 3 I)
  · have hcfg := cfg_of_ambient innAutDerivedVocab hI hK hB hrk hE hc hAB hx hA hT hJ₁ hq hq3 hq8
      hA' hfld
    have := h _ _ _ _ _ hcfg hd (barAut 3 I ⟨a, haN⟩) (mem_ahat.2 ⟨a, ha, haN, rfl⟩)
    show barAut 3 I ⟨a, haN⟩ ∈ d4Vocab.innDiag (barOf 3 I)
    simp only [d4Vocab, if_pos hd]
    exact this
  · show barAut 3 I ⟨a, haN⟩ ∈ d4Vocab.innDiag (barOf 3 I)
    simp only [d4Vocab, if_neg hd]
    exact hmem

section Dispatch


theorem y1431_of_rest (h5 : I1431SporRest) (h6 : I1431LieRest) : Y1431 d4Vocab := by
  intro Y _ _ Â ξ J q c
  have hU := CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
  have hF := CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds
  have hq := c.quasisimple
  obtain ⟨q0, hq0, hqq⟩ := cfg_cube hU hF c
  have hξ3 : ξ ^ 3 = 1 := c.elemAbelian.2 ξ c.mem
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnab := CFSG.HardMathSupport.Dickson.Sec6.I923.exists_not_comm_of_quasisimple hq
  have hcat : Catalog (Y ⧸ Subgroup.center Y) :=
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge _ hnab
      (CFSG.HardMathSupport.Dickson.Sec6.I923.inCatalog_of_quasisimple c.kgroup hq)
  have hspor : (NativeSporadic.SporadicRep (Y ⧸ Subgroup.center Y) ∨
      ∃ p f : ℕ, ReeTitsModel (Y ⧸ Subgroup.center Y) .Tits p f) → Y1431Concl Y Â ξ J q := by
    intro hs
    obtain ⟨A, hA, hAL2⟩ := exists_comp_typeL2_quotient ξ c.comp (hqq ▸ c.typeL2)
    refine (h5 (Y ⧸ Subgroup.center Y) hs (centerDescend Y ξ) ?_ ?_ A hA q0 hq0 hAL2).elim
    · rw [← map_pow, hξ3, map_one]
    · intro h1
      exact c.ne_one (eq_one_of_centerDescend_eq_one hq h1)
  have hlie : ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits →
      LieModel (Y ⧸ Subgroup.center Y) t n p f → Y1431Concl Y Â ξ J q := fun t n p f hadm ht hm =>
    h6 Y Â ξ J q c ⟨t, n, p, f, hadm, ht, hm⟩ q0 hq0 hqq
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hexc | hs
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  ·
    exact (false_of_alt hU hF c hn e).elim
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
        exact hspor (Or.inr ⟨p, f, hm⟩)
      · exact hlie t 0 p f hm.1 htits (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)))
    · obtain ⟨hp2, a, ha, -, -, -, hf, -⟩ := id hm
      subst hp2
      exact hlie .twistedB2 0 2 f ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, hf⟩, by omega⟩
        (by simp) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩)))
  ·
    exact hspor (Or.inl hs)

theorem input14_31_4_d4_of_rest (h5 : I1431SporRest) (h6 : I1431LieRest) :
    Input14_31_4 d4Vocab :=
  input14_31_4_of_Y (y1431_of_rest h5 h6)

theorem input14_31_4_of_rest (h5 : I1431SporRest) (h6 : I1431LieRest) (h4 : I1431D4Rest) :
    Input14_31_4 innAutDerivedVocab :=
  input14_31_4_of_residual (input14_31_4_d4_of_rest h5 h6) (residual_of_d4 h4)

end Dispatch

end CFSG.HardMathSupport.Dickson.Sec6.I1431
