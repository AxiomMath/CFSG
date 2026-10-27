module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLPsl
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLRoots
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLCenter
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped commutatorElement

set_option linter.unusedSectionVars false


@[expose] def ExcTLA2Facts (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] {γ δ : Fin τ.rank → ℤ}, IsRoot τ γ → IsRoot τ δ → IsRoot τ (γ + δ) →
    ¬ IsRoot τ (γ - δ) → ¬ IsRoot τ ((2 : ℤ) • γ + δ) → ¬ IsRoot τ (γ + (2 : ℤ) • δ) →
    (∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ∀ c d : K,
      pinnedX τ K γ c * pinnedX τ K δ d * pinnedX τ K γ (-c) * pinnedX τ K δ (-d) =
        pinnedX τ K (γ + δ) ((e : K) * c * d)) ∧
    ∀ s t u : K, Commute (pinnedX τ K γ s) (pinnedX τ K (γ + δ) u) ∧
      Commute (pinnedX τ K δ t) (pinnedX τ K (γ + δ) u)

theorem excTLA2Facts_of_ne_G2 {τ : Tag} (hτ : τ ≠ .G2) : ExcTLA2Facts τ := by
  intro K _ γ δ hγ hδ hsum h1 h2 h3
  obtain ⟨e, he, hcomm⟩ := excTL_a2_commutator hτ hγ hδ hsum h1 h2 h3
  exact ⟨⟨e, he, fun c d => hcomm K c d⟩, excTL_a2_commute hτ hγ hδ hsum h2 h3 K⟩

theorem excTLInner_of_a2Facts {τ : Tag} (hfacts : ExcTLA2Facts τ) : ExcTLInner τ := by
  intro K _ _ h4 M _ χ i hA2 _hperf q _hq hL2
  obtain ⟨γ, hγ, δ, hδ, hsum, h1, h2, h3⟩ := hA2
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγr := hΨ.isRoot γ hγ
  have hδr := hΨ.isRoot δ hδ
  have hs : γ + δ ∈ componentRoots χ i := hΨ.add_mem γ hγ δ hδ hsum
  have hns : -(γ + δ) ∈ componentRoots χ i := hΨ.neg_mem _ hs
  obtain ⟨⟨e, he, hcomm⟩, hcom⟩ := hfacts K hγr hδr hsum h1 h2 h3
  have he0 : (e : K) ≠ 0 := by rcases he with rfl | rfl <;> simp
  obtain ⟨F, _, _, _, ⟨φ⟩⟩ := hL2
  refine excTL_false_of_heis φ (H := Multiplicative K) ?_ (excTLHom hγ) (excTLHom hδ)
    (excTLElt hs (1 : K)) ?_ ?_ ?_ ?_
  · rw [Nat.card_congr Multiplicative.toAdd]
    omega
  · exact excTL_elt_not_central hs hns one_ne_zero
  · intro s
    exact Subtype.ext (hcom (Multiplicative.toAdd s) 0 1).1.eq
  · intro t
    exact Subtype.ext (hcom 0 (Multiplicative.toAdd t) 1).2.eq
  · intro s t hs1 ht1
    have hs0 : Multiplicative.toAdd s ≠ 0 := fun h => hs1 (by simpa using h)
    have ht0 : Multiplicative.toAdd t ≠ 0 := fun h => ht1 (by simpa using h)
    have key : ⁅excTLHom hγ s, excTLHom hδ t⁆ =
        excTLElt hs ((e : K) * Multiplicative.toAdd s * Multiplicative.toAdd t) := by
      refine Subtype.ext ?_
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, excTLHom_coe, excTLElt_coe, pinnedX_neg]
      exact hcomm _ _
    rw [key]
    exact excTL_elt_not_central hs hns (mul_ne_zero (mul_ne_zero he0 hs0) ht0)

theorem excTLInner_of_ne_G2 {τ : Tag} (hτ : τ ≠ .G2) : ExcTLInner τ :=
  excTLInner_of_a2Facts (excTLA2Facts_of_ne_G2 hτ)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
