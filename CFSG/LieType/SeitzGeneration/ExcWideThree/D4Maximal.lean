module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBigCell
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxEntry
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.PairLemma
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section D4Maximal


theorem eq_top_of_irrational_rootElt_D4 {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : ∀ F : Subfield K, k ≤ F → F = k ∨ F = ⊤) (H : Subgroup ↥(adjointGroup Tag.D4 K))
    (hrat : ∀ (γ : Fin Tag.D4.rank → ℤ), IsRoot Tag.D4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ H)
    (γ₀ : Fin Tag.D4.rank → ℤ) (hγ₀ : IsRoot Tag.D4 γ₀) (t : K) (ht : t ∉ k)
    (hmem : xPar (rootOperatorFamily Tag.D4) γ₀ t ∈ H) : H = ⊤ := by
  have hw := weylElement_one_mem_of_rat k H hrat
  have huniv := fun {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) (hδ : IsRoot Tag.D4 δ)
    (u : K) => xPar_mem_iff_of_roots H hw cartanD4_connected hγ hδ u
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_D4_neighbour (K := K)
  have hil : Tag.D4.cartan (⟨0, by decide⟩ : Fin Tag.D4.rank) ⟨2, by decide⟩ = -1 := by decide
  let S : Subring K :=
    { carrier := {u | ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ →
        xPar (rootOperatorFamily Tag.D4) γ u ∈ H}
      zero_mem' := fun γ _ => by simpa [xPar_zero] using H.one_mem
      one_mem' := fun γ hγ => hrat γ hγ 1 k.one_mem
      add_mem' := fun {a b} ha hb γ hγ => by
        rw [xPar_add]
        exact H.mul_mem (ha γ hγ) (hb γ hγ)
      neg_mem' := fun {a} ha γ hγ => by
        rw [← xPar_neg]
        exact H.inv_mem (ha γ hγ)
      mul_mem' := fun {a b} ha hb γ hγ => by
        have h1 := xPar_mul_mem_of_commutator H hε hcomm
          (ha _ (isRoot_single Tag.D4 _)) (hb _ (isRoot_single Tag.D4 _))
        exact (huniv (isRoot_single_add_single hil) hγ _).1 h1 }
  have hS : S = ⊤ := by
    refine eq_top_of_subring k hk S (fun c hc γ hγ => hrat γ hγ c hc) ht ?_
    intro γ hγ
    exact (huniv hγ₀ hγ t).1 hmem
  refine eq_top_of_forall_xPar_mem H fun γ hγ c => ?_
  have : c ∈ S := by rw [hS]; trivial
  exact this γ hγ

theorem exists_irrational_rootElt_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) (g : ↥(adjointGroup Tag.D4 K))
    (hg : g ∉ subfieldGroup Tag.D4 σ) :
    ∃ r ∈ subfieldGroup Tag.D4 σ, ∃ r' ∈ subfieldGroup Tag.D4 σ,
      ∃ (γ : Fin Tag.D4.rank → ℤ) (_ : IsRoot Tag.D4 γ) (t : K), t ∉ fixSubfield σ ∧
        xPar (rootOperatorFamily Tag.D4) γ t ∈
          Subgroup.closure ((subfieldGroup Tag.D4 σ : Set ↥(adjointGroup Tag.D4 K)) ∪
            ((subfieldGroup Tag.D4 σ).map (MulAut.conj (r * g * r')).toMonoidHom :
              Set ↥(adjointGroup Tag.D4 K))) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot Tag.D4
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_sl d4SimplyLaced σ hD hθ g hg
  have hne0 : entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμ, hψ⟩ := bigCell'_all hθ (r * g * r') hne0
  set H := Subgroup.closure ((subfieldGroup Tag.D4 σ : Set ↥(adjointGroup Tag.D4 K)) ∪
    ((subfieldGroup Tag.D4 σ).map (MulAut.conj (r * g * r')).toMonoidHom :
      Set ↥(adjointGroup Tag.D4 K))) with hH
  have hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ H := fun c hc => by
    rw [(hψ c).1]
    exact Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup Tag.D4 σ θ hc))
  have hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ H := fun c hc => by
    rw [(hψ c).2]
    exact Subgroup.subset_closure (Or.inr ⟨xPar (rootOperatorFamily Tag.D4) θ c,
      xPar_mem_subfieldGroup Tag.D4 σ θ hc, by simp [MulAut.conj_apply, mul_assoc]⟩)
  have hlam : μ₁ * μ₂ ∉ fixSubfield σ := by
    rcases hμ with h | h
    · rw [h]; exact hbad
    · rw [h]; exact fun hm => hbad (by simpa using (fixSubfield σ).neg_mem hm)
  have hfull := sl2_hom_mem_of_pair σ hp hp2 hσ hD ψ μ₁ μ₂ hμ₁ hlam hu hl
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    have := hp.one_lt
    omega
  obtain ⟨t, ht⟩ : ∃ t : K, σ t ≠ t := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext fun x => by simpa using h x)
  refine ⟨r, hr, r', hr', θ, hθ.1, t, fun h' => ht ((mem_fixSubfield σ).1 h'), ?_⟩
  rw [← (hψ t).1]
  exact hfull t

theorem subfieldMaximal_D4_of_card_ne_two {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hk2 : Nat.card (fixSubfield σ) ≠ 2)
    (M : Subgroup ↥(adjointGroup Tag.D4 K)) (hRM : subfieldGroup Tag.D4 σ ≤ M) :
    M = subfieldGroup Tag.D4 σ ∨ M = ⊤ := by
  have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
    by_cases h2 : ringChar K = 2
    · exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd σ h2).resolve_left hk2)
    · exact Or.inl h2
  by_cases hM : M = subfieldGroup Tag.D4 σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup Tag.D4 σ := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  obtain ⟨r, hr, r', hr', γ, hγ, t, ht, hmem⟩ :=
    exists_irrational_rootElt_D4 σ hp hp2 hσ hD g hgR
  set H := Subgroup.closure ((subfieldGroup Tag.D4 σ : Set ↥(adjointGroup Tag.D4 K)) ∪
    ((subfieldGroup Tag.D4 σ).map (MulAut.conj (r * g * r')).toMonoidHom :
      Set ↥(adjointGroup Tag.D4 K))) with hH
  have hgg : r * g * r' ∈ M := mul_mem (mul_mem (hRM hr) hgM) (hRM hr')
  have hHM : H ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hRM hx
    · exact M.mul_mem (M.mul_mem hgg (hRM hy)) (M.inv_mem hgg)
  have hRH : ∀ γ, IsRoot Tag.D4 γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ H := fun γ _ c hc =>
    Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup Tag.D4 σ γ hc))
  have hHtop : H = ⊤ := eq_top_of_irrational_rootElt_D4 (fixSubfield σ)
    (fun F hF => subfield_eq_or_top σ hp hσ F hF) H hRH γ hγ t ht hmem
  exact eq_top_iff.2 (hHtop ▸ hHM)

end D4Maximal

end CFSG.LieType.SeitzGeneration.ExcWideThree
