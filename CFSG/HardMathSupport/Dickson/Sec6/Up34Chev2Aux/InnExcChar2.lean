module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInnerA2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

section TwoRoots

variable {τ : Tag}

theorem forall_eq_or_eq_neg_of_ncard_two {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (h2 : Ψ.ncard = 2) : ∀ α ∈ Ψ, ∀ δ ∈ Ψ, δ = α ∨ δ = -α := by
  classical
  intro α hα δ hδ
  have hfin : Ψ.Finite := Set.finite_of_ncard_pos (by omega)
  have hne : α ≠ -α := by
    intro h
    have hr := iform_self_pos_of_isRoot (hΨ.isRoot α hα)
    have h0 : α = 0 := by
      funext j
      have := congrFun h j
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    rw [h0] at hr
    simp [iform] at hr
  have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hα
    · exact hΨ.neg_mem _ hα
  have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
  have heq : ({α, -α} : Set (Fin τ.rank → ℤ)) = Ψ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, h2]) hfin
  rw [← heq] at hδ
  rcases hδ with h | h
  · exact Or.inl h
  · exact Or.inr h

end TwoRoots

section Kinds

set_option linter.unusedSectionVars false


theorem char2Hrat_inner {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hs : RDSize τ)
    (hg : RDGlue τ) : Char2Hrat τ .inner := by
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL34
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  rcases hs L a hap i with h2 | h6 | h14
  · exfalso
    exact inner_a1_false D (forall_eq_or_eq_neg_of_ncard_two hΨ h2) hL34
  · exact inner_a2_central hT hap h1 D hg h6 hL34
  · exact (inner_big_false hτ D h14 hL34).elim

theorem char2Hrat_twoD_of_no24 {τ : Tag} (hr : τ.rank ≤ 4)
    (h24 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin τ.rank → Lˣ), (∀ j, a j ^ 3 = 1) →
      ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard ≠ 24) :
    Char2Hrat τ .twoD := by
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL34
  exfalso
  obtain ⟨-, h4, hcard⟩ := twoD_kind_unpack hk
  have hrk := compRank_le_rank (τ := τ) (componentRoots (rootCharHom a) i)
  have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
  apply h24 L a hap i
  rw [hcard, h4']

theorem char2Hrat_exc_of_no24 {τ : Tag} (hr : τ.rank ≤ 4)
    (h24 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin τ.rank → Lˣ), (∀ j, a j ^ 3 = 1) →
      ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard ≠ 24) :
    Char2Hrat τ .exc := by
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL34
  exfalso
  obtain ⟨-, h⟩ := exc_kind hk
  have hrk := compRank_le_rank (τ := τ) (componentRoots (rootCharHom a) i)
  rcases h with ⟨h6, -⟩ | ⟨-, h24', -⟩
  · omega
  · exact h24 L a hap i h24'

end Kinds

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
