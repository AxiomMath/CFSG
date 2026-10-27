module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourStableTag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighStable

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice

section LinearIndependent


theorem linearIndependent_toReal_simpleRoots_rhoImage {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ)
    (horth : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform γ (S.ρ δ) = 0) :
    LinearIndependent ℝ (fun x : simpleRoots Ψ ⊕ simpleRoots Ψ =>
      toReal (Sum.elim (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ))
        (fun β : simpleRoots Ψ => S.ρ (β : Fin τ.rank → ℤ)) x)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set A := ∑ β : simpleRoots Ψ, g (Sum.inl β) • toReal (β : Fin τ.rank → ℤ) with hA
  set B := ∑ β : simpleRoots Ψ, g (Sum.inr β) • toReal (S.ρ β) with hB
  have hAB : A + B = 0 := by
    rw [hA, hB, ← hg, Fintype.sum_sum_type]
    simp
  have horthAB : rform A B = 0 := by
    rw [hA, hB, rform_sum_left]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [rform_smul_left, rform_sum_right]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun γ _ => ?_)
    rw [rform_smul_right, rform_toReal,
      horth β (simpleRoots_subset β.2) γ (simpleRoots_subset γ.2)]
    simp
  have hA0 : A = 0 := by
    have hBA : B = -A := eq_neg_of_add_eq_zero_right hAB
    have h1 : rform A A = 0 := by
      have : rform A B = -rform A A := by
        rw [hBA]
        simp only [rform, Matrix.mulVec_neg, dotProduct_neg]
      linarith
    by_contra h
    have := rform_self_pos h
    linarith
  have hB0 : B = 0 := by rw [← hAB, hA0, zero_add]
  have hgA := (Fintype.linearIndependent_iff.1
    (linearIndependent_toReal_of_iform hΨ (f := id) fun _ _ _ _ => rfl))
    (fun β => g (Sum.inl β)) (by simpa [hA] using hA0)
  have hgB := (Fintype.linearIndependent_iff.1
    (linearIndependent_toReal_of_iform hΨ (f := S.ρ) fun β _ γ _ => S.frob.iform_eq β γ))
    (fun β => g (Sum.inr β)) (by simpa [hB] using hB0)
  rintro (β | β)
  · exact hgA β
  · exact hgB β

end LinearIndependent


theorem eight_le_rank_of_image_ne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i j : KernelComponent (rootCharHom a)) (hij : j ≠ i)
    (hj : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) j)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    8 ≤ τ.rank := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ componentRoots (rootCharHom a) j := fun γ hγ => by
    rw [← hj]
    exact ⟨γ, hγ, rfl⟩
  have horth : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform γ (S.ρ δ) = 0 := fun γ hγ δ hδ =>
    iform_eq_zero_of_mem_componentRoots (Ne.symm hij) hγ (hρΨ δ hδ)
  have hcard := (linearIndependent_toReal_simpleRoots_rhoImage S hΨ horth).fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_coe, Module.finrank_fin_fun] at hcard
  have hc := compRank_eq_card hΨ
  omega

theorem image_componentRoots_eq_of_twoD_rank_four_ne_eight {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) (hτ : τ ≠ .E8) :
    (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
  classical
  obtain ⟨j, hj⟩ := outer_exists_image_component S hT i
  by_cases hji : j = i
  · rw [hj, hji]
  · exfalso
    have h8 := eight_le_rank_of_image_ne S hT i j hji hj h4
    have htag := tag_simplyLaced_of_twistKind_twoD_rank_four S hT i hkind h4
    rcases htag with rfl | rfl | rfl | rfl
    · simp [Tag.rank] at h8
    · simp [Tag.rank] at h8
    · simp [Tag.rank] at h8
    · exact hτ rfl

@[expose] def RankFourTwoDE8Stable : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup .E8 L p)
    {a : Fin Tag.E8.rank → Lˣ}, rootDiagUnit .E8 a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .twoD →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i

theorem image_componentRoots_eq_of_twoD_rank_four (hE8 : RankFourTwoDE8Stable)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
  by_cases hτ : τ = .E8
  · subst hτ
    exact hE8 S hT i hkind h4
  · exact image_componentRoots_eq_of_twoD_rank_four_ne_eight S hT i hkind h4 hτ

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
