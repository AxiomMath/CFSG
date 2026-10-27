module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut

set_option linter.unusedSectionVars false

section Independence

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}

theorem rform_sum_self (s : Finset (Fin τ.rank → ℤ)) (g : (Fin τ.rank → ℤ) → ℝ)
    (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) :
    rform (∑ β ∈ s, g β • toReal (f β)) (∑ β ∈ s, g β • toReal (f β)) =
      ∑ β ∈ s, ∑ γ ∈ s, g β * g γ * (iform (f β) (f γ) : ℝ) := by
  rw [rform_sum_sum]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => by rw [rform_toReal]

theorem linearIndependent_toReal_of_iform (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : ∀ β ∈ simpleRoots Ψ, ∀ γ ∈ simpleRoots Ψ, iform (f β) (f γ) = iform β γ) :
    LinearIndependent ℝ fun β : simpleRoots Ψ => toReal (f (β : Fin τ.rank → ℤ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg β
  set c : (Fin τ.rank → ℤ) → ℝ := fun γ => if h : γ ∈ simpleRoots Ψ then g ⟨γ, h⟩ else 0
    with hc
  have hsum : ∀ h : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ,
      ∑ γ : simpleRoots Ψ, g γ • toReal (h (γ : Fin τ.rank → ℤ)) =
        ∑ γ ∈ simpleRoots Ψ, c γ • toReal (h γ) := by
    intro h
    rw [← Finset.sum_coe_sort (simpleRoots Ψ)]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp [hc]
  have hv : ∑ γ ∈ simpleRoots Ψ, c γ • toReal (f γ) = 0 := by rw [← hsum f]; exact hg
  have hu : rform (∑ γ ∈ simpleRoots Ψ, c γ • toReal γ) (∑ γ ∈ simpleRoots Ψ, c γ • toReal γ) =
      0 := by
    have h1 := rform_sum_self (simpleRoots Ψ) c f
    have h2 := rform_sum_self (simpleRoots Ψ) c id
    rw [hv, show rform 0 0 = 0 by simp [rform]] at h1
    simp only [id] at h2
    rw [h2, ← h1.symm]
    refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun δ hδ => ?_
    rw [hf γ hγ δ hδ]
  have hu0 : ∑ γ ∈ simpleRoots Ψ, c γ • toReal γ = 0 := by
    by_contra h
    have := rform_self_pos h
    linarith
  have := eq_zero_of_sum_smul_simpleRoots hΨ hu0 β β.2
  simpa [hc] using this

end Independence

section Stable

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem LangSetup.image_componentRoots_eq_of_five_leT
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
  classical
  obtain ⟨j, hj⟩ := outer_exists_image_component S hT i
  by_cases hij : i = j
  · rw [hj, hij]
  exfalso
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ componentRoots (rootCharHom a) j := fun γ hγ => by
    rw [← hj]
    exact ⟨γ, hγ, rfl⟩
  set v : simpleRoots Ψ ⊕ simpleRoots Ψ → Fin τ.rank → ℝ := fun x =>
    Sum.elim (fun β : simpleRoots Ψ => toReal (β : Fin τ.rank → ℤ))
      (fun β : simpleRoots Ψ => toReal (S.ρ β)) x with hv
  have hind : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set A := ∑ β : simpleRoots Ψ, g (Sum.inl β) • toReal (β : Fin τ.rank → ℤ) with hA
    set B := ∑ β : simpleRoots Ψ, g (Sum.inr β) • toReal (S.ρ β) with hB
    have hAB : A + B = 0 := by
      rw [hA, hB, ← hg, Fintype.sum_sum_type]
      simp [hv]
    have horth : rform A B = 0 := by
      rw [hA, hB, rform_sum_left]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [rform_smul_left, rform_sum_right]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun γ _ => ?_)
      rw [rform_smul_right, rform_toReal,
        iform_eq_zero_of_mem_componentRoots hij (simpleRoots_subset β.2)
          (hρΨ _ (simpleRoots_subset γ.2))]
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
      (linearIndependent_toReal_of_iform hΨ (f := S.ρ) fun β _ γ _ => iform_rho S β γ))
      (fun β => g (Sum.inr β)) (by simpa [hB] using hB0)
    rintro (β | β)
    · exact hgA β
    · exact hgB β
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_coe, Module.finrank_fin_fun] at hcard
  have hc := compRank_eq_card hΨ
  have h8 := rank_le_eight τ
  omega

theorem LangSetup.componentOrbitLength_eq_one_of_five_leT (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} :=
    ⟨one_pos, by rw [Function.iterate_one]; exact S.image_componentRoots_eq_of_five_leT hT i h5⟩
  refine le_antisymm (Nat.sInf_le h1) ?_
  have hne : Set.Nonempty {s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} := ⟨1, h1⟩
  exact (Nat.sInf_mem hne).1

theorem LangSetup.rationalRoots_eq_of_five_leT (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  have hst := S.image_componentRoots_eq_of_five_leT hT i h5
  have hmem : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k generalizing δ with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (hmem δ hδ)
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem LangSetup.twoD_factsT (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ¬ twistInner (componentRoots (rootCharHom a) i) S.ρ ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) := by
  classical
  have hs := S.componentOrbitLength_eq_one_of_five_leT hT i h5
  unfold twistKind at hkind
  rw [hs, Function.iterate_one] at hkind
  split_ifs at hkind with h1 h2 h3
  exact ⟨h1, h3.2⟩

end Stable

end CFSG.HardMathSupport.Timmesfeld.LangTorus
