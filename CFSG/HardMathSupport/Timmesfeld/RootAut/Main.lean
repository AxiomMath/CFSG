module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
public import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import Certificates.Certificate13659

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {τ : Tag}

theorem rank_le_eight (τ : Tag) : τ.rank ≤ 8 := by
  cases τ <;> simp [Tag.rank]

@[expose] def toRat (γ : Fin τ.rank → ℤ) : Fin τ.rank → ℚ := fun i => (γ i : ℚ)

theorem toRat_sum {s : Finset (Fin τ.rank → ℤ)} (c : (Fin τ.rank → ℤ) → ℤ) :
    toRat (∑ β ∈ s, c β • β) = ∑ β ∈ s, (c β : ℚ) • toRat β := by
  funext i
  simp [toRat, Finset.sum_apply]

theorem linearIndependent_toRat {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    LinearIndependent ℚ fun β : simpleRoots Ψ => toRat (β : Fin τ.rank → ℤ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set c : (Fin τ.rank → ℤ) → ℝ := fun γ => if h : γ ∈ simpleRoots Ψ then (g ⟨γ, h⟩ : ℝ) else 0
    with hc
  have hreal : ∑ β ∈ simpleRoots Ψ, c β • toReal β = 0 := by
    funext j
    have h1 := congrArg (fun v : Fin τ.rank → ℚ => ((v j : ℚ) : ℝ)) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, toRat,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero] at h1
    rw [Finset.sum_apply, ← Finset.sum_coe_sort (simpleRoots Ψ)]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, toReal, hc, Finset.coe_mem,
      ↓reduceDIte]
    exact h1
  have := eq_zero_of_sum_smul_simpleRoots hΨ hreal i i.2
  simpa [hc] using this

theorem compRank_eq_card {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    compRank Ψ = (simpleRoots Ψ).card := by
  classical
  have hspan : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) =
      Submodule.span ℚ (Set.range fun β : simpleRoots Ψ => toRat (β : Fin τ.rank → ℤ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, hγ, rfl⟩
      obtain ⟨c, e⟩ := exists_coords hΨ hγ
      show toRat γ ∈ _
      rw [e, toRat_sum]
      refine Submodule.sum_mem _ fun β hβ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨⟨β, hβ⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨β, rfl⟩
      exact Submodule.subset_span ⟨β, simpleRoots_subset β.2, rfl⟩
  rw [compRank, hspan, finrank_span_eq_card (linearIndependent_toRat hΨ), Fintype.card_coe]

theorem compRank_le (Ψ : Set (Fin τ.rank → ℤ)) : compRank Ψ ≤ τ.rank := by
  rw [compRank]
  calc _ ≤ Module.finrank ℚ (Fin τ.rank → ℚ) := Submodule.finrank_le _
    _ = τ.rank := Module.finrank_fin_fun ℚ

theorem corootPair_isometry {Ψ : Set (Fin τ.rank → ℤ)} {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry Ψ f) {β γ : Fin τ.rank → ℤ} (hβ : β ∈ Ψ) (hγ : γ ∈ Ψ) :
    corootPair (f β) (f γ) = corootPair β γ := by
  rw [corootPair, corootPair, hf.iform_eq β hβ γ hγ, hf.iform_eq β hβ β hβ]

theorem componentWeylGroup_le (Ψ : Set (Fin τ.rank → ℤ)) :
    componentWeylGroup Ψ ≤ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
  Subgroup.closure_mono fun _ ⟨β, hβ, e⟩ => ⟨β, simpleRoots_subset hβ, e.symm⟩


theorem rootAutIsWeyl_of_cartan
    (hfin : ∀ (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)), IsRootComponent Ψ →
      TauCeti.IsFiniteType (Matrix.of fun β γ : simpleRoots Ψ =>
        corootPair (β : Fin τ.rank → ℤ) γ))
    (hconn : ∀ (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)), IsRootComponent Ψ → Ψ.Nonempty →
      (TauCeti.diagramGraph (Matrix.of fun β γ : simpleRoots Ψ =>
        corootPair (β : Fin τ.rank → ℤ) γ)).Connected) :
    RootAutIsWeyl := by
  classical
  intro τ Ψ hΨ hns σ hbij hform hneg
  rcases Ψ.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_mem _, fun γ hγ => absurd hγ (Set.notMem_empty γ)⟩
  have hf : IsIsometry Ψ σ := ⟨hbij, hform, hneg⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ fun γ => σ (w • γ) := hf.comp_smul hΨ hw
  suffices hfix : ∀ β ∈ simpleRoots Ψ, σ (w • β) = β by
    obtain ⟨u, hu, hσu⟩ := exists_smul_eq_of_isIsometry hΨ hf hw hfix
    exact ⟨u, componentWeylGroup_le Ψ hu, hσu⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (hfin τ Ψ hΨ).existsUnique_dynkinType (hconn τ Ψ hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcard]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨σ (w • (β : Fin τ.rank → ℤ)), hf'.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : σ (w • (β : Fin τ.rank → ℤ)) = σ (w • (γ : Fin τ.rank → ℤ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (hf'.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have hi := simpleRoots_subset (e.symm i).2
    have hj := simpleRoots_subset (e.symm j).2
    calc t.cartanMatrix (σ' i) (σ' j)
        = t.cartanMatrix (e (π (e.symm i))) (e (π (e.symm j))) := rfl
      _ = corootPair (π (e.symm i) : Fin τ.rank → ℤ) (π (e.symm j)) := (he' _ _).symm
      _ = corootPair (e.symm i : Fin τ.rank → ℤ) (e.symm j) := corootPair_isometry hf' hi hj
      _ = t.cartanMatrix (e (e.symm i)) (e (e.symm j)) := he' _ _
      _ = t.cartanMatrix i j := by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  ·
    have hok : rigidOK t = true := List.all_eq_true.1 Certificates.certificate13659.1 t hmem
    have h1 : σ' = 1 := eq_one_of_sepB hok hσ'M
    intro β hβ
    have h2 := congrArg (fun g : Equiv.Perm (Fin t.rank) => g (e ⟨β, hβ⟩)) h1
    simp only [hσ', Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at h2
    have h3 := congrArg Subtype.val (e.injective h2)
    simpa [hπe, hπ] using h3
  ·
    have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
    have hN : Ψ.ncard = t.numRoots := by
      rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]
    exfalso
    apply hns
    rcases numRoots_of_mem_countTypes hmem with h | h | h
    · exact Or.inl ⟨hrank ▸ h.1, by rw [hN, hrank]; exact h.2⟩
    · exact Or.inr (Or.inl ⟨hrank ▸ h.1, by rw [hN, hrank]; exact h.2⟩)
    · exact Or.inr (Or.inr ⟨hrank ▸ h.1, by rw [hN]; exact h.2⟩)

theorem rootAutIsWeyl_holds : RootAutIsWeyl :=
  rootAutIsWeyl_of_cartan (fun _ _ hΨ => Proving.isFiniteType_simpleRoots_corootPair hΨ)
    (fun _ _ hΨ hne => Proving.diagramGraph_simpleRoots_connected hΨ hne)

end CFSG.HardMathSupport.Timmesfeld.RootAut
