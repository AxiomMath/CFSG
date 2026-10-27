module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Proving

section Diagram

set_option maxRecDepth 100000 in
theorem l154td4_perm_pow_six_A : ∀ σ : Equiv.Perm (Fin 4), (∀ p : Fin 4 × Fin 4,
    (CartanMatrix.A 4 (σ p.1) (σ p.2) : ℤ) = CartanMatrix.A 4 p.1 p.2) → σ ^ 6 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem l154td4_perm_pow_six_B : ∀ σ : Equiv.Perm (Fin 4), (∀ p : Fin 4 × Fin 4,
    (CartanMatrix.B 4 (σ p.1) (σ p.2) : ℤ) = CartanMatrix.B 4 p.1 p.2) → σ ^ 6 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem l154td4_perm_pow_six_C : ∀ σ : Equiv.Perm (Fin 4), (∀ p : Fin 4 × Fin 4,
    (CartanMatrix.C 4 (σ p.1) (σ p.2) : ℤ) = CartanMatrix.C 4 p.1 p.2) → σ ^ 6 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem l154td4_perm_pow_six_D : ∀ σ : Equiv.Perm (Fin 4), (∀ p : Fin 4 × Fin 4,
    (CartanMatrix.D 4 (σ p.1) (σ p.2) : ℤ) = CartanMatrix.D 4 p.1 p.2) → σ ^ 6 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem l154td4_perm_pow_six_F : ∀ σ : Equiv.Perm (Fin 4), (∀ p : Fin 4 × Fin 4,
    (CartanMatrix.F₄ (σ p.1) (σ p.2) : ℤ) = CartanMatrix.F₄ p.1 p.2) → σ ^ 6 = 1 := by
  decide

theorem l154td4_cartan_perm_pow_six {t : TauCeti.DynkinType} (hr : t.rank = 4)
    (σ : Equiv.Perm (Fin t.rank))
    (h : ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j) : σ ^ 6 = 1 := by
  cases t with
  | A n =>
    have hn : n = 4 := hr
    subst hn
    simp only [TauCeti.DynkinType.cartanMatrix_A] at h
    exact l154td4_perm_pow_six_A σ fun p => h p.1 p.2
  | B n =>
    have hn : n = 4 := hr
    subst hn
    simp only [TauCeti.DynkinType.cartanMatrix_B] at h
    exact l154td4_perm_pow_six_B σ fun p => h p.1 p.2
  | C n =>
    have hn : n = 4 := hr
    subst hn
    simp only [TauCeti.DynkinType.cartanMatrix_C] at h
    exact l154td4_perm_pow_six_C σ fun p => h p.1 p.2
  | D n =>
    have hn : n = 4 := hr
    subst hn
    simp only [TauCeti.DynkinType.cartanMatrix_D] at h
    exact l154td4_perm_pow_six_D σ fun p => h p.1 p.2
  | E6 => exact absurd hr (by decide)
  | E7 => exact absurd hr (by decide)
  | E8 => exact absurd hr (by decide)
  | F4 =>
    simp only [TauCeti.DynkinType.cartanMatrix_F4] at h
    exact l154td4_perm_pow_six_F σ fun p => h p.1 p.2
  | G2 => exact absurd hr (by decide)

end Diagram

section IsometryBasic

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {f g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem l154td4_isIsometry_id : IsIsometry Ψ (id : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) :=
  ⟨Set.bijOn_id Ψ, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem l154td4_isIsometry_comp (hf : IsIsometry Ψ f) (hg : IsIsometry Ψ g) :
    IsIsometry Ψ (f ∘ g) := by
  refine ⟨hf.bijOn.comp hg.bijOn, fun γ hγ δ hδ => ?_, fun γ hγ => ?_⟩
  · simp only [Function.comp]
    rw [hf.iform_eq _ (hg.bijOn.mapsTo hγ) _ (hg.bijOn.mapsTo hδ), hg.iform_eq γ hγ δ hδ]
  · simp only [Function.comp]
    rw [hg.neg γ hγ, hf.neg _ (hg.bijOn.mapsTo hγ)]

theorem l154td4_isIsometry_iterate (hf : IsIsometry Ψ f) (k : ℕ) : IsIsometry Ψ (f^[k]) := by
  induction k with
  | zero => exact l154td4_isIsometry_id
  | succ k ih => rw [Function.iterate_succ]; exact l154td4_isIsometry_comp ih hf

end IsometryBasic

section Isometry

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {f h : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem l154td4_iform_sub_add_smul_self (a b d : Fin τ.rank → ℤ) (c : ℤ) :
    iform (a - b + c • d) (a - b + c • d) =
      iform a a + iform b b + c * c * iform d d - 2 * iform a b + 2 * c * iform a d -
        2 * c * iform b d := by
  simp only [iform_add_left, iform_add_right, iform_sub_left, iform_sub_right, iform_smul_left,
    iform_smul_right]
  rw [iform_comm b a, iform_comm d a, iform_comm d b]
  ring

theorem l154td4_map_rootReflection (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    {β γ : Fin τ.rank → ℤ} (hβ : β ∈ Ψ) (hγ : γ ∈ Ψ) :
    f (rootReflection β • γ) = rootReflection (f β) • f γ := by
  have hfβ : f β ∈ Ψ := hf.bijOn.mapsTo hβ
  have hδ : rootReflection β • γ ∈ Ψ := hΨ.reflection_mem γ hγ β hβ
  have e1 : rootReflection β • γ = γ - corootPair β γ • β :=
    rootReflection_smul (hΨ.isRoot β hβ) γ
  have e2 : rootReflection (f β) • f γ = f γ - corootPair β γ • f β := by
    rw [rootReflection_smul (hΨ.isRoot _ hfβ) (f γ), corootPair_isometry hf hβ hγ]
  rw [e2]
  set δ := rootReflection β • γ with hδdef
  set c := corootPair β γ with hc
  have h0 : iform (f δ - f γ + c • f β) (f δ - f γ + c • f β) = 0 := by
    rw [l154td4_iform_sub_add_smul_self, hf.iform_eq δ hδ δ hδ, hf.iform_eq γ hγ γ hγ,
      hf.iform_eq β hβ β hβ, hf.iform_eq δ hδ γ hγ, hf.iform_eq δ hδ β hβ,
      hf.iform_eq γ hγ β hβ, ← l154td4_iform_sub_add_smul_self]
    have : δ - γ + c • β = 0 := by rw [e1]; abel
    rw [this]
    exact iform_self_eq_zero_of_zero
  have h1 := eq_zero_of_iform_self_eq_zero h0
  calc f δ = (f δ - f γ + c • f β) + (f γ - c • f β) := by abel
    _ = f γ - c • f β := by rw [h1, zero_add]

theorem l154td4_exists_weyl_conj (hΨ : IsRootComponent Ψ) (hh : IsIsometry Ψ h)
    (hΔ : ∀ β ∈ simpleRoots Ψ, h β ∈ simpleRoots Ψ) {v : WeylGroup τ}
    (hv : v ∈ componentWeylGroup Ψ) :
    ∃ v' ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, v • h γ = h (v' • γ) := by
  classical
  have hfinΔ : (simpleRoots Ψ : Set (Fin τ.rank → ℤ)).Finite := Finset.finite_toSet _
  have hbij : Set.BijOn h (simpleRoots Ψ : Set (Fin τ.rank → ℤ))
      (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) :=
    (Set.Finite.injOn_iff_bijOn_of_mapsTo hfinΔ (fun β hβ => hΔ β hβ)).1
      (hh.bijOn.injOn.mono fun β hβ => simpleRoots_subset hβ)
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    obtain ⟨β', hβ', hββ'⟩ := hbij.surjOn hβ
    refine ⟨rootReflection β', rootReflection_mem_componentWeylGroup hβ', fun γ hγ => ?_⟩
    rw [← hββ']
    exact (l154td4_map_rootReflection hΨ hh (simpleRoots_subset hβ') hγ).symm
  | one => exact ⟨1, one_mem _, fun γ _ => by simp only [one_smul]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', haγ⟩ := ha
    obtain ⟨b', hb', hbγ⟩ := hb
    refine ⟨a' * b', mul_mem ha' hb', fun γ hγ => ?_⟩
    rw [mul_smul, hbγ γ hγ, haγ _ (smul_mem_of_mem_componentWeylGroup hΨ hb' γ hγ), mul_smul]
  | inv a _ ha =>
    obtain ⟨a', ha', haγ⟩ := ha
    refine ⟨a'⁻¹, inv_mem ha', fun γ hγ => ?_⟩
    have hγ' : a'⁻¹ • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem ha') γ hγ
    have h1 := haγ _ hγ'
    rw [smul_inv_smul] at h1
    rw [← h1, inv_smul_smul]

end Isometry

section Main

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {f g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem l154td4_iterate_six_fixes_simpleRoots (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (hr : compRank Ψ = 4) (hg : IsIsometry Ψ g) (hΔ : ∀ β ∈ simpleRoots Ψ, g β ∈ simpleRoots Ψ) :
    ∀ β ∈ simpleRoots Ψ, g^[6] β = β := by
  classical
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
    (diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : t.rank = 4 := by rw [← hcard, ← compRank_eq_card hΨ, hr]
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β => ⟨g (β : Fin τ.rank → ℤ), hΔ β β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ hβγ
    have h' : g (β : Fin τ.rank → ℤ) = g (γ : Fin τ.rank → ℤ) := congrArg Subtype.val hβγ
    exact Subtype.ext (hg.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
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
      _ = corootPair (e.symm i : Fin τ.rank → ℤ) (e.symm j) := corootPair_isometry hg hi hj
      _ = t.cartanMatrix (e (e.symm i)) (e (e.symm j)) := he' _ _
      _ = t.cartanMatrix i j := by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h6 : σ' ^ 6 = 1 := l154td4_cartan_perm_pow_six hrank σ' hσ'M
  have hiter : ∀ (k : ℕ) (β : simpleRoots Ψ),
      ((σ' : Fin t.rank → Fin t.rank)^[k] (e β)) = e (π^[k] β) := by
    intro k
    induction k with
    | zero => intro β; rfl
    | succ k ih =>
      intro β
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp only [hσ', Equiv.trans_apply, Equiv.symm_apply_apply]
      rfl
  have hπk : ∀ (k : ℕ) (β : simpleRoots Ψ),
      ((π^[k] β : simpleRoots Ψ) : Fin τ.rank → ℤ) = g^[k] (β : Fin τ.rank → ℤ) := by
    intro k
    induction k with
    | zero => intro β; rfl
    | succ k ih => intro β; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  intro β hβ
  have h1 := hiter 6 ⟨β, hβ⟩
  rw [Equiv.Perm.iterate_eq_pow, h6, Equiv.Perm.coe_one, id_eq] at h1
  have h2 : π^[6] ⟨β, hβ⟩ = ⟨β, hβ⟩ := e.injective h1.symm
  have h3 := hπk 6 ⟨β, hβ⟩
  rw [h2] at h3
  exact h3.symm

theorem l154td4_twistInner_iterate_six (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (hr : compRank Ψ = 4) (hf : IsIsometry Ψ f) : twistInner Ψ (f^[6]) := by
  classical
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  set g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun γ => f (w • γ) with hgdef
  have hg : IsIsometry Ψ g := hf.comp_smul hΨ hw
  have hΔ : ∀ β ∈ simpleRoots Ψ, g β ∈ simpleRoots Ψ := fun β hβ =>
    hg.apply_mem_simpleRoots hΨ hpos hβ
  have hΔk : ∀ (k : ℕ), ∀ β ∈ simpleRoots Ψ, g^[k] β ∈ simpleRoots Ψ := by
    intro k
    induction k with
    | zero => exact fun β hβ => hβ
    | succ k ih => exact fun β hβ => by rw [Function.iterate_succ_apply]; exact ih _ (hΔ β hβ)
  have h6 := l154td4_iterate_six_fixes_simpleRoots hΨ hne hr hg hΔ
  have hfg : ∀ δ, f δ = g (w⁻¹ • δ) := fun δ => by simp only [hgdef, smul_inv_smul]
  have key : ∀ k : ℕ, ∃ u ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, f^[k] γ = g^[k] (u • γ) := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, fun γ _ => by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, huk⟩ := ih
      obtain ⟨v, hv, hvk⟩ := l154td4_exists_weyl_conj hΨ (l154td4_isIsometry_iterate hg k)
        (hΔk k) (inv_mem hw)
      refine ⟨v * u, mul_mem hv hu, fun γ hγ => ?_⟩
      have huγ : u • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ hu γ hγ
      rw [Function.iterate_succ_apply', huk γ hγ, hfg, hvk _ huγ, mul_smul,
        Function.iterate_succ_apply']
  obtain ⟨u, hu, huk⟩ := key 6
  refine ⟨u, componentWeylGroup_le Ψ hu, fun γ hγ => ?_⟩
  have huγ : u • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ hu γ hγ
  rw [huk γ hγ]
  exact (l154td4_isIsometry_iterate hg 6).eq_self_of_simpleRoots hΨ h6 huγ

end Main

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
