module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RootSpanMap

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false

private theorem eqvGen_map {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

section Orbit

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem iform_rho (γ δ : Fin τ.rank → ℤ) : iform (S.ρ γ) (S.ρ δ) = iform γ δ :=
  S.frob.iform_eq γ δ

private noncomputable def outerRhoSigma (hT : rootDiagUnit τ a ∈ S.D.torus) :
    kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) :=
  fun γ => ⟨S.ρ γ, outer_rho_mem_kernelRoots S hT γ.2⟩

theorem outer_rho_symm_mem_kernelRoots (hT : rootDiagUnit τ a ∈ S.D.torus)
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ kernelRoots (rootCharHom a)) :
    S.ρ.symm δ ∈ kernelRoots (rootCharHom a) := by
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1
  have hmaps : Set.MapsTo (S.ρ : (Fin τ.rank → ℤ) → _) (kernelRoots (rootCharHom a))
      (kernelRoots (rootCharHom a)) := fun γ hγ => outer_rho_mem_kernelRoots S hT hγ
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 S.ρ.injective.injOn
  obtain ⟨γ, hγ, rfl⟩ := hbij.surjOn hδ
  simpa using hγ

theorem outer_exists_image_component (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    ∃ j : KernelComponent (rootCharHom a),
      (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) j := by
  obtain ⟨γ₀, rfl⟩ := Quotient.exists_rep i
  refine ⟨⟦outerRhoSigma S hT γ₀⟧, ?_⟩
  have hrel : ∀ x y : kernelRoots (rootCharHom a),
      ((x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0) →
      ((outerRhoSigma S hT x : Fin τ.rank → ℤ) ⬝ᵥ
        (τ.symmetrizedCartan *ᵥ (outerRhoSigma S hT y : Fin τ.rank → ℤ)) ≠ 0) := by
    intro x y h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    exact fun h0 => h (by rw [← iform_rho S]; exact h0)
  have hrel' : ∀ x y : kernelRoots (rootCharHom a),
      ((x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0) →
      ((⟨S.ρ.symm x, outer_rho_symm_mem_kernelRoots S hT x.2⟩ :
          kernelRoots (rootCharHom a)) : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ
        ((⟨S.ρ.symm y, outer_rho_symm_mem_kernelRoots S hT y.2⟩ :
          kernelRoots (rootCharHom a)) : Fin τ.rank → ℤ)) ≠ 0 := by
    intro x y h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    simp only
    have := iform_rho S (S.ρ.symm x) (S.ρ.symm y)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]
    exact h
  ext δ
  constructor
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    refine ⟨outer_rho_mem_kernelRoots S hT hγ, ?_⟩
    have h1 : Relation.EqvGen _ (⟨γ, hγ⟩ : kernelRoots (rootCharHom a)) γ₀ := Quotient.exact hγi
    exact Quotient.sound (eqvGen_map (R := fun α β : kernelRoots (rootCharHom a) =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (R' := fun α β : kernelRoots (rootCharHom a) =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (outerRhoSigma S hT) hrel h1)
  · rintro ⟨hδ, hδi⟩
    refine ⟨S.ρ.symm δ, ⟨outer_rho_symm_mem_kernelRoots S hT hδ, ?_⟩, by simp⟩
    have h1 : Relation.EqvGen _ (⟨δ, hδ⟩ : kernelRoots (rootCharHom a))
        (outerRhoSigma S hT γ₀) := Quotient.exact hδi
    have h2 := eqvGen_map (R := fun α β : kernelRoots (rootCharHom a) =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (R' := fun α β : kernelRoots (rootCharHom a) =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (fun x : kernelRoots (rootCharHom a) =>
      (⟨S.ρ.symm x, outer_rho_symm_mem_kernelRoots S hT x.2⟩ :
        kernelRoots (rootCharHom a))) hrel' h1
    refine Quotient.sound ?_
    have h3 : (⟨S.ρ.symm (outerRhoSigma S hT γ₀ : Fin τ.rank → ℤ),
        outer_rho_symm_mem_kernelRoots S hT (outerRhoSigma S hT γ₀).2⟩ :
          kernelRoots (rootCharHom a)) = γ₀ :=
      Subtype.ext (by simp [outerRhoSigma])
    rw [h3] at h2
    exact h2

theorem outer_exists_period (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    ∃ s : ℕ, 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1
  obtain ⟨d, hd, hfix⟩ := exists_iterate_eq_of_mapsTo hfin
    (fun γ hγ => outer_rho_mem_kernelRoots S hT hγ) S.ρ.injective.injOn
  refine ⟨d, hd, ?_⟩
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [hfix γ hγ.1]
    exact hγ
  · intro hδ
    exact ⟨δ, hδ, hfix δ hδ.1⟩

theorem outer_componentOrbitLength_spec (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i ∧
      ∀ k, 0 < k → k < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
          componentRoots (rootCharHom a) i := by
  have hne : {s : ℕ | 0 < s ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i}.Nonempty := outer_exists_period S hT i
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun k hk hks h => ?_⟩
  exact Nat.notMem_of_lt_sInf hks ⟨hk, h⟩

theorem outer_iterate_image_component (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (k : ℕ) :
    ∃ j : KernelComponent (rootCharHom a), componentRoots (rootCharHom a) j =
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i := by
  induction k with
  | zero => exact ⟨i, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨j', hj'⟩ := outer_exists_image_component S hT j
    refine ⟨j', ?_⟩
    rw [← hj', hj, Function.iterate_succ', Set.image_comp]

theorem componentOrbitLength_spec (hE : rootDiagUnit τ a ∈ S.E)
    (i : KernelComponent (rootCharHom a)) :
    0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i ∧
      ∀ k, 0 < k → k < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
          componentRoots (rootCharHom a) i :=
  outer_componentOrbitLength_spec S (S.E_le hE).1 i

theorem iterate_image_period {Ψ : Set (Fin τ.rank → ℤ)} {s : ℕ}
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ) (k : ℕ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ = (S.ρ : (Fin τ.rank → ℤ) → _)^[k % s] '' Ψ := by
  have hq : ∀ q : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[s * q] '' Ψ = Ψ := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add, Set.image_comp, hs, ih]
  conv_lhs => rw [← Nat.mod_add_div k s, Function.iterate_add, Set.image_comp, hq]

theorem map_rootSpan_step (T : Set (Fin τ.rank → ℤ)) (hT : ∀ γ ∈ T, IsRoot τ γ) :
    (rootSpan τ L T).map S.D.step =
      rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _) '' T) :=
  S.frob.map_rootSpan T hT

theorem outer_isRoot_of_mem_iterate_image (i : KernelComponent (rootCharHom a)) (k : ℕ)
    {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i) :
    IsRoot τ γ := by
  obtain ⟨δ, hδ, rfl⟩ := hγ
  exact S.iterate_isRoot k (isRoot_of_mem_componentRoots hδ)

theorem outer_commute_orbit_lt (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i) {k l : ℕ} (hkl : k < l) (hl : l < s) :
    ∀ x ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i),
      ∀ y ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i),
        x * y = y * x := by
  obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k
  obtain ⟨j', hj'⟩ := outer_iterate_image_component S hT i l
  have hne : j ≠ j' := by
    intro h
    subst h
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i := hj.symm.trans hj'
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[l - k] '' componentRoots (rootCharHom a) i) := by
      rw [Set.image_image]
      refine Set.image_congr fun x _ => ?_
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h2] at h1
    have h3 := (Set.image_injective.2 (S.ρ.injective.iterate k)) h1
    exact hmin (l - k) (by omega) (by omega) h3.symm
  have hbot := (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.2.1 j j'
    hne
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot
  intro x hx y hy
  have hxS : x ∈ componentRootSpan L (rootCharHom a) j := by
    have : componentRootSpan L (rootCharHom a) j =
        rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i) := by
      rw [← hj]; rfl
    rw [this]; exact hx
  have hyS : y ∈ componentRootSpan L (rootCharHom a) j' := by
    have : componentRootSpan L (rootCharHom a) j' =
        rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i) := by
      rw [← hj']; rfl
    rw [this]; exact hy
  have := Subgroup.mem_centralizer_iff.1 (hle hxS) y hyS
  exact this.symm

theorem val_add_one_eq {s : ℕ} [NeZero s] (k : ZMod s) : (k + 1).val = (k.val + 1) % s := by
  have h : (((k.val + 1 : ℕ)) : ZMod s) = k + 1 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast] at this
  exact this.symm

section Family

section Torus

variable (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {s : ℕ}
  [NeZero s]
  (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
    componentRoots (rootCharHom a) i)
  (hmin : ∀ k, 0 < k → k < s →
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i)

include hT hs hmin in
@[expose] noncomputable def outerOrbitFamily : CycFamily S.D.step s where
  S k := rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' componentRoots (rootCharHom a) i)
  map_eq k := by
    rw [map_rootSpan_step S _ (fun γ hγ => outer_isRoot_of_mem_iterate_image S i k.val hγ)]
    congr 1
    rw [← Set.image_comp, ← Function.iterate_succ', val_add_one_eq,
      ← iterate_image_period S hs (k.val + 1)]
  comm j k hjk x hx y hy := by
    have hne : j.val ≠ k.val := fun h => hjk (ZMod.val_injective s h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact outer_commute_orbit_lt S hT i hmin h (ZMod.val_lt k) x hx y hy
    · exact (outer_commute_orbit_lt S hT i hmin h (ZMod.val_lt j) y hy x hx).symm

include hT hs hmin in
theorem outerOrbitFamily_S (k : ZMod s) : (outerOrbitFamily S hT i hs hmin).S k =
    rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' componentRoots (rootCharHom a) i) :=
  rfl

include hT hs hmin in
theorem outerOrbitFamily_A : (outerOrbitFamily S hT i hs hmin).A =
    rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    refine rootSpan_mono ?_
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨k.val, δ, hδ, rfl⟩
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨m, δ, hδ, rfl⟩ := hγ
    have hk : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] δ ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[(m : ZMod s).val] '' componentRoots (rootCharHom a) i := by
      rw [ZMod.val_natCast, ← iterate_image_period S hs m]
      exact ⟨δ, hδ, rfl⟩
    exact le_trans (show rootSubgroup τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[m] δ) ≤
      rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[(m : ZMod s).val] ''
        componentRoots (rootCharHom a) i) from le_iSup₂_of_le _ hk le_rfl)
      (le_iSup (fun k : ZMod s => (outerOrbitFamily S hT i hs hmin).S k) (m : ZMod s))

end Torus

variable (hE : rootDiagUnit τ a ∈ S.E) (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
  (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
    componentRoots (rootCharHom a) i)
  (hmin : ∀ k, 0 < k → k < s → (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
    componentRoots (rootCharHom a) i)

end Family

end Orbit

end CFSG.HardMathSupport.Timmesfeld.LangTorus
