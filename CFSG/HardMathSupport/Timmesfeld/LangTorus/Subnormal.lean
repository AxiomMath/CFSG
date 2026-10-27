module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped commutatorElement
open Matrix

set_option linter.unusedSectionVars false


section Generic

theorem eqvGen_map {X : Type*} {r : X → X → Prop} (f : X → X)
    (hf : ∀ x y, r x y → r (f x) (f y)) {x y : X} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y := by
  refine ⟨fun h => ?_, eqvGen_map e fun x y h => (hr x y).2 h⟩
  have := eqvGen_map e.symm (fun a b h => (hr (e.symm a) (e.symm b)).1 (by simpa using h)) h
  simpa using this

theorem commutator_le_self_of_subgroup {G : Type*} [Group G] (N : Subgroup G) : ⁅N, N⁆ ≤ N :=
  Subgroup.commutator_le_self N

theorem conj_mem_commutator_self {G : Type*} [Group G] {N : Subgroup G} {g z : G} (hg : g ∈ N)
    (hz : z ∈ ⁅N, N⁆) : g * z * g⁻¹ ∈ ⁅N, N⁆ := by
  have h : ⁅N, N⁆ ≤ (⁅N, N⁆).comap (MulAut.conj g).toMonoidHom :=
    Subgroup.commutator_le.2 fun x hx y hy => by
      show g * ⁅x, y⁆ * g⁻¹ ∈ ⁅N, N⁆
      have e : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (N.mul_mem (N.mul_mem hg hx) (N.inv_mem hg))
        (N.mul_mem (N.mul_mem hg hy) (N.inv_mem hg))
  exact h hz

theorem isSubnormal_commutator_subgroupOf {G : Type*} [Group G] {N C : Subgroup G}
    (hN : (N.subgroupOf C).IsSubnormal) : ((⁅N, N⁆).subgroupOf C).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (H := (⁅N, N⁆).subgroupOf C) (K := N.subgroupOf C)
    (Subgroup.comap_mono (commutator_le_self_of_subgroup N)) ?_ hN
  refine Subgroup.Normal.isSubnormal ⟨fun x hx g => ?_⟩
  simp only [Subgroup.mem_subgroupOf] at hx ⊢
  have hg : ((g : ↥C) : G) ∈ N := g.2
  have h1 : (((g : ↥(N.subgroupOf C)) : ↥C) : G) ∈ N := hg
  exact conj_mem_commutator_self h1 hx

section Orbit

variable {τ : Tag} {L : Type} [Field L] {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}

theorem kernelComponent_eq_iff (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

theorem iform_iterate {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) = iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

theorem iterate_mem_kernelRoots {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) : (ρ : (Fin τ.rank → ℤ) → _)^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih => rw [Function.iterate_succ_apply']; exact hker _ ih

theorem rationalRoots_subset_kernelRoots {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    rationalRoots ρ χ i ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact iterate_mem_kernelRoots hker k hδ

theorem rationalRoots_closed {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ rationalRoots ρ χ i) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, rationalRoots_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ rationalRoots ρ χ i := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  let σ : kernelRoots χ → kernelRoots χ := fun x => ⟨ρ x, hker x x.2⟩
  have hσinj : Function.Injective σ := fun x y h =>
    Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : Equiv.Perm (kernelRoots χ) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have he_iter : ∀ (k : ℕ) (x : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = (ρ : (Fin τ.rank → ℤ) → _)^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show ρ (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = _
      rw [ih, Function.iterate_succ_apply']
  have hr : ∀ (k : ℕ) (x y : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ
          (τ.symmetrizedCartan *ᵥ (((e ^ k) y : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 ↔
        (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro k x y
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, he_iter, he_iter,
      iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ = ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [kernelComponent_eq_iff]
    refine (eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (kernelComponent_eq_iff _ _).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

end Orbit

end Generic

section Chain

variable {τ : Tag} {L : Type} [Field L]

theorem rootSpan_le_normalizer_of_closed {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ ⊆ kernelRoots χ)
    (hcl : ∀ γ (hγ : γ ∈ Ψ) β (hβ : β ∈ kernelRoots χ),
      (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, hΨ hγ⟩⟧ → β ∈ Ψ) :
    rootSpan τ L (kernelRoots χ) ≤ Subgroup.normalizer (rootSpan τ L Ψ : Set (ModGL τ L)) := by
  refine iSup₂_le fun β hβ => ?_
  by_cases hβΨ : β ∈ Ψ
  · exact (le_iSup₂_of_le (f := fun α (_ : α ∈ Ψ) => rootSubgroup τ L α) β hβΨ le_rfl).trans
      Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (rootSpan τ L Ψ : Set (ModGL τ L)))
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hne : (⟦⟨γ, hΨ hγ⟩⟧ : KernelComponent χ) ≠ ⟦⟨β, hβ⟩⟧ := fun h =>
      hβΨ (hcl γ hγ β hβ h.symm)
    exact (commute_of_mk_ne hne L x hx y hy).eq

theorem isSubnormal_kernelRootSpan (a : Fin τ.rank → Lˣ) :
    ((rootSpan τ L (kernelRoots (rootCharHom a))).subgroupOf
      (toralCentralizer τ L a)).IsSubnormal := by
  obtain ⟨-, hMn, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ L a
  have hRM : rootSpan τ L (kernelRoots (rootCharHom a)) ≤ toralRootGroup τ L a :=
    le_sup_right
  have h0 : ((toralRootGroup τ L a).subgroupOf (toralCentralizer τ L a)).IsSubnormal :=
    hMn.isSubnormal
  have hNR : toralRootGroup τ L a ≤ Subgroup.normalizer
      (rootSpan τ L (kernelRoots (rootCharHom a)) : Set (ModGL τ L)) :=
    sup_le (CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _
      fun _ hα => hα.1) Subgroup.le_normalizer
  exact isSubnormal_subgroupOf_step hRM h0 fun y hy r hr =>
    (Subgroup.mem_normalizer_iff.1 (hNR hy) r).1 hr

end Chain

theorem langSubnormal_of_mem_torus {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hdT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
      ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subgroupOf
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).IsSubnormal := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγ, h⟩
    refine ⟨(S.frob.isRoot_iff γ).2 hγ, ?_⟩
    have h' : rootChar a γ = 1 := h
    show rootChar a (S.ρ γ) = 1
    rw [S.frob.rootChar_eq a hdT γ hγ, h', one_pow]
  have hΨ : rationalRoots S.ρ (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
    rationalRoots_subset_kernelRoots hker i
  have hcl : ∀ γ (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) β
      (hβ : β ∈ kernelRoots (rootCharHom a)),
      (⟦⟨β, hβ⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨γ, hΨ hγ⟩⟧ →
        β ∈ rationalRoots S.ρ (rootCharHom a) i :=
    fun γ hγ β hβ h => rationalRoots_closed hker S.frob.iform_eq i hγ hβ h
  have hΓ : S.Γ ≤ adjointGroup τ L :=
    (commutator_le_self_of_subgroup S.D.model).trans inf_le_left
  have hcent : rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ≤
      Subgroup.centralizer {rootDiagUnit τ a} := rootSpan_le_centralizer a hΨ
  have hN : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} :=
    fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, hcent (Subgroup.mem_inf.1 hx).1⟩
  refine ⟨(commutator_le_self_of_subgroup _).trans hN, ?_⟩
  have hnorm := rootSpan_le_normalizer_of_closed (L := L) hΨ hcl
  have hsub : ((rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).subgroupOf
      (toralCentralizer τ L a)).IsSubnormal :=
    isSubnormal_subgroupOf_step
      (iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ kernelRoots (rootCharHom a)) =>
        rootSubgroup τ L α) α (hΨ hα) le_rfl)
      (isSubnormal_kernelRootSpan a) fun y hy x hx =>
        (Subgroup.mem_normalizer_iff.1 (hnorm hy) x).1 hx
  have h2 := isSubnormal_inf_subgroupOf hsub S.Γ
  have hTC : toralCentralizer τ L a ⊓ S.Γ =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    ext x
    simp only [toralCentralizer, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hΓ h.1, h.2⟩, h.1⟩⟩
  rw [hTC] at h2
  exact isSubnormal_commutator_subgroupOf h2

theorem langSubnormal_proved : LangSubnormal := fun _ _ _ _ _ S _ hE _ i =>
  langSubnormal_of_mem_torus S (S.E_le hE).1 i

end CFSG.HardMathSupport.Timmesfeld.LangTorus
