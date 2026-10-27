module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Maschke

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MonoidAlgebra Representation

section Semilinear

variable {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  {ε ε' : R →+* R} [RingHomInvPair ε ε'] [RingHomInvPair ε' ε]

def semilinearConjEnd (ψ : M ≃ₛₗ[ε] M') (f : Module.End R M') : Module.End R M where
  toFun x := ψ.symm (f (ψ x))
  map_add' x y := by simp
  map_smul' a x := by
    simp only [RingHom.id_apply, map_smulₛₗ]
    rw [RingHomInvPair.comp_apply_eq₂]

lemma apply_semilinearConjEnd (ψ : M ≃ₛₗ[ε] M') (f : Module.End R M') (x : M) :
    ψ (semilinearConjEnd ψ f x) = f (ψ x) := by simp [semilinearConjEnd]

lemma isFullyInvariant_map_of_semilinearEquiv (ψ : M ≃ₛₗ[ε] M') {p : Submodule R M}
    (hp : p.IsFullyInvariant) : (p.map (ψ : M →ₛₗ[ε] M')).IsFullyInvariant := fun f x hx => by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  exact Submodule.mem_comap.2 (Submodule.mem_map.2
    ⟨semilinearConjEnd ψ f y, hp _ hy, apply_semilinearConjEnd ψ f y⟩)

lemma isSemisimpleModule_of_semilinearEquiv (ψ : M ≃ₛₗ[ε] M') [IsSemisimpleModule R M] :
    IsSemisimpleModule R M' :=
  { (Submodule.orderIsoMapComap ψ).complementedLattice with }

lemma isIsotypic_of_semilinearEquiv (ψ : M ≃ₛₗ[ε] M') [IsSemisimpleModule R M]
    (h : IsIsotypic R M) : IsIsotypic R M' := by
  have := isSemisimpleModule_of_semilinearEquiv ψ
  rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top] at h ⊢
  intro q hq
  rcases h _ (isFullyInvariant_map_of_semilinearEquiv ψ.symm hq) with h1 | h1
  · exact Or.inl ((Submodule.map_eq_bot_iff (e := ψ.symm)).1 h1)
  · refine Or.inr ?_
    have h2 : (q.map (ψ.symm : M' →ₛₗ[ε'] M)).map (ψ : M →ₛₗ[ε] M') = q :=
      (Submodule.map_symm_eq_iff ψ).mp rfl
    rw [h1] at h2
    simpa using h2.symm

lemma map_mem_isotypicComponents [IsSemisimpleModule R M] (ψ : M ≃ₛₗ[ε] M')
    {c : Submodule R M} (hc : c ∈ isotypicComponents R M) :
    c.map (ψ : M →ₛₗ[ε] M') ∈ isotypicComponents R M' := by
  have := isSemisimpleModule_of_semilinearEquiv ψ (R := R) (M := M) (M' := M')
  rw [mem_isotypicComponents_iff] at hc ⊢
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨isIsotypic_of_semilinearEquiv (ψ.submoduleMap c) h1,
    isFullyInvariant_map_of_semilinearEquiv ψ h2, ?_⟩
  simpa [Submodule.map_eq_bot_iff] using h3

end Semilinear

section Comparable

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

lemma eq_of_mem_isotypicComponents_of_le {c d : Submodule R M}
    (hc : c ∈ isotypicComponents R M) (hd : d ∈ isotypicComponents R M) (hcd : c ≤ d) : c = d := by
  by_contra hne
  have hdisj : Disjoint c (sSup (isotypicComponents R M \ {c})) :=
    sSupIndep_isotypicComponents R M hc
  have hle : d ≤ sSup (isotypicComponents R M \ {c}) :=
    le_sSup ⟨hd, by simpa using Ne.symm hne⟩
  have hbot : c = ⊥ := by simpa using (hdisj.mono_right hle).eq_bot_of_le hcd
  obtain ⟨S, hS, rfl⟩ := hc
  exact absurd hbot (bot_lt_isotypicComponent S).ne'

end Comparable

section MapsSup

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

lemma Submodule.map_sSup (f : M →ₗ[R] M₂) (s : Set (Submodule R M)) :
    (sSup s).map f = sSup (Submodule.map f '' s) := by
  rw [sSup_eq_iSup', Submodule.map_iSup, sSup_image']

end MapsSup

attribute [local instance] RingHomInvPair.of_ringEquiv

local instance ringHomInvPairSymmSelf {R : Type*} [Semiring R] (e : R ≃+* R) :
    RingHomInvPair (e.symm : R →+* R) (e : R →+* R) :=
  RingHomInvPair.symm (e : R →+* R) (e.symm : R →+* R)

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

@[expose] noncomputable def resSubgroup (ρ : Representation k G V) (N : Subgroup G) :
    Representation k N V := ρ.comp N.subtype

@[simp] lemma resSubgroup_apply (ρ : Representation k G V) (N : Subgroup G) (n : N) :
    resSubgroup ρ N n = ρ (n : G) := rfl

noncomputable def conjAlg (k : Type*) [Field k] {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (g : G) : MonoidAlgebra k N ≃+* MonoidAlgebra k N :=
  (MonoidAlgebra.domCongr k k (MulAut.conjNormal g)).toRingEquiv

@[simp] lemma conjAlg_of (N : Subgroup G) [N.Normal] (g : G) (n : N) :
    conjAlg k N g (MonoidAlgebra.of k N n) = MonoidAlgebra.of k N (MulAut.conjNormal g n) := by
  simp [conjAlg, MonoidAlgebra.of_apply]

@[simp] lemma conjAlg_smul (N : Subgroup G) [N.Normal] (g : G) (c : k) (r : MonoidAlgebra k N) :
    conjAlg k N g (c • r) = c • conjAlg k N g r := by simp [conjAlg]

variable (ρ : Representation k G V) (N : Subgroup G)

lemma rho_asAlgebraHom_conjAlg [N.Normal] (g : G) (r : MonoidAlgebra k N) (x : V) :
    ρ g ((resSubgroup ρ N).asAlgebraHom r x)
      = (resSubgroup ρ N).asAlgebraHom (conjAlg k N g r) (ρ g x) := by
  induction r using MonoidAlgebra.induction_on with
  | of n =>
      rw [conjAlg_of, Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
      change ρ g (ρ (n : G) x) = ρ ((MulAut.conjNormal g n : N) : G) (ρ g x)
      rw [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
        ← map_mul]
      congr 2
      rw [mul_assoc (g * (n : G)), inv_mul_cancel, mul_one]
  | add r s hr hs => simp [hr, hs]
  | smul c r hr => simp [hr]

variable [N.Normal]

noncomputable def conjEquiv (g : G) :
    (resSubgroup ρ N).asModule
      ≃ₛₗ[(conjAlg k N g : MonoidAlgebra k N →+* MonoidAlgebra k N)]
      (resSubgroup ρ N).asModule where
  toFun x := (resSubgroup ρ N).asModuleEquiv.symm (ρ g ((resSubgroup ρ N).asModuleEquiv x))
  map_add' x y := by simp
  map_smul' r x := by
    apply (resSubgroup ρ N).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply,
      rho_asAlgebraHom_conjAlg]
    rfl
  invFun x := (resSubgroup ρ N).asModuleEquiv.symm (ρ g⁻¹ ((resSubgroup ρ N).asModuleEquiv x))
  left_inv x := by
    simp only [LinearEquiv.apply_symm_apply, ← Module.End.mul_apply, ← map_mul]; simp
  right_inv x := by
    simp only [LinearEquiv.apply_symm_apply, ← Module.End.mul_apply, ← map_mul]; simp

@[simp] lemma asModuleEquiv_conjEquiv (g : G) (x : (resSubgroup ρ N).asModule) :
    (resSubgroup ρ N).asModuleEquiv (conjEquiv ρ N g x)
      = ρ g ((resSubgroup ρ N).asModuleEquiv x) := by simp [conjEquiv]

noncomputable def toSubspace : Submodule k (resSubgroup ρ N).asModule ≃o Submodule k V :=
  Submodule.orderIsoMapComap (resSubgroup ρ N).asModuleEquiv

noncomputable def compAsSubspace
    (c : Submodule (MonoidAlgebra k N) (resSubgroup ρ N).asModule) : Submodule k V :=
  toSubspace ρ N (Submodule.restrictScalars k c)

@[simp] lemma mem_compAsSubspace
    (c : Submodule (MonoidAlgebra k N) (resSubgroup ρ N).asModule) (v : V) :
    v ∈ compAsSubspace ρ N c ↔ (resSubgroup ρ N).asModuleEquiv.symm v ∈ c := by
  simp [compAsSubspace, toSubspace, Submodule.mem_map_equiv]

lemma compAsSubspace_injective : Function.Injective (compAsSubspace ρ N) := fun _ _ h =>
  Submodule.restrictScalars_injective k _ _ ((toSubspace ρ N).injective h)

@[simp] lemma compAsSubspace_bot : compAsSubspace ρ N ⊥ = ⊥ := by
  simp [compAsSubspace, toSubspace]

lemma sSup_image_compAsSubspace
    (s : Set (Submodule (MonoidAlgebra k N) (resSubgroup ρ N).asModule)) :
    sSup (compAsSubspace ρ N '' s) = compAsSubspace ρ N (sSup s) := by
  have h : compAsSubspace ρ N = (toSubspace ρ N) ∘ (Submodule.restrictScalars k) := rfl
  rw [h, Set.image_comp, ← FrameHomClass.map_sSup (toSubspace ρ N),
    ← Submodule.restrictScalars_sSup]
  rfl

lemma compAsSubspace_inf (c d : Submodule (MonoidAlgebra k N) (resSubgroup ρ N).asModule) :
    compAsSubspace ρ N c ⊓ compAsSubspace ρ N d = compAsSubspace ρ N (c ⊓ d) := by
  rw [compAsSubspace, compAsSubspace, compAsSubspace, ← map_inf, ← Submodule.restrictScalars_inf]

noncomputable def comps : Set (Submodule k V) :=
  compAsSubspace ρ N '' isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule

lemma compAsSubspace_mem_comps
    {c : Submodule (MonoidAlgebra k N) (resSubgroup ρ N).asModule}
    (hc : c ∈ isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule) :
    compAsSubspace ρ N c ∈ comps ρ N := ⟨c, hc, rfl⟩

lemma mem_comps_iff {W : Submodule k V} :
    W ∈ comps ρ N ↔ ∃ c ∈ isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule,
      compAsSubspace ρ N c = W := Iff.rfl

lemma ne_bot_of_mem_comps {W : Submodule k V} (hW : W ∈ comps ρ N) : W ≠ ⊥ := by
  obtain ⟨c, ⟨S, hS, rfl⟩, rfl⟩ := hW
  intro hcon
  rw [← compAsSubspace_bot ρ N] at hcon
  exact (bot_lt_isotypicComponent S).ne' (compAsSubspace_injective ρ N hcon)

lemma smul_mem_of_mem_comps {W : Submodule k V} (hW : W ∈ comps ρ N) (n : N) {v : V}
    (hv : v ∈ W) : ρ (n : G) v ∈ W := by
  obtain ⟨c, hc, rfl⟩ := hW
  rw [mem_compAsSubspace] at hv ⊢
  have h : MonoidAlgebra.of k N n • (resSubgroup ρ N).asModuleEquiv.symm v ∈ c := c.smul_mem _ hv
  have h2 := Representation.asModuleEquiv_map_smul (resSubgroup ρ N) (MonoidAlgebra.of k N n)
    ((resSubgroup ρ N).asModuleEquiv.symm v)
  rw [Representation.asAlgebraHom_of, LinearEquiv.apply_symm_apply] at h2
  have h3 : (resSubgroup ρ N).asModuleEquiv.symm (ρ (n : G) v) =
      MonoidAlgebra.of k N n • (resSubgroup ρ N).asModuleEquiv.symm v := by
    apply (resSubgroup ρ N).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, h2]; rfl
  exact h3 ▸ h

theorem sSupIndep_comps : sSupIndep (comps ρ N) := by
  have key := sSupIndep_isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule
  intro W hW
  obtain ⟨c, hc, rfl⟩ := hW
  have himg : comps ρ N \ {compAsSubspace ρ N c} = compAsSubspace ρ N ''
      (isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule \ {c}) := by
    rw [comps, Set.image_sdiff (compAsSubspace_injective ρ N), Set.image_singleton]
  rw [himg, disjoint_iff, sSup_image_compAsSubspace, compAsSubspace_inf,
    (disjoint_iff).1 (key hc), compAsSubspace_bot]

theorem sSup_comps [Finite N] (hN : (Nat.card N : k) ≠ 0) : sSup (comps ρ N) = ⊤ := by
  have : NeZero ((Nat.card N : k)) := ⟨hN⟩
  rw [comps, sSup_image_compAsSubspace,
    sSup_isotypicComponents (MonoidAlgebra k N) (resSubgroup ρ N).asModule]
  simp [compAsSubspace, toSubspace]

theorem directSum_comps [Finite N] (hN : (Nat.card N : k) ≠ 0) :
    DirectSum.IsInternal (fun W : comps ρ N => (W : Submodule k V)) := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((sSupIndep_iff _).1 (sSupIndep_comps ρ N)) ?_
  rw [← sSup_eq_iSup', sSup_comps ρ N hN]

theorem map_mem_comps [Finite N] (hN : (Nat.card N : k) ≠ 0) (g : G) {W : Submodule k V}
    (hW : W ∈ comps ρ N) : W.map (ρ g) ∈ comps ρ N := by
  have : NeZero ((Nat.card N : k)) := ⟨hN⟩
  obtain ⟨c, hc, rfl⟩ := hW
  refine ⟨c.map (conjEquiv ρ N g : (resSubgroup ρ N).asModule
    →ₛₗ[(conjAlg k N g : MonoidAlgebra k N →+* MonoidAlgebra k N)] (resSubgroup ρ N).asModule),
    map_mem_isotypicComponents _ hc, ?_⟩
  ext v
  simp only [mem_compAsSubspace, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hyv⟩
    refine ⟨(resSubgroup ρ N).asModuleEquiv y, by simpa using hy, ?_⟩
    have h := congrArg (resSubgroup ρ N).asModuleEquiv hyv
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← asModuleEquiv_conjEquiv]
    exact h
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(resSubgroup ρ N).asModuleEquiv.symm w, hw, ?_⟩
    apply (resSubgroup ρ N).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, asModuleEquiv_conjEquiv, LinearEquiv.apply_symm_apply]

noncomputable def compPerm [Finite N] (hN : (Nat.card N : k) ≠ 0) :
    G →* Equiv.Perm (comps ρ N) where
  toFun g :=
    { toFun := fun W => ⟨(W : Submodule k V).map (ρ g), map_mem_comps ρ N hN g W.2⟩
      invFun := fun W => ⟨(W : Submodule k V).map (ρ g⁻¹), map_mem_comps ρ N hN g⁻¹ W.2⟩
      left_inv := fun W => by
        apply Subtype.ext
        change ((W : Submodule k V).map (ρ g)).map (ρ g⁻¹) = (W : Submodule k V)
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
          show (1 : Module.End k V) = LinearMap.id from rfl, Submodule.map_id]
      right_inv := fun W => by
        apply Subtype.ext
        change ((W : Submodule k V).map (ρ g⁻¹)).map (ρ g) = (W : Submodule k V)
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          show (1 : Module.End k V) = LinearMap.id from rfl, Submodule.map_id] }
  map_one' := by
    ext W : 1
    apply Subtype.ext
    change (W : Submodule k V).map (ρ 1) = (W : Submodule k V)
    rw [map_one, show (1 : Module.End k V) = LinearMap.id from rfl, Submodule.map_id]
  map_mul' g h := by
    ext W : 1
    apply Subtype.ext
    change (W : Submodule k V).map (ρ (g * h)) = ((W : Submodule k V).map (ρ h)).map (ρ g)
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]

@[simp] lemma coe_compPerm_apply [Finite N] (hN : (Nat.card N : k) ≠ 0) (g : G) (W : comps ρ N) :
    ((compPerm ρ N hN g W : comps ρ N) : Submodule k V) = (W : Submodule k V).map (ρ g) := (rfl)

theorem exists_map_eq_of_isIrreducible [Finite N] (hN : (Nat.card N : k) ≠ 0)
    (hirr : ρ.IsIrreducible) {W W' : Submodule k V} (hW : W ∈ comps ρ N)
    (hW' : W' ∈ comps ρ N) : ∃ g : G, W.map (ρ g) = W' := by
  by_contra hcon
  push Not at hcon
  set O : Set (Submodule k V) := {U | ∃ g : G, W.map (ρ g) = U} with hO
  have hOsub : O ⊆ comps ρ N := by rintro U ⟨g, rfl⟩; exact map_mem_comps ρ N hN g hW
  set T : Submodule k V := sSup O with hT
  have hTinv : ∀ g : G, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    have hle : T.map (ρ g) ≤ T := by
      rw [hT, Submodule.map_sSup]
      refine sSup_le ?_
      rintro U ⟨U', ⟨h, rfl⟩, rfl⟩
      exact le_sSup ⟨g * h, by rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]⟩
    exact hle (Submodule.mem_map_of_mem hv)
  have hWle : W ≤ T :=
    le_sSup ⟨1, by rw [map_one, show (1 : Module.End k V) = LinearMap.id from rfl,
      Submodule.map_id]⟩
  have hTne : T ≠ ⊥ := fun h => ne_bot_of_mem_comps ρ N hW (le_bot_iff.1 (h ▸ hWle))
  have hTtop : T = ⊤ := by
    rcases hirr.eq_bot_or_eq_top (⟨T, fun g v hv => hTinv g v hv⟩ : Subrepresentation ρ) with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hTne
    · exact congrArg Subrepresentation.toSubmodule h
  have hW'notO : W' ∉ O := by rintro ⟨g, hg⟩; exact hcon g hg
  have hOsub' : O ⊆ comps ρ N \ {W'} := fun U hU => ⟨hOsub hU, fun hUW' => hW'notO (hUW' ▸ hU)⟩
  have h1 : W' ≤ sSup (comps ρ N \ {W'}) :=
    le_trans le_top (le_trans (le_of_eq hTtop.symm) (sSup_le_sSup hOsub'))
  exact ne_bot_of_mem_comps ρ N hW'
    (by simpa using (sSupIndep_comps ρ N hW').eq_bot_of_le h1)

theorem exists_compPerm_eq_of_isIrreducible [Finite N] (hN : (Nat.card N : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (W W' : comps ρ N) : ∃ g : G, compPerm ρ N hN g W = W' := by
  obtain ⟨g, hg⟩ := exists_map_eq_of_isIrreducible ρ N hN hirr W.2 W'.2
  exact ⟨g, Subtype.ext hg⟩

end CFSG.FeitThompson
