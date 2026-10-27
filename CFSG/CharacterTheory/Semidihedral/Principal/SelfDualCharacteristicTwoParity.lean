module

public import CFSG.CharacterTheory.Semidihedral.Principal.CompositionMultiplicity
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open Representation

section GroupAlgebraLinear

variable {k G : Type*} [CommRing k] [Monoid G]
variable {X Y : Type*} [AddCommGroup X] [Module k X] [Module (MonoidAlgebra k G) X]
  [IsScalarTower k (MonoidAlgebra k G) X] [AddCommGroup Y] [Module k Y]
  [Module (MonoidAlgebra k G) Y] [IsScalarTower k (MonoidAlgebra k G) Y]

@[expose] def groupAlgebraLinearMap (f : X →ₗ[k] Y)
    (hf : ∀ (g : G) (x : X), f (MonoidAlgebra.of k G g • x) = MonoidAlgebra.of k G g • f x) :
    X →ₗ[MonoidAlgebra k G] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    induction r using MonoidAlgebra.induction_on with
    | of g => exact hf g x
    | add a b ha hb => simp only [add_smul, map_add, ha, hb, RingHom.id_apply] at *
    | smul c a ha =>
      simp only [RingHom.id_apply] at ha ⊢
      rw [smul_assoc, f.map_smul, ha, smul_assoc]

@[simp]
theorem groupAlgebraLinearMap_apply (f : X →ₗ[k] Y)
    (hf : ∀ (g : G) (x : X), f (MonoidAlgebra.of k G g • x) = MonoidAlgebra.of k G g • f x)
    (x : X) : groupAlgebraLinearMap f hf x = f x :=
  rfl

theorem ofModule'_apply (g : G) (x : X) :
    Representation.ofModule' (k := k) (G := G) X g x = MonoidAlgebra.of k G g • x :=
  rfl

noncomputable def ofModule'AsModuleEquiv :
    (Representation.ofModule' (k := k) (G := G) X).asModule ≃ₗ[MonoidAlgebra k G] X :=
  LinearEquiv.ofBijective
    (groupAlgebraLinearMap (Representation.ofModule' (k := k) (G := G) X).asModuleEquiv.toLinearMap
      fun g x => by
        rw [LinearEquiv.coe_coe, asModuleEquiv_map_smul, asAlgebraHom_of]
        rfl)
    (Representation.ofModule' (k := k) (G := G) X).asModuleEquiv.bijective

end GroupAlgebraLinear

section Dual

variable {k G : Type*} [Field k] [Group G]
variable {X Y Z : Type*} [AddCommGroup X] [Module k X] [Module (MonoidAlgebra k G) X]
  [IsScalarTower k (MonoidAlgebra k G) X] [AddCommGroup Y] [Module k Y]
  [Module (MonoidAlgebra k G) Y] [IsScalarTower k (MonoidAlgebra k G) Y] [AddCommGroup Z]
  [Module k Z] [Module (MonoidAlgebra k G) Z] [IsScalarTower k (MonoidAlgebra k G) Z]

variable (k G) in
abbrev DualMod (X : Type*) [AddCommGroup X] [Module k X] [Module (MonoidAlgebra k G) X]
    [IsScalarTower k (MonoidAlgebra k G) X] : Type _ :=
  (Representation.ofModule' (k := k) (G := G) X).dual.asModule

noncomputable abbrev DualMod.toDual : DualMod k G X ≃ₗ[k] Module.Dual k X :=
  (Representation.ofModule' (k := k) (G := G) X).dual.asModuleEquiv

theorem DualMod.of_smul_apply (g : G) (f : DualMod k G X) (x : X) :
    DualMod.toDual (MonoidAlgebra.of k G g • f) x =
      DualMod.toDual f (MonoidAlgebra.of k G g⁻¹ • x) := by
  rw [asModuleEquiv_map_smul, asAlgebraHom_of, dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, ofModule'_apply]

variable (k G) in
@[expose] noncomputable def dualModMapLinear (f : X →ₗ[MonoidAlgebra k G] Y) :
    DualMod k G Y →ₗ[k] DualMod k G X :=
  (DualMod.toDual (k := k) (G := G) (X := X)).symm.toLinearMap ∘ₗ
    (f.restrictScalars k).dualMap ∘ₗ (DualMod.toDual (k := k) (G := G) (X := Y)).toLinearMap

theorem dualModMapLinear_apply (f : X →ₗ[MonoidAlgebra k G] Y) (φ : DualMod k G Y) (x : X) :
    DualMod.toDual (dualModMapLinear k G f φ) x = DualMod.toDual φ (f x) :=
  rfl

theorem dualModMapLinear_comm (f : X →ₗ[MonoidAlgebra k G] Y) (g : G) (φ : DualMod k G Y) :
    dualModMapLinear k G f (MonoidAlgebra.of k G g • φ) =
      MonoidAlgebra.of k G g • dualModMapLinear k G f φ := by
  apply (DualMod.toDual (k := k) (G := G) (X := X)).injective
  ext x
  rw [dualModMapLinear_apply, DualMod.of_smul_apply, DualMod.of_smul_apply,
    dualModMapLinear_apply, f.map_smul]

variable (k G) in
@[expose] noncomputable def dualModMap (f : X →ₗ[MonoidAlgebra k G] Y) :
    DualMod k G Y →ₗ[MonoidAlgebra k G] DualMod k G X :=
  groupAlgebraLinearMap (X := DualMod k G Y) (Y := DualMod k G X) (dualModMapLinear k G f)
    (dualModMapLinear_comm f)

theorem dualModMap_apply (f : X →ₗ[MonoidAlgebra k G] Y) (φ : DualMod k G Y) (x : X) :
    DualMod.toDual (dualModMap k G f φ) x = DualMod.toDual φ (f x) :=
  rfl

theorem toDual_dualModMap (f : X →ₗ[MonoidAlgebra k G] Y) (φ : DualMod k G Y) :
    DualMod.toDual (dualModMap k G f φ) = (f.restrictScalars k).dualMap (DualMod.toDual φ) :=
  rfl

theorem dualModMap_injective {f : X →ₗ[MonoidAlgebra k G] Y} (hf : Function.Surjective f) :
    Function.Injective (dualModMap k G f) := by
  have h := LinearMap.dualMap_injective_of_surjective (f := f.restrictScalars k) hf
  intro φ ψ hφψ
  apply (DualMod.toDual (k := k) (G := G) (X := Y)).injective
  apply h
  have := congrArg (DualMod.toDual (k := k) (G := G) (X := X)) hφψ
  rwa [toDual_dualModMap, toDual_dualModMap] at this

theorem dualModMap_surjective {f : X →ₗ[MonoidAlgebra k G] Y} (hf : Function.Injective f) :
    Function.Surjective (dualModMap k G f) := by
  have h := LinearMap.dualMap_surjective_of_injective (f := f.restrictScalars k) hf
  intro ψ
  obtain ⟨φ, hφ⟩ := h (DualMod.toDual ψ)
  refine ⟨(DualMod.toDual (k := k) (G := G) (X := Y)).symm φ, ?_⟩
  apply (DualMod.toDual (k := k) (G := G) (X := X)).injective
  rw [toDual_dualModMap, LinearEquiv.apply_symm_apply]
  exact hφ

theorem dualModMap_exact {f : X →ₗ[MonoidAlgebra k G] Y} {g : Y →ₗ[MonoidAlgebra k G] Z}
    (H : Function.Exact f g) : Function.Exact (dualModMap k G g) (dualModMap k G f) := by
  have hker : LinearMap.ker (g.restrictScalars k) = LinearMap.range (f.restrictScalars k) := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.coe_restrictScalars, LinearMap.mem_range]
    exact H y
  have hdual : LinearMap.range (g.restrictScalars k).dualMap =
      LinearMap.ker (f.restrictScalars k).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, hker]
  intro φ
  constructor
  · intro hφ
    have hmem : DualMod.toDual φ ∈ LinearMap.ker (f.restrictScalars k).dualMap := by
      rw [LinearMap.mem_ker]
      have := congrArg (DualMod.toDual (k := k) (G := G) (X := X)) hφ
      rwa [toDual_dualModMap, map_zero] at this
    rw [← hdual] at hmem
    obtain ⟨ψ, hψ⟩ := hmem
    refine ⟨(DualMod.toDual (k := k) (G := G) (X := Z)).symm ψ, ?_⟩
    apply (DualMod.toDual (k := k) (G := G) (X := Y)).injective
    rw [toDual_dualModMap, LinearEquiv.apply_symm_apply]
    exact hψ
  · rintro ⟨ψ, rfl⟩
    have hmem : (g.restrictScalars k).dualMap (DualMod.toDual ψ) ∈
        LinearMap.ker (f.restrictScalars k).dualMap := by
      rw [← hdual]
      exact ⟨_, rfl⟩
    rw [LinearMap.mem_ker] at hmem
    apply (DualMod.toDual (k := k) (G := G) (X := X)).injective
    rw [toDual_dualModMap, toDual_dualModMap, map_zero]
    exact hmem

variable (k G) in
noncomputable def dualModCongr (e : X ≃ₗ[MonoidAlgebra k G] Y) :
    DualMod k G Y ≃ₗ[MonoidAlgebra k G] DualMod k G X :=
  LinearEquiv.ofBijective (dualModMap k G e.toLinearMap)
    ⟨dualModMap_injective e.surjective, dualModMap_surjective e.injective⟩

theorem finrank_dualMod [FiniteDimensional k X] :
    Module.finrank k (DualMod k G X) = Module.finrank k X :=
  (DualMod.toDual (k := k) (G := G) (X := X)).finrank_eq.trans Subspace.dual_finrank_eq

variable (k G) in
@[expose] noncomputable def doubleDualLinearEquiv [FiniteDimensional k X] :
    X ≃ₗ[k] DualMod k G (DualMod k G X) :=
  (Module.evalEquiv k X).trans ((DualMod.toDual (k := k) (G := G) (X := X)).dualMap.trans
    (DualMod.toDual (k := k) (G := G) (X := DualMod k G X)).symm)

theorem doubleDualLinearEquiv_apply [FiniteDimensional k X] (x : X) (φ : DualMod k G X) :
    DualMod.toDual (doubleDualLinearEquiv k G x) φ = DualMod.toDual φ x :=
  rfl

theorem doubleDualLinearEquiv_comm [FiniteDimensional k X] (g : G) (x : X) :
    doubleDualLinearEquiv k G (MonoidAlgebra.of k G g • x) =
      MonoidAlgebra.of k G g • doubleDualLinearEquiv k G x := by
  apply (DualMod.toDual (k := k) (G := G) (X := DualMod k G X)).injective
  ext φ
  rw [doubleDualLinearEquiv_apply, DualMod.of_smul_apply, doubleDualLinearEquiv_apply,
    DualMod.of_smul_apply, inv_inv]

variable (k G) in
noncomputable def doubleDualEquiv [FiniteDimensional k X] :
    X ≃ₗ[MonoidAlgebra k G] DualMod k G (DualMod k G X) :=
  LinearEquiv.ofBijective (groupAlgebraLinearMap (X := X) (Y := DualMod k G (DualMod k G X))
    (doubleDualLinearEquiv k G).toLinearMap (doubleDualLinearEquiv_comm (k := k) (G := G)))
    (doubleDualLinearEquiv k G).bijective

theorem isSimpleModule_dualMod [FiniteDimensional k X] [IsSimpleModule (MonoidAlgebra k G) X] :
    IsSimpleModule (MonoidAlgebra k G) (DualMod k G X) := by
  have hX : Nontrivial X := IsSimpleModule.nontrivial (MonoidAlgebra k G) X
  have hD : Nontrivial (DualMod k G X) := by
    rw [← Module.finrank_pos_iff (R := k), finrank_dualMod]
    exact Module.finrank_pos
  rw [isSimpleModule_iff]
  have hsimple : IsSimpleOrder (Submodule (MonoidAlgebra k G) X) :=
    (isSimpleModule_iff (MonoidAlgebra k G) X).mp inferInstance
  refine { eq_bot_or_eq_top := fun W => ?_ }
  let W' : Submodule k (Module.Dual k X) :=
    (W.restrictScalars k).map (DualMod.toDual (k := k) (G := G) (X := X)).toLinearMap
  have hmemW' : ∀ ψ : DualMod k G X, DualMod.toDual ψ ∈ W' ↔ ψ ∈ W := by
    intro ψ
    constructor
    · rintro ⟨ψ', hψ', hψψ'⟩
      have : ψ' = ψ := DualMod.toDual.injective hψψ'
      rw [← this]
      exact hψ'
    · intro hψ
      exact ⟨ψ, hψ, rfl⟩
  let C : Submodule (MonoidAlgebra k G) X :=
    { W'.dualCoannihilator with
      smul_mem' := fun r x hx => by
        induction r using MonoidAlgebra.induction_on with
        | of g =>
          change MonoidAlgebra.of k G g • x ∈ W'.dualCoannihilator
          rw [Submodule.mem_dualCoannihilator]
          intro φ hφ
          obtain ⟨ψ, hψ, rfl⟩ := hφ
          have h1 : MonoidAlgebra.of k G g⁻¹ • ψ ∈ W := W.smul_mem _ hψ
          have h2 := (Submodule.mem_dualCoannihilator _).mp hx _ ((hmemW' _).mpr h1)
          rw [DualMod.of_smul_apply, inv_inv] at h2
          exact h2
        | add a b ha hb =>
          rw [add_smul]
          exact W'.dualCoannihilator.add_mem ha hb
        | smul c a ha =>
          rw [smul_assoc]
          exact W'.dualCoannihilator.smul_mem c ha }
  have hCmem : ∀ x, x ∈ C ↔ x ∈ W'.dualCoannihilator := fun x => Iff.rfl
  rcases hsimple.eq_bot_or_eq_top C with hC | hC
  · right
    have hbot : W'.dualCoannihilator = ⊥ := by
      ext x
      rw [← hCmem, hC]
      rfl
    have htop : W' = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W'), hbot,
        Submodule.dualAnnihilator_bot]
    rw [eq_top_iff]
    intro ψ _
    rw [← hmemW', htop]
    trivial
  · left
    have htop : W'.dualCoannihilator = ⊤ := by
      ext x
      rw [← hCmem, hC]
      rfl
    have hbot : W' = ⊥ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W'), htop,
        Submodule.dualAnnihilator_top]
    rw [eq_bot_iff]
    intro ψ hψ
    rw [← hmemW', hbot, Submodule.mem_bot] at hψ
    rw [Submodule.mem_bot]
    exact DualMod.toDual.injective (hψ.trans (map_zero _).symm)

end Dual

section Duality

variable {k G : Type*} [Field k] [Group G]

theorem compositionMultiplicity_dualMod_of_isSimpleModule {Q : Type*} [AddCommGroup Q]
    [Module k Q] [Module (MonoidAlgebra k G) Q] [IsScalarTower k (MonoidAlgebra k G) Q]
    [FiniteDimensional k Q] [IsSimpleModule (MonoidAlgebra k G) Q] (S : Type*) [AddCommGroup S]
    [Module k S] [Module (MonoidAlgebra k G) S] [IsScalarTower k (MonoidAlgebra k G) S]
    [FiniteDimensional k S] :
    compositionMultiplicity (MonoidAlgebra k G) (DualMod k G Q) S =
      compositionMultiplicity (MonoidAlgebra k G) Q (DualMod k G S) := by
  have := isSimpleModule_dualMod (k := k) (G := G) (X := Q)
  rw [compositionMultiplicity_of_isSimpleModule, compositionMultiplicity_of_isSimpleModule]
  refine if_congr ⟨fun ⟨e⟩ => ⟨(doubleDualEquiv k G).trans (dualModCongr k G e).symm⟩,
    fun ⟨e⟩ => ⟨(dualModCongr k G e).symm.trans (doubleDualEquiv k G).symm⟩⟩ rfl rfl

theorem compositionMultiplicity_dualMod {X : Type*} [AddCommGroup X] [Module k X]
    [Module (MonoidAlgebra k G) X] [IsScalarTower k (MonoidAlgebra k G) X]
    [FiniteDimensional k X] (S : Type*) [AddCommGroup S] [Module k S]
    [Module (MonoidAlgebra k G) S] [IsScalarTower k (MonoidAlgebra k G) S]
    [FiniteDimensional k S] :
    compositionMultiplicity (MonoidAlgebra k G) (DualMod k G X) S =
      compositionMultiplicity (MonoidAlgebra k G) X (DualMod k G S) := by
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    rcases subsingleton_or_nontrivial X with hX | hX
    · have : Subsingleton (DualMod k G X) := by
        rw [← Module.finrank_zero_iff (R := k), finrank_dualMod]
        exact Module.finrank_zero_of_subsingleton
      rw [compositionMultiplicity_of_subsingleton, compositionMultiplicity_of_subsingleton]
    · have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := X)
      have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := X)
      obtain ⟨N, hN⟩ : ∃ N : Submodule (MonoidAlgebra k G) X, IsCoatom N := by
        obtain h | ⟨N, hN, -⟩ := eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) X)
        · exact absurd h bot_ne_top
        · exact ⟨N, hN⟩
      have : IsSimpleModule (MonoidAlgebra k G) (X ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
      have : FiniteDimensional k N :=
        Module.Finite.of_injective (N.subtype.restrictScalars k) N.injective_subtype
      have hNlt : Module.finrank k N < n := by
        rw [← hn]
        have hne : N.restrictScalars k ≠ ⊤ := by
          intro h
          apply hN.1
          ext x
          have := congrArg (x ∈ ·) h
          simpa using this
        exact Submodule.finrank_lt hne
      have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := DualMod k G N)
      have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := DualMod k G N)
      have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G)
        (M := DualMod k G (X ⧸ N))
      have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G)
        (M := DualMod k G (X ⧸ N))
      rw [compositionMultiplicity_eq_add_of_exact (N := DualMod k G (X ⧸ N))
        (M := DualMod k G X) (P := DualMod k G N) (dualModMap k G N.mkQ)
        (dualModMap k G N.subtype) (dualModMap_injective N.mkQ_surjective)
        (dualModMap_surjective N.injective_subtype)
        (dualModMap_exact (LinearMap.exact_subtype_mkQ N)) S,
        compositionMultiplicity_eq_submodule_add_quotient N (DualMod k G S),
        ih _ hNlt (X := N) rfl, compositionMultiplicity_dualMod_of_isSimpleModule S, add_comm]

end Duality

section Alternating

theorem even_finrank_of_isAlt {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {B : LinearMap.BilinForm K W} (hB : B.Nondegenerate)
    (hA : B.IsAlt) : Even (Module.finrank K W) := by
  let P : ℕ → Prop := fun n => ∃ U : Submodule K W, U ≤ B.orthogonal U ∧ Module.finrank K U = n
  have hP0 : P 0 := ⟨⊥, bot_le, finrank_bot K W⟩
  obtain ⟨U, hUiso, hUm⟩ : P (Nat.findGreatest P (Module.finrank K W)) :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hmax : B.orthogonal U ≤ U := by
    intro x hx
    by_contra hxU
    have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
    have hiso : U ⊔ Submodule.span K {x} ≤ B.orthogonal (U ⊔ Submodule.span K {x}) := by
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b hb
      obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨u', hu', s', hs', rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hs'
      have h1 : B u' u = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp (hUiso hu)) u' hu'
      have h2 : B u' x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u' hu'
      have h3 : B x u = 0 := (hA.eq_iff).mp
        ((LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu)
      have h4 : B x x = 0 := hA x
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1, h2, h3, h4,
        smul_zero, add_zero]
    have hdim : Module.finrank K ↥(U ⊔ Submodule.span K {x}) =
        Nat.findGreatest P (Module.finrank K W) + 1 := by
      have hinf : U ⊓ Submodule.span K {x} = ⊥ :=
        disjoint_iff.mp ((Submodule.disjoint_span_singleton' hx0).mpr hxU)
      have := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span K {x})
      rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0, hUm] at this
      exact this
    have hle := Nat.le_findGreatest (P := P)
      (hdim ▸ Submodule.finrank_le (U ⊔ Submodule.span K {x})) ⟨_, hiso, hdim⟩
    omega
  have heq : B.orthogonal U = U := le_antisymm hmax hUiso
  have hdim := LinearMap.BilinForm.finrank_orthogonal hB U
  rw [heq] at hdim
  have hle := Submodule.finrank_le U
  exact ⟨Module.finrank K U, by omega⟩

end Alternating

section Fong

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

theorem even_finrank_of_irreducible_selfDual [IsAlgClosed k] [CharP k 2] [FiniteDimensional k W]
    (σ : Representation k G W) (hσ : σ.IsIrreducible)
    (hnt : ¬ Nonempty (σ.Equiv (Representation.trivial k G k)))
    (hsd : Nonempty (σ.Equiv σ.dual)) : Even (Module.finrank k W) := by
  obtain ⟨φ⟩ := hsd
  have : σ.IsIrreducible := hσ
  let B : LinearMap.BilinForm k W := φ.toLinearMap
  have hBφ : ∀ v w, B v w = φ v w := fun _ _ => rfl
  have hφ : ∀ g v, φ (σ g v) = σ.dual g (φ v) := fun g v =>
    IntertwiningMap.isIntertwining σ σ.dual φ.toIntertwiningMap g v
  have hinv : ∀ g v w, B (σ g v) (σ g w) = B v w := by
    intro g v w
    rw [hBφ, hBφ, hφ g v]
    rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective φ := φ.injective
  have hsepL : ∀ v, (∀ w, B v w = 0) → v = 0 := by
    intro v hv
    apply hinj
    rw [map_zero]
    ext w
    exact hv w
  have hnd : B.Nondegenerate := by
    refine ⟨hsepL, fun w hw => ?_⟩
    rw [← Module.forall_dual_apply_eq_zero_iff k w]
    intro f
    obtain ⟨v, rfl⟩ := φ.surjective f
    exact hw v
  let ψ : σ.IntertwiningMap σ.dual :=
    { toLinearMap := B.flip
      isIntertwining' := fun g => by
        ext v w
        change B w (σ g v) = (σ.dual g (B.flip v)) w
        rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
          LinearMap.BilinForm.flip_apply, ← hinv g (σ g⁻¹ w) v, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] }
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := σ)).2 (φ.symm.toIntertwiningMap.comp ψ)
  have hflip : ∀ v w, B w v = c * B v w := by
    intro v w
    have h : (algebraMap k (σ.IntertwiningMap σ) c) v = (φ.symm.toIntertwiningMap.comp ψ) v := by
      rw [hc]
    rw [Algebra.algebraMap_eq_smul_one, IntertwiningMap.smul_apply] at h
    have h₁ : c • v = φ.symm (ψ v) := h
    have h' : φ (c • v) = ψ v := by
      rw [h₁]
      exact φ.apply_symm_apply _
    have := congrArg (fun f : Module.Dual k W => f w) h'
    change (φ (c • v)) w = B w v at this
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    rw [← this, hBφ]
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    exact (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (hsepL v h)
  have hc2 : c * c = 1 := by
    have h1 := hflip v w
    have h2 := hflip w v
    have : (c * c - 1) * B v w = 0 := by linear_combination -h2 - c * h1
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hw
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have : (c - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have hsymm : ∀ v w, B w v = B v w := fun v w => by rw [hflip, hc1, one_mul]
  let fr := (frobeniusEquiv k 2).symm
  have hfr2 : ∀ a : k, fr (a ^ 2) = a := fun a => by
    have := (frobeniusEquiv k 2).symm_apply_apply a
    rwa [frobeniusEquiv_apply, frobenius_def] at this
  let ℓ : W →ₗ[k] k :=
    { toFun := fun v => fr (B v v)
      map_add' := fun v w => by
        have : B (v + w) (v + w) = B v v + B w w := by
          simp only [map_add, LinearMap.add_apply]
          rw [hsymm v w]
          linear_combination (B v w) * h2
        rw [this, map_add]
      map_smul' := fun a v => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← mul_assoc, ← sq, map_mul, hfr2] }
  have hℓ : ∀ g v, ℓ (σ g v) = ℓ v := fun g v => by
    change fr (B (σ g v) (σ g v)) = fr (B v v)
    rw [hinv]
  have hℓ0 : ℓ = 0 := by
    by_contra hne
    let K : Subrepresentation σ := ⟨LinearMap.ker ℓ, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hℓ, hv]⟩
    rcases hσ.eq_bot_or_eq_top K with hK | hK
    · have hkerl : LinearMap.ker ℓ = ⊥ := congrArg Subrepresentation.toSubmodule hK
      have hsurj : Function.Surjective ℓ := by
        obtain ⟨v₀, hv₀⟩ : ∃ v₀, ℓ v₀ ≠ 0 := by
          by_contra h
          push Not at h
          exact hne (LinearMap.ext h)
        intro a
        refine ⟨(a / ℓ v₀) • v₀, ?_⟩
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀]
      apply hnt
      refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ℓ
        ⟨LinearMap.ker_eq_bot.mp hkerl, hsurj⟩) fun g => ?_⟩
      ext v
      change ℓ (σ g v) = (Representation.trivial k G k) g (ℓ v)
      rw [hℓ]
      rfl
    · apply hne
      ext v
      have : v ∈ K.toSubmodule := by rw [hK]; trivial
      exact this
  have halt : B.IsAlt := by
    intro v
    have : ℓ v = 0 := by rw [hℓ0]; rfl
    exact fr.injective (this.trans (map_zero fr).symm)
  exact even_finrank_of_isAlt hnd halt

end Fong

section Counting

theorem sum_filter_pairs_eq_sum_filter_diag {ι : Type*} [Fintype ι] (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → R j i) (w : ι → ZMod 2) (hw : ∀ i j, R i j → w i = w j) :
    ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => R p.1 p.2), w p.1 =
      ∑ i ∈ Finset.univ.filter (fun i => R i i), w i := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ι × ι => p.1 = p.2)]
  have hoff : ∑ p ∈ ((Finset.univ : Finset (ι × ι)).filter (fun p => R p.1 p.2)).filter
      (fun p => ¬ p.1 = p.2), w p.1 = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) (fun p hp => ?_) (fun p hp _ => ?_)
      (fun p hp => ?_) (fun p _ => rfl)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [hw _ _ hp.1]
      exact CharTwo.add_self_eq_zero _
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      intro h
      apply hp.2
      have := congrArg Prod.fst h
      simpa using this.symm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hR _ _ hp.1, fun h => hp.2 h.symm⟩
  rw [hoff, add_zero]
  refine Finset.sum_nbij' Prod.fst (fun i => (i, i)) (fun p hp => ?_) (fun i hi => ?_)
    (fun p hp => ?_) (fun i _ => rfl) (fun p _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h := hp.2
    rw [← h] at hp
    exact hp.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Prod.ext rfl hp.2

theorem sum_filter_pairs_eq_sum_card {ι : Type*} [Fintype ι] (R : ι → ι → Prop)
    (w : ι → ZMod 2) :
    ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => R p.1 p.2), w p.1 =
      ∑ i, ((Finset.univ.filter (R i)).card : ZMod 2) * w i := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

end Counting

section Parity

universe u

variable {k G : Type*} [Field k] [Group G]

theorem irreducible_ofModule' (S : Type*) [AddCommGroup S] [Module k S]
    [Module (MonoidAlgebra k G) S] [IsScalarTower k (MonoidAlgebra k G) S]
    [IsSimpleModule (MonoidAlgebra k G) S] :
    (Representation.ofModule' (k := k) (G := G) S).IsIrreducible := by
  rw [irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr (ofModule'AsModuleEquiv (k := k) (G := G) (X := S))

noncomputable def dualAsModuleEquiv {M : Type*} [AddCommGroup M] [Module k M]
    (ρ : Representation k G M) :
    ρ.dual.asModule ≃ₗ[MonoidAlgebra k G] DualMod k G ρ.asModule :=
  let E : ρ.dual.asModule ≃ₗ[k] DualMod k G ρ.asModule :=
    ρ.dual.asModuleEquiv.trans (ρ.asModuleEquiv.dualMap.trans
      (DualMod.toDual (k := k) (G := G) (X := ρ.asModule)).symm)
  LinearEquiv.ofBijective (groupAlgebraLinearMap (X := ρ.dual.asModule)
    (Y := DualMod k G ρ.asModule) E.toLinearMap fun g f => by
      apply (DualMod.toDual (k := k) (G := G) (X := ρ.asModule)).injective
      ext x
      rw [DualMod.of_smul_apply]
      change (ρ.dual.asModuleEquiv (MonoidAlgebra.of k G g • f)) (ρ.asModuleEquiv x) =
        (ρ.dual.asModuleEquiv f) (ρ.asModuleEquiv (MonoidAlgebra.of k G g⁻¹ • x))
      rw [asModuleEquiv_map_smul, asModuleEquiv_map_smul, asAlgebraHom_of, asAlgebraHom_of,
        dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]) E.bijective

noncomputable def trivialSelfDual :
    (Representation.trivial k G k).asModule ≃ₗ[MonoidAlgebra k G]
      DualMod k G (Representation.trivial k G k).asModule :=
  let E : (Representation.trivial k G k).asModule ≃ₗ[k]
      DualMod k G (Representation.trivial k G k).asModule :=
    (Representation.trivial k G k).asModuleEquiv.trans
      ((LinearMap.ringLmapEquivSelf k k k).symm.trans
      ((Representation.trivial k G k).asModuleEquiv.dualMap.trans
        (DualMod.toDual (k := k) (G := G) (X := (Representation.trivial k G k).asModule)).symm))
  have htriv : ∀ (g : G) (x : (Representation.trivial k G k).asModule),
      MonoidAlgebra.of k G g • x = x := fun g x => by
    apply (Representation.trivial k G k).asModuleEquiv.injective
    rw [asModuleEquiv_map_smul, asAlgebraHom_of]
    rfl
  LinearEquiv.ofBijective (groupAlgebraLinearMap (X := (Representation.trivial k G k).asModule)
    (Y := DualMod k G (Representation.trivial k G k).asModule) E.toLinearMap fun g x => by
      rw [htriv]
      apply (DualMod.toDual (k := k) (G := G)
        (X := (Representation.trivial k G k).asModule)).injective
      refine LinearMap.ext fun y => ?_
      rw [DualMod.of_smul_apply, htriv]) E.bijective

abbrev seriesFactor {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (s : CompositionSeries (Submodule A M)) (i : Fin s.length) : Type _ :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

theorem isSimpleModule_seriesFactor {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    IsSimpleModule A (seriesFactor s i) :=
  (covBy_iff_quot_is_simple (s.lt_succ i).le).mp (s.step i)

theorem finiteDimensional_seriesFactor {A M : Type*} [Ring A] [Algebra k A] [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    FiniteDimensional k (seriesFactor s i) := by
  have : FiniteDimensional k (s i.succ) :=
    Module.Finite.of_injective ((s i.succ).subtype.restrictScalars k) (s i.succ).injective_subtype
  infer_instance

end Parity

section ParityTheorem

universe u

variable {k G : Type*} [Field k] [Group G]

theorem compositionMultiplicity_eq_dualMod_of_dual {M : Type u} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (ρ : Representation k G M)
    (hρ : ∀ (W : Type u) [AddCommGroup W] [Module k W] (σ : Representation k G W),
      σ.IsIrreducible → repMultiplicity ρ σ = repMultiplicity ρ.dual σ)
    (S : Type u) [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k G) S]
    [IsScalarTower k (MonoidAlgebra k G) S] [IsSimpleModule (MonoidAlgebra k G) S]
    [FiniteDimensional k S] :
    compositionMultiplicity (MonoidAlgebra k G) ρ.asModule S =
      compositionMultiplicity (MonoidAlgebra k G) ρ.asModule (DualMod k G S) := by
  have h := hρ S (Representation.ofModule' (k := k) (G := G) S) (irreducible_ofModule' S)
  unfold repMultiplicity at h
  calc compositionMultiplicity (MonoidAlgebra k G) ρ.asModule S
      = compositionMultiplicity (MonoidAlgebra k G) ρ.asModule
          (Representation.ofModule' (k := k) (G := G) S).asModule :=
        (compositionMultiplicity_congr_right (ofModule'AsModuleEquiv (k := k) (G := G))).symm
    _ = compositionMultiplicity (MonoidAlgebra k G) ρ.dual.asModule
          (Representation.ofModule' (k := k) (G := G) S).asModule := h
    _ = compositionMultiplicity (MonoidAlgebra k G) ρ.dual.asModule S :=
        compositionMultiplicity_congr_right (ofModule'AsModuleEquiv (k := k) (G := G))
    _ = compositionMultiplicity (MonoidAlgebra k G) (DualMod k G ρ.asModule) S :=
        compositionMultiplicity_congr_left (dualAsModuleEquiv ρ) S
    _ = compositionMultiplicity (MonoidAlgebra k G) ρ.asModule (DualMod k G S) :=
        compositionMultiplicity_dualMod S

theorem self_dual_characteristic_two_composition_parity_forces_trivial_factor [IsAlgClosed k]
    [CharP k 2] {M : Type u} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (ρ : Representation k G M)
    (hρ : ∀ (W : Type u) [AddCommGroup W] [Module k W] (σ : Representation k G W),
      σ.IsIrreducible → repMultiplicity ρ σ = repMultiplicity ρ.dual σ) :
    repMultiplicity ρ (Representation.trivial k G k) ≡ Module.finrank k M [MOD 2] ∧
    (Odd (Module.finrank k M) → 0 < repMultiplicity ρ (Representation.trivial k G k) ∧
      Odd (repMultiplicity ρ (Representation.trivial k G k))) ∧
    ∀ (W : Type*) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (σ : Representation k G W), σ.IsIrreducible →
      ¬ Nonempty (σ.Equiv (Representation.trivial k G k)) → Nonempty (σ.Equiv σ.dual) →
      Even (Module.finrank k W) := by
  have key : ((repMultiplicity ρ (Representation.trivial k G k) : ℕ) : ZMod 2) =
      (Module.finrank k M : ZMod 2) := by
    have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ.asModule)
    have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ.asModule)
    obtain ⟨s, hs₁, hs₂⟩ :=
      exists_compositionSeries_of_isNoetherian_isArtinian (MonoidAlgebra k G) ρ.asModule
    have hsim := isSimpleModule_seriesFactor s
    have hfin := finiteDimensional_seriesFactor (k := k) s
    let T := (Representation.trivial k G k).asModule
    let R₁ : Fin s.length → Fin s.length → Prop := fun i j =>
      Nonempty (seriesFactor s j ≃ₗ[MonoidAlgebra k G] seriesFactor s i)
    let R₂ : Fin s.length → Fin s.length → Prop := fun i j =>
      Nonempty (seriesFactor s j ≃ₗ[MonoidAlgebra k G] DualMod k G (seriesFactor s i))
    let w : Fin s.length → ZMod 2 := fun i => (Module.finrank k (seriesFactor s i) : ZMod 2)
    have hR₁ : ∀ i j, R₁ i j → R₁ j i := fun i j ⟨e⟩ => ⟨e.symm⟩
    have hw₁ : ∀ i j, R₁ i j → w i = w j := fun i j ⟨e⟩ => by
      simp only [w]
      rw [(e.restrictScalars k).finrank_eq]
    have hR₂ : ∀ i j, R₂ i j → R₂ j i := fun i j ⟨e⟩ =>
      ⟨(doubleDualEquiv k G).trans (dualModCongr k G e)⟩
    have hw₂ : ∀ i j, R₂ i j → w i = w j := fun i j ⟨e⟩ => by
      simp only [w]
      rw [(e.restrictScalars k).finrank_eq, finrank_dualMod]
    have hc : ∀ i, compositionMultiplicity (MonoidAlgebra k G) ρ.asModule (seriesFactor s i) =
        (Finset.univ.filter (R₁ i)).card := fun i => by
      rw [compositionMultiplicity_eq_factorCount s hs₁ hs₂]
      rfl
    have hd : ∀ i, compositionMultiplicity (MonoidAlgebra k G) ρ.asModule
        (DualMod k G (seriesFactor s i)) = (Finset.univ.filter (R₂ i)).card := fun i => by
      rw [compositionMultiplicity_eq_factorCount s hs₁ hs₂]
      rfl
    have hcd : ∀ i, (Finset.univ.filter (R₁ i)).card = (Finset.univ.filter (R₂ i)).card :=
      fun i => by
        rw [← hc, ← hd]
        exact compositionMultiplicity_eq_dualMod_of_dual ρ hρ (seriesFactor s i)
    have hsum : ∑ i, w i = ∑ i ∈ Finset.univ.filter (fun i => R₂ i i), w i := by
      have h1 := sum_filter_pairs_eq_sum_filter_diag R₁ hR₁ w hw₁
      have h2 := sum_filter_pairs_eq_sum_filter_diag R₂ hR₂ w hw₂
      rw [sum_filter_pairs_eq_sum_card] at h1 h2
      have hdiag : Finset.univ.filter (fun i => R₁ i i) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => ⟨LinearEquiv.refl _ _⟩
      rw [hdiag] at h1
      rw [← h1, ← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcd]
    have hself : ∀ i, R₂ i i → w i = if Nonempty (seriesFactor s i ≃ₗ[MonoidAlgebra k G] T)
        then 1 else 0 := by
      intro i ⟨e⟩
      split_ifs with ht
      · obtain ⟨t⟩ := ht
        simp only [w]
        rw [(t.restrictScalars k).finrank_eq,
          ((Representation.trivial k G k).asModuleEquiv).finrank_eq, Module.finrank_self]
        simp
      · let σ := Representation.ofModule' (k := k) (G := G) (seriesFactor s i)
        have hσ : σ.IsIrreducible := irreducible_ofModule' (seriesFactor s i)
        have hnt : ¬ Nonempty (σ.Equiv (Representation.trivial k G k)) := by
          rintro ⟨φ⟩
          exact ht ⟨(ofModule'AsModuleEquiv (k := k) (G := G)).symm.trans
            (asModuleEquivOfEquiv φ)⟩
        have hsd : Nonempty (σ.Equiv σ.dual) :=
          ⟨equivOfAsModuleEquiv ((ofModule'AsModuleEquiv (k := k) (G := G)).trans e)⟩
        obtain ⟨m, hm⟩ := even_finrank_of_irreducible_selfDual σ hσ hnt hsd
        simp only [w]
        change ((Module.finrank k (seriesFactor s i) : ℕ) : ZMod 2) = 0
        rw [hm, Nat.cast_add, CharTwo.add_self_eq_zero]
    have htrivsd : ∀ i, Nonempty (seriesFactor s i ≃ₗ[MonoidAlgebra k G] T) → R₂ i i :=
      fun i ⟨t⟩ => ⟨t.trans (trivialSelfDual.trans (dualModCongr k G t))⟩
    have hcount : ∑ i ∈ Finset.univ.filter (fun i => R₂ i i), w i =
        ((Finset.univ.filter fun i =>
          Nonempty (seriesFactor s i ≃ₗ[MonoidAlgebra k G] T)).card : ZMod 2) := by
      rw [Finset.sum_congr rfl fun i hi => hself i (Finset.mem_filter.mp hi).2,
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.filter_filter]
      congr 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨htrivsd i h, h⟩⟩
    have hmult : repMultiplicity ρ (Representation.trivial k G k) =
        (Finset.univ.filter fun i =>
          Nonempty (seriesFactor s i ≃ₗ[MonoidAlgebra k G] T)).card := by
      unfold repMultiplicity
      rw [compositionMultiplicity_eq_factorCount s hs₁ hs₂]
      rfl
    have hdim : Module.finrank k M = ∑ i, Module.finrank k (seriesFactor s i) := by
      rw [← ρ.asModuleEquiv.finrank_eq]
      exact finrank_eq_sum_finrank_factor k s hs₁ hs₂
    rw [hmult, ← hcount, ← hsum, hdim]
    push_cast
    rfl
  have hmod : repMultiplicity ρ (Representation.trivial k G k) ≡ Module.finrank k M [MOD 2] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp key
  refine ⟨hmod, fun hodd => ?_, fun W _ _ _ σ hσ hnt hsd =>
    even_finrank_of_irreducible_selfDual σ hσ hnt hsd⟩
  have hodd' : Odd (repMultiplicity ρ (Representation.trivial k G k)) := by
    rw [Nat.odd_iff] at hodd ⊢
    rw [Nat.ModEq] at hmod
    rw [hmod, hodd]
  exact ⟨hodd'.pos, hodd'⟩

end ParityTheorem

end CFSG.Semidihedral.Principal
