module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.SimpleModule.Isotypic

public section

open Submodule

open scoped MonoidAlgebra

namespace CFSG.LinearAlgebra.CoprimeActions.PrimeNormalizerStableIrreducibleType

section abstract

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  {φ ψ : R →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]

theorem tw_equiv (T : M ≃ₛₗ[φ] M) {X Y : Submodule R M} (e : X ≃ₗ[R] Y) :
    Nonempty (X.map (T : M →ₛₗ[φ] M) ≃ₗ[R] Y.map (T : M →ₛₗ[φ] M)) :=
  ⟨((T.submoduleMap X).symm.trans e).trans (T.submoduleMap Y)⟩

theorem tw_simple (T : M ≃ₛₗ[φ] M) {X : Submodule R M} (h : IsSimpleModule R X) :
    IsSimpleModule R (X.map (T : M →ₛₗ[φ] M)) := by
  rw [isSimpleModule_iff_isAtom] at *
  exact (Submodule.orderIsoMapComap T).isAtom_iff X |>.mpr h

@[expose] def tw (T : M ≃ₛₗ[φ] M) (X : Submodule R M) : Submodule R M := X.map (T : M →ₛₗ[φ] M)

theorem tw_iter_equiv (T : M ≃ₛₗ[φ] M) {X Y : Submodule R M} (e : Nonempty (X ≃ₗ[R] Y)) (m : ℕ) :
    Nonempty ((tw T)^[m] X ≃ₗ[R] (tw T)^[m] Y) := by
  induction m with
  | zero => simpa using e
  | succ m ih =>
    obtain ⟨e⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact tw_equiv T e

theorem tw_iter_simple (T : M ≃ₛₗ[φ] M) {X : Submodule R M} (h : IsSimpleModule R X) (m : ℕ) :
    IsSimpleModule R ((tw T)^[m] X) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact tw_simple T ih

theorem clifford_shift [IsSemisimpleModule R M] (T : M ≃ₛₗ[φ] M) (r : ℕ) [hr : Fact r.Prime]
    (hid : (tw T)^[r] = id) (S0 : Submodule R M)
    (i j : ℕ) (hij : i < j) (hjr : j < r)
    (e : Nonempty (((tw T)^[i] S0) ≃ₗ[R] ((tw T)^[j] S0))) :
    Nonempty (S0 ≃ₗ[R] (tw T S0)) := by
  have hmod : ∀ n, (tw T)^[n] = (tw T)^[n % r] := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n r, Function.iterate_add,
      Function.iterate_mul, hid, Function.iterate_id]
    rfl
  set k := j - i with hk
  have hk0 : 0 < k := by omega
  have hkr : k < r := by omega
  have hjik : j = i + k := by omega
  have hreind : ∀ a b, (tw T)^[a * r + b] = (tw T)^[b] := by
    intro a b
    rw [Function.iterate_add, mul_comm, Function.iterate_mul, hid, Function.iterate_id]
    rfl
  have h0 : Nonempty (S0 ≃ₗ[R] ((tw T)^[k] S0)) := by
    obtain ⟨e'⟩ := tw_iter_equiv T e ((r - 1) * i)
    have h1 : (tw T)^[(r - 1) * i] ((tw T)^[i] S0) = S0 := by
      rw [← Function.iterate_add_apply]
      have : (r - 1) * i + i = i * r + 0 := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      rw [this, hreind]; rfl
    have h2 : (tw T)^[(r - 1) * i] ((tw T)^[j] S0) = (tw T)^[k] S0 := by
      rw [← Function.iterate_add_apply]
      have : (r - 1) * i + j = i * r + k := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring_nf; omega
      rw [this, hreind]
    rw [h1, h2] at e'
    exact ⟨e'⟩
  have hshift : ∀ n, Nonempty (((tw T)^[n] S0) ≃ₗ[R] ((tw T)^[n + k] S0)) := by
    intro n
    obtain ⟨e'⟩ := tw_iter_equiv T h0 n
    rw [← Function.iterate_add_apply] at e'
    exact ⟨e'⟩
  have hmul : ∀ a, Nonempty (S0 ≃ₗ[R] ((tw T)^[a * k] S0)) := by
    intro a
    induction a with
    | zero => rw [zero_mul]; exact ⟨LinearEquiv.refl _ _⟩
    | succ a ih =>
      obtain ⟨e1⟩ := ih
      obtain ⟨e2⟩ := hshift (a * k)
      rw [Nat.succ_mul]
      exact ⟨e1.trans e2⟩
  have hcop : Nat.Coprime k r := by
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr.out).2 (Nat.not_dvd_of_pos_of_lt hk0 hkr)))
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.out.one_lt
  obtain ⟨e⟩ := hmul a
  rw [mul_comm, hmod, ha] at e
  exact ⟨by simpa using e⟩

theorem clifford_indep [IsSemisimpleModule R M] (T : M ≃ₛₗ[φ] M) (r : ℕ) [hr : Fact r.Prime]
    (hid : (tw T)^[r] = id) (S0 : Submodule R M) [IsSimpleModule R S0]
    (hne : ¬ Nonempty (S0 ≃ₗ[R] (tw T S0))) :
    iSupIndep (fun i : Fin r => isotypicComponent R M ((tw T)^[i.val] S0)) := by
  have hsimple : ∀ i : ℕ, IsSimpleModule R ((tw T)^[i] S0) := fun i => tw_iter_simple T ‹_› i
  let c : Fin r → ↥(isotypicComponents R M) := fun i =>
    ⟨isotypicComponent R M ((tw T)^[i.val] S0), (tw T)^[i.val] S0, hsimple _, rfl⟩
  have hlt : ∀ i j : Fin r, i < j →
      isotypicComponent R M ((tw T)^[i.val] S0) = isotypicComponent R M ((tw T)^[j.val] S0) →
      False := by
    intro i j hij h
    apply hne
    refine clifford_shift T r hid S0 i.val j.val hij j.2 ?_
    have hle : ((tw T)^[i.val] S0) ≤ isotypicComponent R M ((tw T)^[j.val] S0) := by
      rw [← h]; exact Submodule.le_isotypicComponent _
    have hiso := (le_isotypicComponent_iff (R := R) (M := M)).1 hle
    haveI := hsimple i.val
    haveI : IsSimpleModule R (⊤ : Submodule R ((tw T)^[i.val] S0)) :=
      IsSimpleModule.congr (Submodule.topEquiv (R := R) (M := ((tw T)^[i.val] S0)))
    obtain ⟨e⟩ := hiso ⊤
    exact ⟨(Submodule.topEquiv (R := R) (M := ((tw T)^[i.val] S0))).symm.trans e⟩
  have hinj : Function.Injective c := by
    intro i j hij
    have h : isotypicComponent R M ((tw T)^[i.val] S0) = isotypicComponent R M ((tw T)^[j.val] S0) :=
      congrArg Subtype.val hij
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h1 | h1
    · exact hlt i j h1 h
    · exact hlt j i h1 h.symm
  exact ((sSupIndep_iff _).1 (sSupIndep_isotypicComponents R M)).comp hinj

end abstract

section spec

variable {F : Type*} [Field F] {E : Type*} [Group E] {V : Type*} [AddCommGroup V] [Module F V]

@[expose] noncomputable def twRing (α : MulAut E) : F[E] →+* F[E] :=
  MonoidAlgebra.mapDomainRingHom F (α : E →* E)

theorem twRing_symm (α : MulAut E) (x : F[E]) : twRing (F := F) α⁻¹ (twRing α x) = x := by
  have := congrArg (fun f => f x) (MonoidAlgebra.mapDomainRingHom_comp (R := F) ((α⁻¹ : MulAut E) : E →* E) (α : E →* E))
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  have h2 : ((α⁻¹ : MulAut E) : E →* E).comp (α : E →* E) = MonoidHom.id E := by
    ext e; simp
  rw [h2] at this
  simpa [twRing] using this.symm

instance (α : MulAut E) : RingHomInvPair (twRing (F := F) α) (twRing α⁻¹) :=
  ⟨RingHom.ext (twRing_symm α), RingHom.ext fun x => by simpa using twRing_symm (F := F) α⁻¹ x⟩

instance (α : MulAut E) : RingHomInvPair (twRing (F := F) α⁻¹) (twRing α) :=
  ⟨RingHom.ext fun x => by simpa using twRing_symm (F := F) α⁻¹ x, RingHom.ext (twRing_symm α)⟩

theorem key_cov (σ : Representation F E V) (α : MulAut E) (T : V ≃ₗ[F] V)
    (hcov : ∀ e v, T (σ e v) = σ (α e) (T v)) (r : F[E]) (v : V) :
    T (Representation.asAlgebraHom σ r v) = Representation.asAlgebraHom σ (twRing α r) (T v) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    simp [twRing, MonoidAlgebra.of_apply, hcov]
  | add x y hx hy => simp [map_add, hx, hy]
  | smul c x hx =>
    have : twRing (F := F) α (c • x) = c • twRing α x := by
      simp [twRing, MonoidAlgebra.mapDomain_smul]
    rw [this]; simp [hx]

@[expose] noncomputable def mkSL (σ : Representation F E V) (α : MulAut E) (T : V ≃ₗ[F] V)
    (hcov : ∀ e v, T (σ e v) = σ (α e) (T v)) : σ.asModule →ₛₗ[twRing (F := F) α] σ.asModule where
  toFun x := σ.asModuleEquiv.symm (T (σ.asModuleEquiv x))
  map_add' x y := by simp
  map_smul' r x := by
    apply σ.asModuleEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul]
    exact key_cov σ α T hcov r _

@[expose] noncomputable def mkSLEquiv (σ : Representation F E V) (α : MulAut E) (T : V ≃ₗ[F] V)
    (hcov : ∀ e v, T (σ e v) = σ (α e) (T v)) : σ.asModule ≃ₛₗ[twRing (F := F) α] σ.asModule :=
  LinearEquiv.ofLinear (mkSL σ α T hcov)
    (mkSL σ α⁻¹ T.symm (fun e v => by
      apply T.injective
      simp [hcov]))
    (by ext x; simp [mkSL]) (by ext x; simp [mkSL])

end spec

end CFSG.LinearAlgebra.CoprimeActions.PrimeNormalizerStableIrreducibleType
