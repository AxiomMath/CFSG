module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ1
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open TensorProduct Module

universe u

section Span

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

theorem conj_map_span (a : W ≃ₗ[F] W) (X Y : Subgroup (W ≃ₗ[F] W)) (h : conjSub a X = Y) :
    (Submodule.span F (Set.range fun l : X => ((l : W ≃ₗ[F] W) : Module.End F W))).map
        (a.conjAlgEquiv F).toLinearMap =
      Submodule.span F (Set.range fun l : Y => ((l : W ≃ₗ[F] W) : Module.End F W)) := by
  rw [Submodule.map_span]
  congr 1
  ext T
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
    have hl : a * (l : W ≃ₗ[F] W) * a⁻¹ ∈ Y := by
      rw [← h, mem_conjSub]
      simp [mul_assoc]
    refine ⟨⟨_, hl⟩, ?_⟩
    apply LinearMap.ext
    intro w
    simp [LinearEquiv.conjAlgEquiv_apply]
  · rintro ⟨m, rfl⟩
    have hm : a⁻¹ * (m : W ≃ₗ[F] W) * a ∈ X := by
      have hm' : (m : W ≃ₗ[F] W) ∈ conjSub a X := by
        rw [h]
        exact m.2
      exact mem_conjSub.1 hm'
    refine ⟨_, ⟨⟨_, hm⟩, rfl⟩, ?_⟩
    apply LinearMap.ext
    intro w
    simp [LinearEquiv.conjAlgEquiv_apply]

end Span

section TensorData

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
  [AddCommGroup W] [Module F W] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module F (V i)] [∀ i, Nontrivial (V i)] [∀ i, Module.Finite F (V i)]

theorem finrank_span_of_tensor (e : W ≃ₗ[F] ⨂[F] i, V i) (R : Submodule F (Module.End F W))
    (i : ι)
    (hR : ∀ T : Module.End F W, T ∈ R ↔
      ∃ f : Module.End F (V i), ∀ w, e (T w) = factorEnd i f (e w)) :
    Module.finrank F R = Module.finrank F (V i) ^ 2 := by
  let Φ : Module.End F (V i) →ₗ[F] Module.End F W :=
    (LinearEquiv.conj e.symm).toLinearMap ∘ₗ (factorAlgHom (F := F) (V := V) i).toLinearMap
  have hΦ : ∀ f w, Φ f w = e.symm (factorEnd i f (e w)) := fun f w => by
    simp [Φ, LinearEquiv.conj_apply, factorAlgHom_apply]
  have hinj : Function.Injective Φ := by
    intro f g hfg
    apply factorAlgHom_injective (F := F) (V := V) i
    refine LinearMap.ext fun y => ?_
    have h1 := LinearMap.congr_fun hfg (e.symm y)
    rw [hΦ, hΦ] at h1
    have h2 := congrArg e h1
    simpa [factorAlgHom_apply] using h2
  have hrange : LinearMap.range Φ = R := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact (hR _).2 ⟨f, fun w => by rw [hΦ]; simp⟩
    · intro hT
      obtain ⟨f, hf⟩ := (hR T).1 hT
      refine ⟨f, LinearMap.ext fun w => ?_⟩
      rw [hΦ]
      exact (LinearEquiv.symm_apply_eq e).2 (hf w).symm
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_linearMap F F (V i) (V i), sq]

omit [Fintype ι] [∀ i, Nontrivial (V i)] [∀ i, Module.Finite F (V i)] in
theorem mem_factorAlg_const_iff {U : Type*} [AddCommGroup U] [Module F U]
    (e : W ≃ₗ[F] ⨂[F] i, V i) (τ : ∀ i, V i ≃ₗ[F] U) (R : Submodule F (Module.End F W)) (i : ι)
    (hR : ∀ T : Module.End F W, T ∈ R ↔
      ∃ f : Module.End F (V i), ∀ w, e (T w) = factorEnd i f (e w))
    (X : Module.End F (⨂[F] _ : ι, U)) :
    X ∈ factorAlg (F := F) (V := fun _ : ι => U) i ↔
      ((e.trans (PiTensorProduct.congr τ)).symm.toLinearMap ∘ₗ X ∘ₗ
        (e.trans (PiTensorProduct.congr τ)).toLinearMap) ∈ R := by
  set Θ : (⨂[F] j, V j) ≃ₗ[F] ⨂[F] _ : ι, U := PiTensorProduct.congr τ with hΘ
  have hG1 : ∀ f : Module.End F (V i), Θ.toLinearMap ∘ₗ factorEnd i f ∘ₗ Θ.symm.toLinearMap =
      factorEnd i ((τ i).toLinearMap ∘ₗ f ∘ₗ (τ i).symm.toLinearMap) :=
    fun f => congr_factorEnd_het τ i f
  rw [hR]
  constructor
  · rintro ⟨g, hg⟩
    set f : Module.End F (V i) := (τ i).symm.toLinearMap ∘ₗ g ∘ₗ (τ i).toLinearMap with hf
    refine ⟨f, fun w => ?_⟩
    have h1 := hG1 f
    have h2 : (τ i).toLinearMap ∘ₗ f ∘ₗ (τ i).symm.toLinearMap = g := by
      refine LinearMap.ext fun x => ?_
      simp [hf]
    rw [h2] at h1
    have hg' : factorEnd i g = X := hg
    have hX : X = Θ.toLinearMap ∘ₗ factorEnd i f ∘ₗ Θ.symm.toLinearMap := by
      rw [h1]
      exact hg'.symm
    have h3 : X (Θ (e w)) = Θ (factorEnd i f (e w)) := by
      rw [hX]
      simp
    simp [LinearEquiv.trans_apply, h3]
  · rintro ⟨f, hf⟩
    refine ⟨(τ i).toLinearMap ∘ₗ f ∘ₗ (τ i).symm.toLinearMap, ?_⟩
    show factorEnd i ((τ i).toLinearMap ∘ₗ f ∘ₗ (τ i).symm.toLinearMap) = X
    rw [← hG1 f]
    refine LinearMap.ext fun y => ?_
    have h4 := hf (e.symm (Θ.symm y))
    simp at h4
    have h5 := congrArg Θ h4
    simp at h5
    simpa using h5.symm

end TensorData

section SmallGL

theorem not_perfect_of_finrank_two {F : Type*} [Field F] [Finite F] {U : Type*} [AddCommGroup U]
    [Module F U] [Module.Finite F U] (hF : Nat.card F = 2) (hU : Module.finrank F U = 2)
    {P : Type*} [Group P] [Nontrivial P] [Finite P] (ρ : P →* (U ≃ₗ[F] U))
    (hinj : Function.Injective ρ) (hperf : Group.IsPerfect P) : False := by
  classical
  have hUfin : Finite U := Module.finite_of_finite F
  have hcardU : Nat.card U = 4 := by
    have := Module.natCard_eq_pow_finrank (K := F) (V := U)
    rw [this, hF, hU]
    norm_num
  let X := {u : U // u ≠ 0}
  have hcardX : Nat.card X = 3 := by
    have h1 : Nat.card X + 1 = Nat.card U := by
      have e := Equiv.optionSubtypeNe (0 : U)
      rw [← Nat.card_congr e]
      exact Eq.symm Finite.card_option
    omega
  let φ : (U ≃ₗ[F] U) →* Equiv.Perm X :=
    { toFun := fun x => Equiv.Perm.subtypePerm (x.toEquiv : Equiv.Perm U) (fun u => by simp)
      map_one' := by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hφ : Function.Injective φ := by
    intro x y h
    apply LinearEquiv.ext
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · have h2 := congrArg (fun p => ((p ⟨u, hu⟩ : X) : U)) h
      exact h2
  have hdvd : Nat.card P ∣ Nat.card (Equiv.Perm X) :=
    Subgroup.card_dvd_of_injective (φ.comp ρ) (hφ.comp hinj)
  have h6 : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_perm, hcardX]
    rfl
  have hsq6 : Squarefree (6 : ℕ) := by
    have h23 : (6 : ℕ) = 2 * 3 := rfl
    rw [h23, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have hsq : Squarefree (Nat.card P) := Squarefree.squarefree_of_dvd (h6 ▸ hdvd) hsq6
  have : IsZGroup P := IsZGroup.of_squarefree hsq
  have h1 : commutator P < ⊤ := IsZGroup.commutator_lt P
  exact h1.ne (Group.isPerfect_def.1 hperf)

end SmallGL

section ConjCompat

variable {F : Type*} [Field F] {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
  [Module F N]

theorem conjAlgEquiv_autConj (e : M ≃ₗ[F] N) (a : M ≃ₗ[F] M) (T : Module.End F M) :
    ((autConj e a).conjAlgEquiv F) (e.conjAlgEquiv F T) = e.conjAlgEquiv F (a.conjAlgEquiv F T) := by
  refine LinearMap.ext fun w => ?_
  simp [LinearEquiv.conjAlgEquiv_apply, autConj_apply, autConj_symm_apply]

end ConjCompat

end CFSG.QuasithinUnique.Setup.Layer
