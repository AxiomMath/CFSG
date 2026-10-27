module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

theorem card_ringAut_and_isCyclic {p n : ℕ} (hp : p.Prime) (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = p ^ n) : Nat.card (RingAut K) = n ∧ IsCyclic (RingAut K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : RingAut K ≃* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x =>
        DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) K))
          (algebraMap (ZMod p) K)) x
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun _ => RingEquiv.ext fun _ => rfl
      right_inv := fun _ => AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine ⟨?_, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  apply Nat.pow_right_injective hp.two_le
  change p ^ Module.finrank (ZMod p) K = p ^ n
  rw [FiniteField.pow_finrank_eq_natCard, hK]

variable (K : Type*) [Field K] (d : ℕ)

@[expose] def unitsPiRingAut : RingAut K →* MulAut (Fin d → Kˣ) where
  toFun σ := MulEquiv.piCongrRight fun _ => Units.mapEquiv σ.toMulEquiv
  map_one' := MulEquiv.ext fun _ => funext fun _ => Units.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => funext fun _ => Units.ext rfl

@[expose] def semilinearAddEquiv (a : Fin d → Kˣ) (σ : RingAut K) :
    (Fin d → K) ≃+ (Fin d → K) where
  toFun x j := a j * σ (x j)
  invFun x j := σ.symm (((a j)⁻¹ : Kˣ) * x j)
  left_inv x := funext fun j => by simp
  right_inv x := funext fun j => by simp
  map_add' x y := funext fun j => by simp [mul_add]

variable (p : ℕ) [Module (ZMod p) K]

@[expose] def semilinearGL (a : Fin d → Kˣ) (σ : RingAut K) :
    LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    { (semilinearAddEquiv K d a σ).toAddMonoidHom.toZModLinearMap p with
      invFun := (semilinearAddEquiv K d a σ).symm
      left_inv := (semilinearAddEquiv K d a σ).left_inv
      right_inv := (semilinearAddEquiv K d a σ).right_inv }

theorem semilinearGL_apply (a : Fin d → Kˣ) (σ : RingAut K) (x : Fin d → K) (j : Fin d) :
    (semilinearGL K d p a σ : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j = a j * σ (x j) :=
  rfl

theorem semilinearGL_mul (a b : Fin d → Kˣ) (σ τ : RingAut K) :
    semilinearGL K d p a σ * semilinearGL K d p b τ =
      semilinearGL K d p (a * unitsPiRingAut K d σ b) (σ * τ) := by
  refine Units.ext (LinearMap.ext fun x => funext fun j => ?_)
  change (a j : K) * σ ((b j : K) * τ (x j)) = ((a j : K) * σ (b j)) * σ (τ (x j))
  rw [map_mul, mul_assoc]

@[expose] def semilinearHom : (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K →*
    LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K) where
  toFun g := semilinearGL K d p g.left g.right
  map_one' := Units.ext (LinearMap.ext fun x => funext fun j => by
    change ((1 : Kˣ) : K) * x j = x j
    rw [Units.val_one, one_mul])
  map_mul' g h := by
    rw [semilinearGL_mul]
    rfl

theorem semilinearHom_apply (g : (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K)
    (x : Fin d → K) (j : Fin d) :
    (semilinearHom K d p g : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j =
      g.left j * g.right (x j) :=
  rfl

theorem semilinearHom_injective (hd : 1 ≤ d) : Function.Injective (semilinearHom K d p) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : ∀ (x : Fin d → K) (j : Fin d), (g.left j : K) * g.right (x j) = x j := fun x j =>
    congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K) =>
      (f : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j) hg
  have hl : g.left = 1 := funext fun j => Units.ext (by simpa using h 1 j)
  have hr : g.right = 1 := RingEquiv.ext fun c => by
    have := h (fun _ => c) ⟨0, hd⟩
    rw [hl] at this
    change g.right c = c
    simpa using this
  exact SemidirectProduct.ext hl hr

@[expose] def diagSemilinearGroup : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) :=
  (semilinearHom K d p).range

@[expose] def diagUnitGroup : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) :=
  ((semilinearHom K d p).comp SemidirectProduct.inl).range

theorem mem_diagSemilinearGroup_iff {g : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)} :
    g ∈ diagSemilinearGroup K d p ↔ ∃ (a : Fin d → Kˣ) (σ : RingAut K), ∀ x j,
      (g : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j = a j * σ (x j) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.left, g.right, fun x j => rfl⟩
  · rintro ⟨a, σ, h⟩
    exact ⟨⟨a, σ⟩, Units.ext (LinearMap.ext fun x => funext fun j => (h x j).symm)⟩

theorem mem_diagUnitGroup_iff {g : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)} :
    g ∈ diagUnitGroup K d p ↔ ∃ a : Fin d → Kˣ, ∀ x j,
      (g : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j = a j * x j := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, fun x j => rfl⟩
  · rintro ⟨a, h⟩
    exact ⟨a, Units.ext (LinearMap.ext fun x => funext fun j => (h x j).symm)⟩

theorem diagUnitGroup_le : diagUnitGroup K d p ≤ diagSemilinearGroup K d p := by
  rintro _ ⟨a, rfl⟩
  exact ⟨SemidirectProduct.inl a, rfl⟩

theorem diagUnitGroup_mul_comm {g h : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)}
    (hg : g ∈ diagUnitGroup K d p) (hh : h ∈ diagUnitGroup K d p) : g * h = h * g := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hh
  rw [← map_mul, ← map_mul, mul_comm]

instance diagUnitGroup_subgroupOf_normal :
    ((diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  obtain ⟨y, hy⟩ := g.2
  have hn : y * SemidirectProduct.inl a * y⁻¹ ∈
      (SemidirectProduct.inl :
        (Fin d → Kˣ) →* (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      SemidirectProduct.rightHom_inl, mul_one, mul_inv_cancel]
  obtain ⟨b, hb⟩ := hn
  refine ⟨b, ?_⟩
  change semilinearHom K d p (SemidirectProduct.inl b) =
    (g : LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) * x * (g : _)⁻¹
  rw [hb, map_mul, map_mul, map_inv, hy,
    show semilinearHom K d p (SemidirectProduct.inl a) = x from ha]
  rfl

variable {K d p} in
@[expose] noncomputable def diagSemilinearEquiv (hd : 1 ≤ d) :
    ((Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K) ≃* diagSemilinearGroup K d p :=
  MonoidHom.ofInjective (semilinearHom_injective K d p hd)

theorem coe_diagSemilinearEquiv (hd : 1 ≤ d) (x : (Fin d → Kˣ) ⋊[unitsPiRingAut K d] RingAut K) :
    ((diagSemilinearEquiv (p := p) hd x : diagSemilinearGroup K d p) :
      LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)) = semilinearHom K d p x :=
  rfl

variable {K d p} in
@[expose] noncomputable def diagSemilinearProj (hd : 1 ≤ d) :
    diagSemilinearGroup K d p →* RingAut K :=
  SemidirectProduct.rightHom.comp (diagSemilinearEquiv (p := p) hd).symm.toMonoidHom

theorem diagSemilinearProj_surjective (hd : 1 ≤ d) :
    Function.Surjective (diagSemilinearProj (K := K) (p := p) hd) :=
  SemidirectProduct.rightHom_surjective.comp (diagSemilinearEquiv hd).symm.surjective

theorem ker_diagSemilinearProj (hd : 1 ≤ d) :
    (diagSemilinearProj (K := K) (p := p) hd).ker =
      (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p) := by
  ext g
  obtain ⟨x, rfl⟩ := (diagSemilinearEquiv (p := p) hd).surjective g
  rw [MonoidHom.mem_ker, diagSemilinearProj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, SemidirectProduct.rightHom_eq_right, Subgroup.mem_subgroupOf,
    coe_diagSemilinearEquiv]
  constructor
  · intro hx
    refine ⟨x.left, ?_⟩
    change semilinearHom K d p (SemidirectProduct.inl x.left) = semilinearHom K d p x
    congr 1
    exact SemidirectProduct.ext rfl hx.symm
  · rintro ⟨a, ha⟩
    have h : semilinearHom K d p (SemidirectProduct.inl a) = semilinearHom K d p x := ha
    rw [← semilinearHom_injective K d p hd h]
    rfl

theorem commutatorElement_mem_diagUnitGroup (hd : 1 ≤ d)
    (hK : ∀ σ τ : RingAut K, σ * τ = τ * σ) (g h : diagSemilinearGroup K d p) :
    ⁅g, h⁆ ∈ (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p) := by
  rw [← ker_diagSemilinearProj K d p hd, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hK _ _

theorem derivedSeries_one_le_diagUnitGroup (hd : 1 ≤ d)
    (hK : ∀ σ τ : RingAut K, σ * τ = τ * σ) :
    derivedSeries (diagSemilinearGroup K d p) 1 ≤
      (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p) := by
  rw [derivedSeries_one, _root_.commutator_def]
  exact Subgroup.commutator_le.2 fun g _ h _ => commutatorElement_mem_diagUnitGroup K d p hd hK g h

theorem derivedSeries_two_diagSemilinearGroup (hd : 1 ≤ d)
    (hK : ∀ σ τ : RingAut K, σ * τ = τ * σ) :
    derivedSeries (diagSemilinearGroup K d p) 2 = ⊥ := by
  have h1 := derivedSeries_one_le_diagUnitGroup K d p hd hK
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono h1 h1).trans (Subgroup.commutator_le.2 fun g hg h hh => ?_)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subtype.ext (diagUnitGroup_mul_comm K d p hg hh)

theorem finite_field_diagonal_semilinear_metabelian (p : ℕ) [Fact p.Prime] {n d : ℕ}
    (_hn : 1 ≤ n) (hd : 1 ≤ d) (K : Type*) [Field K] [Finite K] [Module (ZMod p) K]
    (hK : Nat.card K = p ^ n) :
    (∀ g, g ∈ diagSemilinearGroup K d p ↔ ∃ (a : Fin d → Kˣ) (σ : K ≃+* K), ∀ x j,
      (g : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j = a j * σ (x j)) ∧
    (∀ g, g ∈ diagUnitGroup K d p ↔ ∃ a : Fin d → Kˣ, ∀ x j,
      (g : (Fin d → K) →ₗ[ZMod p] (Fin d → K)) x j = a j * x j) ∧
    diagUnitGroup K d p ≤ diagSemilinearGroup K d p ∧
    (∀ g ∈ diagUnitGroup K d p, ∀ h ∈ diagUnitGroup K d p, g * h = h * g) ∧
    ((diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p)).Normal ∧
    IsCyclic (diagSemilinearGroup K d p ⧸
      (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p)) ∧
    Nat.card (diagSemilinearGroup K d p ⧸
      (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p)) = n ∧
    ⁅diagSemilinearGroup K d p, diagSemilinearGroup K d p⁆ ≤ diagUnitGroup K d p ∧
    derivedSeries (diagSemilinearGroup K d p) 2 = ⊥ ∧
    ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → K)),
      H ≤ diagSemilinearGroup K d p → Group.IsSolvable H := by
  have hker := ker_diagSemilinearProj K d p hd
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK
  have hRcomm : ∀ a b : RingAut K, a * b = b * a := fun a b => IsCyclic.commGroup.mul_comm a b
  let eQ : diagSemilinearGroup K d p ⧸
      (diagUnitGroup K d p).subgroupOf (diagSemilinearGroup K d p) ≃* RingAut K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (diagSemilinearProj_surjective K d p hd))
  have h2 := derivedSeries_two_diagSemilinearGroup K d p hd hRcomm
  have : Group.IsSolvable (diagSemilinearGroup K d p) := ⟨⟨2, h2⟩⟩
  refine ⟨fun g => mem_diagSemilinearGroup_iff K d p, fun g => mem_diagUnitGroup_iff K d p,
    diagUnitGroup_le K d p, fun g hg h hh => diagUnitGroup_mul_comm K d p hg hh, inferInstance,
    isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective,
    (Nat.card_congr eQ.toEquiv).trans hcard, ?_, h2,
    fun H hH => Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hH)⟩
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutatorElement_mem_diagUnitGroup K d p hd hRcomm ⟨g, hg⟩ ⟨h, hh⟩

end CFSG.LocalAnalysis.ComponentInitial
