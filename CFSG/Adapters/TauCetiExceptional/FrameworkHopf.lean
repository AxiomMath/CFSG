module

public import TauCeti.LinearAlgebra.TensorProduct.Separation
public import Mathlib.RingTheory.Flat.Domain
public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

public noncomputable section

open scoped TensorProduct
open WithConv

namespace CFSG.TauCetiBridge

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem isTorsionFree_pi_frac (ι : Type*) : Module.IsTorsionFree R (ι → K) where
  isSMulRegular r hr v w hvw := by
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr.ne_zero
    funext i
    have := congrFun hvw i
    simp only [Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hr0 this

theorem tensor_eq_zero_of_forall_productMap_eq_zero_frac {A B ι κ : Type*} [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (f : ι → A →ₐ[R] K) (g : κ → B →ₐ[R] K)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    (x : A ⊗[R] B) (hx : ∀ i j, Algebra.TensorProduct.productMap (f i) (g j) x = 0) :
    x = 0 := by
  let F : A →ₗ[R] (ι → K) := LinearMap.pi fun i => (f i).toLinearMap
  let G : B →ₗ[R] (κ → K) := LinearMap.pi fun j => (g j).toLinearMap
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hf a fun i => congrFun ha i
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact hg b fun j => congrFun hb j
  have := isTorsionFree_pi_frac (R := R) (K := K) ι
  have := isTorsionFree_pi_frac (R := R) (K := K) κ
  have : Module.IsTorsionFree R A := hF.moduleIsTorsionFree F fun r a => F.map_smul r a
  have : Module.IsTorsionFree R B := hG.moduleIsTorsionFree G fun r b => G.map_smul r b
  have hinj := TensorProduct.map_injective_of_flat_flat_of_isDomain F G hF hG
  let e := (IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K (ι → K) (κ → K)).symm
  have key : ∀ (i : ι) (j : κ) (y : A ⊗[R] B),
      TensorProduct.lid K K (TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)
        (e (TensorProduct.map F G y))) = Algebra.TensorProduct.productMap (f i) (g j) y := by
    intro i j y
    induction y with
    | tmul a b =>
      change TensorProduct.lid K K (TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)
        (F a ⊗ₜ[K] G b)) = _
      simp [F, G]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hz := TauCeti.tensor_eq_zero_of_forall_lid_map_eq_zero (k := K)
    (fun i => (LinearMap.proj i : (ι → K) →ₗ[K] K))
    (fun j => (LinearMap.proj j : (κ → K) →ₗ[K] K))
    (fun v hv => funext hv) (fun w hw => funext hw) (e (TensorProduct.map F G x))
    (fun i j => (key i j x).trans (hx i j))
  apply hinj
  rw [map_zero]
  exact e.injective (hz.trans e.map_zero.symm)

section Vanishing

variable {H : Type*} [CommRing H] [HopfAlgebra R H]

def fracPointKernel (S : Subgroup (WithConv (H →ₐ[R] K))) : Ideal H :=
  ⨅ g : S, RingHom.ker g.val.ofConv

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem mem_fracPointKernel (S : Subgroup (WithConv (H →ₐ[R] K))) (x : H) :
    x ∈ fracPointKernel S ↔ ∀ g : S, g.val.ofConv x = 0 := by
  simp [fracPointKernel, RingHom.mem_ker]

def fracQuotientEval (S : Subgroup (WithConv (H →ₐ[R] K))) (g : S) :
    H ⧸ fracPointKernel S →ₐ[R] K :=
  Ideal.Quotient.liftₐ _ g.val.ofConv fun x hx ↦ (mem_fracPointKernel S x).mp hx g

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem fracQuotientEval_mk (S : Subgroup (WithConv (H →ₐ[R] K))) (g : S) (x : H) :
    fracQuotientEval S g (Ideal.Quotient.mk (fracPointKernel S) x) = g.val.ofConv x :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem fracQuotientEval_separates (S : Subgroup (WithConv (H →ₐ[R] K)))
    (y : H ⧸ fracPointKernel S) (hy : ∀ g, fracQuotientEval S g y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (fracPointKernel S) y
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  refine (mem_fracPointKernel S y).mpr fun g ↦ ?_
  rw [← fracQuotientEval_mk]
  exact hy g

theorem comul_mem_fracPointKernel (S : Subgroup (WithConv (H →ₐ[R] K)))
    {x : H} (hx : x ∈ fracPointKernel S) :
    Coalgebra.comul (R := R) x ∈
      TauCeti.HopfIdeal.leftTensorIdeal (R := R) (H := H) (fracPointKernel S) ⊔
        TauCeti.HopfIdeal.rightTensorIdeal (R := R) (H := H) (fracPointKernel S) := by
  let q := Ideal.Quotient.mkₐ R (fracPointKernel S)
  have hker : RingHom.ker q = fracPointKernel S := Ideal.Quotient.mkₐ_ker R (fracPointKernel S)
  rw [← hker, ← TauCeti.HopfIdeal.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
    q q (Ideal.Quotient.mkₐ_surjective R _) (Ideal.Quotient.mkₐ_surjective R _), RingHom.mem_ker]
  apply tensor_eq_zero_of_forall_productMap_eq_zero_frac (fracQuotientEval S)
    (fracQuotientEval S) (fracQuotientEval_separates S) (fracQuotientEval_separates S)
  intro g h
  have heq : ∀ y : H ⊗[R] H,
      Algebra.TensorProduct.productMap (fracQuotientEval S g) (fracQuotientEval S h)
          (Algebra.TensorProduct.map q q y) =
        Algebra.TensorProduct.productMap g.val.ofConv h.val.ofConv y := by
    intro y
    induction y with
    | tmul a b => simp [q, fracQuotientEval_mk]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [heq]
  exact (AlgHom.convMul_apply g.val h.val x).symm.trans
    ((mem_fracPointKernel S x).mp hx (g * h))

def fracVanishingIdeal (S : Subgroup (WithConv (H →ₐ[R] K))) : TauCeti.HopfIdeal R H :=
  TauCeti.HopfIdeal.ofIdeal (fracPointKernel S) (fun _ hx ↦ comul_mem_fracPointKernel S hx)
    (fun x hx ↦ by
      have h1 := (mem_fracPointKernel S x).mp hx 1
      simp only [OneMemClass.coe_one] at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).1
        ((AlgHom.convOne_apply x).symm.trans h1))
    (fun x hx ↦ (mem_fracPointKernel S _).mpr fun g ↦ by
      simpa using (mem_fracPointKernel S x).mp hx g⁻¹)

theorem mem_fracVanishingIdeal (S : Subgroup (WithConv (H →ₐ[R] K))) (x : H) :
    x ∈ fracVanishingIdeal S ↔ ∀ g : S, g.val.ofConv x = 0 := by
  rw [fracVanishingIdeal, TauCeti.HopfIdeal.mem_ofIdeal]
  exact mem_fracPointKernel S x

end Vanishing

end CFSG.TauCetiBridge
