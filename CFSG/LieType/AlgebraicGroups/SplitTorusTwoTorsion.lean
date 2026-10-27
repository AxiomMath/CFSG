module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.Mathlib.RingTheory.RootsOfUnity.ZModUnits

import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.RingTheory.RootsOfUnity.ZMod
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.ZMod.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

open scoped CFSG.ConvolutionPoints

open CategoryTheory

variable {L : Type} [Field L] [IsAlgClosed L] {R : Type} [CommRing R] [HopfAlgebra L R]
  [Algebra.FiniteType L R]

section TangentMonoidAlgebra

variable {σ : Type} [Fintype σ]

private def exponent (c : σ → L) (m : Multiplicative (σ →₀ ℤ)) : L :=
  (Multiplicative.toAdd m).sum fun i e => e • c i

omit [IsAlgClosed L] [Fintype σ] in
private lemma exponent_mul (c : σ → L) (m m' : Multiplicative (σ →₀ ℤ)) :
    exponent c (m * m') = exponent c m + exponent c m' := by
  classical
  rw [exponent, exponent, exponent, toAdd_mul,
    Finsupp.sum_add_index' (fun i => by simp)
      (fun i e₁ e₂ => add_zsmul (c i) e₁ e₂)]

private noncomputable def pointDerivationLinear (c : σ → L) :
    MonoidAlgebra L (Multiplicative (σ →₀ ℤ)) →ₗ[L] L :=
  (Finsupp.lift L L (Multiplicative (σ →₀ ℤ)) (exponent c)).comp
    (MonoidAlgebra.coeffLinearEquiv (R := L) (S := L) (M := Multiplicative (σ →₀ ℤ))).toLinearMap

omit [IsAlgClosed L] [Fintype σ] in
private lemma pointDerivationLinear_single (c : σ → L)
    (m : Multiplicative (σ →₀ ℤ)) (a : L) :
    pointDerivationLinear c (MonoidAlgebra.single m a) = a * exponent c m := by
  change (Finsupp.lift L L (Multiplicative (σ →₀ ℤ)) (exponent c))
      (Finsupp.single m a) = a * exponent c m
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

private noncomputable def tangentChar
    (D : TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ))))) :
    Multiplicative (σ →₀ ℤ) →* Multiplicative L where
  toFun m := Multiplicative.ofAdd (D.1 (MonoidAlgebra.single m 1))
  map_one' := by
    apply Multiplicative.ext
    change D.1 (MonoidAlgebra.single 1 1) = 0
    rw [← MonoidAlgebra.one_def]
    exact map_one_of_mem_tangentSpace D.2
  map_mul' m m' := by
    apply Multiplicative.ext
    have h := D.2 (MonoidAlgebra.single m 1) (MonoidAlgebra.single m' 1)
    simpa [MonoidAlgebra.single_mul_single, add_comm] using h

private noncomputable def tangentAddHom
    (D : TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ))))) :
    (σ →₀ ℤ) →+ L where
  toFun f := (tangentChar D (Multiplicative.ofAdd f)).toAdd
  map_zero' := by
    change D.1 (MonoidAlgebra.single (Multiplicative.ofAdd (0 : σ →₀ ℤ)) 1) = 0
    rw [show Multiplicative.ofAdd (0 : σ →₀ ℤ) = 1 by rfl, ← MonoidAlgebra.one_def]
    exact map_one_of_mem_tangentSpace D.2
  map_add' f g := by
    rw [ofAdd_add, map_mul]
    rfl

omit [IsAlgClosed L] [Fintype σ] in
private lemma tangent_single_zpow
    (D : TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))))
    (m : Multiplicative (σ →₀ ℤ)) (e : ℤ) :
    D.1 (MonoidAlgebra.single (m ^ e) 1) = e • D.1 (MonoidAlgebra.single m 1) := by
  have h := congrArg Multiplicative.toAdd (map_zpow (tangentChar D) m e)
  simpa [tangentChar, toAdd_pow] using h

omit [IsAlgClosed L] [Fintype σ] in
private lemma tangent_single_eq_smul
    (D : TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))))
    (m : Multiplicative (σ →₀ ℤ)) (a : L) :
    D.1 (MonoidAlgebra.single m a) = a * D.1 (MonoidAlgebra.single m 1) := by
  have h : MonoidAlgebra.single m a = a • MonoidAlgebra.single m (1 : L) := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [h, map_smul]
  simp

omit [IsAlgClosed L] [Fintype σ] in
private lemma pointDerivationLinear_mem (c : σ → L) :
    ∀ x y : MonoidAlgebra L (Multiplicative (σ →₀ ℤ)),
      pointDerivationLinear c (x * y) =
        Coalgebra.counit x * pointDerivationLinear c y +
          Coalgebra.counit y * pointDerivationLinear c x := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => intro y; simp
  | add x y hx hy =>
      intro z
      simp only [add_mul, map_add, hx z, hy z]
      ring
  | single m a =>
      intro y
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y z hy hz =>
          simp only [mul_add, map_add, hy, hz]
          ring
      | single m' a' =>
          rw [MonoidAlgebra.single_mul_single, pointDerivationLinear_single,
            pointDerivationLinear_single, pointDerivationLinear_single, exponent_mul]
          simp only [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
          ring

private noncomputable def pointDerivationOfFamily (c : σ → L) :
    TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))) :=
  ⟨pointDerivationLinear c, pointDerivationLinear_mem c⟩

omit [IsAlgClosed L] [Fintype σ] in
private lemma tangentAddHom_apply
    (D : TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))))
    (f : σ →₀ ℤ) :
    tangentAddHom D f =
      exponent (fun i => D.1 (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) (Multiplicative.ofAdd f) := by
  let F : σ → ℤ →+ L := fun i => (tangentAddHom D).comp (Finsupp.singleAddHom i)
  have hF : Finsupp.liftAddHom F = tangentAddHom D :=
    (Finsupp.liftAddHom (α := σ) (M := ℤ) (N := L)).apply_symm_apply (tangentAddHom D)
  have hF_apply (i : σ) (e : ℤ) :
      F i e = e • D.1 (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single i 1)) 1) := by
    change (tangentChar D (Multiplicative.ofAdd (Finsupp.single i e))).toAdd = _
    rw [show Finsupp.single i e = e • Finsupp.single i (1 : ℤ) by
      rw [Finsupp.smul_single_one]]
    rw [ofAdd_zsmul]
    change D.1 (MonoidAlgebra.single ((Multiplicative.ofAdd (Finsupp.single i 1)) ^ e) 1) =
      e • D.1 (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)
    rw [tangent_single_zpow]
  calc
    tangentAddHom D f = (Finsupp.liftAddHom F) f := by rw [hF]
    _ = f.sum (fun i => F i) := Finsupp.liftAddHom_apply F f
    _ = f.sum (fun i e => e • D.1 (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) := by
        congr 1
        funext i e
        exact hF_apply i e
    _ = exponent (fun i => D.1 (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) (Multiplicative.ofAdd f) := rfl

private noncomputable def tangentEquivFamily :
    TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))) ≃ₗ[L]
        (σ → L) where
  toFun D := fun i =>
    D.1 (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)
  invFun c := pointDerivationOfFamily c
  map_add' D E := by
    funext i
    rfl
  map_smul' a D := by
    funext i
    rfl
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change pointDerivationLinear (fun i => D.1 (MonoidAlgebra.single
      (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) x = D.1 x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | single m a =>
        rw [pointDerivationLinear_single, tangent_single_eq_smul]
        congr 1
        simpa [tangentAddHom, tangentChar] using
          (tangentAddHom_apply D (Multiplicative.toAdd m)).symm
  right_inv c := by
    funext i
    change pointDerivationLinear c
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) = c i
    rw [pointDerivationLinear_single]
    simp [exponent]

omit [IsAlgClosed L] in
private lemma finrank_tangentSpace_monoidAlgebra (σ : Type) [Fintype σ] :
    Module.finrank L (TangentSpace L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ)))
      (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative (σ →₀ ℤ))))) =
        Fintype.card σ := by
  rw [(tangentEquivFamily (σ := σ) (L := L)).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

end TangentMonoidAlgebra

noncomputable def tangentEquivOfBialgEquiv
    {A B : Type} [CommRing A] [Bialgebra L A] [CommRing B] [Bialgebra L B]
    (e : A ≃ₐc[L] B) :
    TangentSpace L B (Bialgebra.counitAlgHom L B) ≃ₗ[L]
      TangentSpace L A (Bialgebra.counitAlgHom L A) where
  toFun := tangentMap (e : A →ₐ[L] B) (BialgHom.counitAlgHom_comp (e : A →ₐc[L] B))
  invFun := tangentMap (e.symm : B →ₐ[L] A)
    (BialgHom.counitAlgHom_comp (e.symm : B →ₐc[L] A))
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change D.1 ((e : A →ₐ[L] B) ((e.symm : B →ₐ[L] A) x)) = D.1 x
    rw [show (e : A →ₐ[L] B) ((e.symm : B →ₐ[L] A) x) = x by simp]
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change D.1 ((e.symm : B →ₐ[L] A) ((e : A →ₐ[L] B) x)) = D.1 x
    rw [show (e.symm : B →ₐ[L] A) ((e : A →ₐ[L] B) x) = x by simp]
  map_add' D E :=
    (tangentMap (e : A →ₐ[L] B)
      (BialgHom.counitAlgHom_comp (e : A →ₐc[L] B))).map_add D E
  map_smul' a D :=
    (tangentMap (e : A →ₐ[L] B)
      (BialgHom.counitAlgHom_comp (e : A →ₐc[L] B))).map_smul a D

section PrimeTorsion

private noncomputable def sign (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    Multiplicative (Fin n → ZMod p) →* (ULift (Fin n) → Lˣ) where
  toFun x := fun i => (zmodToUnits (L := L) p ζ hζ (x.toAdd i.down)).toMul
  map_one' := by
    funext i
    simp [zmodToUnits]
  map_mul' x y := by
    funext i
    simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply, map_add, toMul_add]

omit [IsAlgClosed L] in
private lemma sign_injective (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    Function.Injective (sign (L := L) p ζ hζ n) := by
  intro x y hxy
  apply Multiplicative.ext
  funext i
  have h := congrFun hxy (ULift.up i)
  have hs : zmodToUnits (L := L) p ζ hζ (x.toAdd i) =
      zmodToUnits (L := L) p ζ hζ (y.toAdd i) := by
    apply Additive.ext
    simpa [sign] using h
  exact zmodToUnits_injective (L := L) p ζ hζ hs

omit [IsAlgClosed L] in
private lemma mem_sign_range (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (n : ℕ)
    (c : ULift (Fin n) → Lˣ) :
    c ∈ (sign (L := L) p ζ hζ n).range ↔ c ^ p = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    funext i
    simpa [sign, zmodToUnits, rootsOfUnityAddHom] using
      (mem_rootsOfUnity p ((hζ.zmodEquivRootsOfUnity (x.toAdd i.down)).toMul : Lˣ)).1
        (hζ.zmodEquivRootsOfUnity (x.toAdd i.down)).toMul.2
  · intro hc
    have hci : ∀ i, c i ^ p = 1 := by
      intro i
      simpa [Pi.pow_apply] using congrFun hc i
    refine ⟨Multiplicative.ofAdd fun i : Fin n =>
      hζ.zmodEquivRootsOfUnity.symm (Additive.ofMul
        ⟨c (ULift.up i), (mem_rootsOfUnity p (c (ULift.up i))).2 (hci (ULift.up i))⟩), ?_⟩
    funext i
    simp [sign, zmodToUnits, rootsOfUnityAddHom]

theorem exists_finrank_tangent_coordinateEquiv_of_torus
    (hR : TauCeti.torusCommHopfAlgProperty L (TauCeti.FiniteTypeCommHopfAlgCat.of L R)) :
    ∃ d : ℕ, Module.finrank L (TangentSpace L R (Bialgebra.counitAlgHom L R)) = d ∧
      Nonempty (MonoidAlgebra L (Multiplicative (Fin d →₀ ℤ)) ≃ₐc[L] R) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_coordinateEquiv_of_torus (TauCeti.FiniteTypeCommHopfAlgCat.of L R) hR
  have hfin : Module.finrank L (TangentSpace L R (Bialgebra.counitAlgHom L R)) = n :=
    (tangentEquivOfBialgEquiv (L := L) e).finrank_eq.trans
      (by simpa using finrank_tangentSpace_monoidAlgebra (L := L) (σ := Fin n))
  exact ⟨n, hfin, ⟨e⟩⟩

theorem exists_finrank_tangent_pointsMulEquiv_of_torus
    (hR : TauCeti.torusCommHopfAlgProperty L (TauCeti.FiniteTypeCommHopfAlgCat.of L R)) :
    ∃ d : ℕ, Module.finrank L (TangentSpace L R (Bialgebra.counitAlgHom L R)) = d ∧
      Nonempty (WithConv (R →ₐ[L] L) ≃* (ULift.{0} (Fin d) → Lˣ)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_finrank_tangent_coordinateEquiv_of_torus hR
  let ψ : WithConv (R →ₐ[L] L) ≃* (Fin d → Lˣ) :=
    (TauCeti.AlgHom.mapDomainMulEquiv (A := L) e).trans
      (TauCeti.SplitTorus.pointsMulEquiv (R := L) (A := L) (σ := Fin d))
  let ι : (Fin d → Lˣ) ≃* (ULift.{0} (Fin d) → Lˣ) :=
    { toFun := fun f i => f i.down
      invFun := fun f i => f (ULift.up i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact ⟨d, hd, ⟨ψ.trans ι⟩⟩

private theorem exists_finrank_tangent_primeTorsion_aux {p : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0)
    (hR : TauCeti.torusCommHopfAlgProperty L (TauCeti.FiniteTypeCommHopfAlgCat.of L R)) :
    ∃ d : ℕ, Module.finrank L (TangentSpace L R (Bialgebra.counitAlgHom L R)) = d ∧
      ∃ ι : Multiplicative (Fin d → ZMod p) →* WithConv (R →ₐ[L] L),
        Function.Injective ι ∧ ∀ g : WithConv (R →ₐ[L] L), g ∈ ι.range ↔ g ^ p = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := p) hpL
  have hζ' : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.mpr hζ
  obtain ⟨n, hfin, ⟨ψ⟩⟩ := exists_finrank_tangent_pointsMulEquiv_of_torus hR
  let ι : Multiplicative (Fin n → ZMod p) →* WithConv (R →ₐ[L] L) :=
    ψ.symm.toMonoidHom.comp (sign (L := L) p ζ hζ' n)
  have hι : Function.Injective ι :=
    ψ.symm.injective.comp (sign_injective (L := L) p ζ hζ' n)
  have hrange : ∀ g : WithConv (R →ₐ[L] L), g ∈ ι.range ↔ g ^ p = 1 := by
    have hsr : ∀ c : ULift (Fin n) → Lˣ,
        c ∈ (sign (L := L) p ζ hζ' n).range ↔ c ^ p = 1 :=
      mem_sign_range (L := L) p ζ hζ' n
    intro g
    constructor
    · intro hg
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
      apply ψ.injective
      rw [map_pow, map_one]
      have hψx : ψ (ι x) = sign (L := L) p ζ hζ' n x := by
        simp [ι]
      rw [hψx]
      exact (hsr (sign (L := L) p ζ hζ' n x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    · intro hg
      have hmem : ψ g ∈ (sign (L := L) p ζ hζ' n).range :=
        (hsr (ψ g)).mpr (by rw [← map_pow, hg, map_one])
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
      refine MonoidHom.mem_range.mpr ⟨x, ?_⟩
      rw [show ι x = ψ.symm (sign (L := L) p ζ hζ' n x) from rfl, hx,
        ψ.symm_apply_apply]
  exact ⟨n, hfin, ι, hι, hrange⟩

end PrimeTorsion

theorem exists_finrank_tangent_primeTorsion_range_of_torus {p : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0)
    (hR : TauCeti.torusCommHopfAlgProperty L (TauCeti.FiniteTypeCommHopfAlgCat.of L R)) :
    ∃ d : ℕ, Module.finrank L (TangentSpace L R (Bialgebra.counitAlgHom L R)) = d ∧
      ∃ ι : Multiplicative (Fin d → ZMod p) →* WithConv (R →ₐ[L] L),
        Function.Injective ι ∧ (∀ g : WithConv (R →ₐ[L] L), g ∈ ι.range ↔ g ^ p = 1) ∧
          Nonempty (Multiplicative (Fin d → ZMod p) ≃* ι.range) := by
  obtain ⟨d, hd, ι, hι, hrange⟩ := exists_finrank_tangent_primeTorsion_aux (L := L) hp hpL hR
  exact ⟨d, hd, ι, hι, hrange, ⟨MonoidHom.ofInjective hι⟩⟩

end CFSG.LieType.AlgebraicGroups

end
