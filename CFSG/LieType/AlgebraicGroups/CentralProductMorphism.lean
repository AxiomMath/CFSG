module

public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import TauCeti.RingTheory.TensorProduct.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Bialgebra.Convolution
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.Product

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralProduct

open CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] def centralProductAlgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) : M →ₐ[k] (T ⊗[k] D) :=
  (Algebra.TensorProduct.map (iT : M →ₐ[k] T) (iD : M →ₐ[k] D)).comp
    (Bialgebra.comulAlgHom k M)

@[expose] def PointImageCentral
    {M T : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k} (iT : M →ₐc[k] T) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A),
    TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain iT t)

omit [IsAlgClosed k] in
theorem pointImageCentral_of_isCentral_ker
    {M T : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k} (iT : M →ₐc[k] T)
    (I : TauCeti.HopfIdeal k M) (hI : I.IsCentral)
    (hker : ∀ x : M, x ∈ I → iT x = 0) : PointImageCentral iT := by
  intro A t
  apply TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup M.obj I hI A
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  rw [TauCeti.AlgHom.mapDomain_apply_apply]
  rw [hker x hx, map_zero]

omit [IsAlgClosed k] in
theorem pointImage_commute
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (A : CommAlgCat.{u} k) (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A)
    (d : TauCeti.HopfAlgebra.points (R := k) (H := D) A) :
    Commute (TauCeti.AlgHom.mapDomain iT t) (TauCeti.AlgHom.mapDomain iD d) :=
  (hT A t).commute (TauCeti.AlgHom.mapDomain iD d)

omit [IsAlgClosed k] in
theorem centralProductAlgHom_point_eq
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D)
    (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k) (H := T ⊗[k] D) A) :
    toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
      TauCeti.AlgHom.mapDomain iT
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).1 *
        TauCeti.AlgHom.mapDomain iD
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).2 := by
  let phi : (M ⊗[k] M) →ₐ[k] A :=
    y.ofConv.comp (Algebra.TensorProduct.map (iT : M →ₐ[k] T) (iD : M →ₐ[k] D))
  have hraw := TauCeti.Bialgebra.toConv_comp_comulAlgHom (R := k) (H := M) (A := A)
    (phi := phi)
  have hleft : phi.comp
      (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := M) (H₂ := M)).toAlgHom =
      (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := T) (H₂ := D)).toAlgHom).comp
        (iT : M →ₐ[k] T) := by
    dsimp only [phi]
    simp only [TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, ← AlgHom.comp_assoc]
  have hright : phi.comp
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := M) (H₂ := M)).toAlgHom =
      (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)).toAlgHom).comp
        (iD : M →ₐ[k] D) := by
    dsimp only [phi]
    simp only [TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, ← AlgHom.comp_assoc]
  have hfst : (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).1 =
      toConv (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := T) (H₂ := D)).toAlgHom) := by
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply, TauCeti.AlgHom.mapDomain_apply]
  have hsnd : (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).2 =
      toConv (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)).toAlgHom) := by
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply, TauCeti.AlgHom.mapDomain_apply]
    rfl
  change toConv (phi.comp (Bialgebra.comulAlgHom k M)) = _
  rw [hraw, hleft, hright, hfst, hsnd]
  rfl

omit [IsAlgClosed k] in
theorem centralProductAlgHom_point_mul
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (y z : WithConv ((T ⊗[k] D) →ₐ[k] k)) :
    toConv ((y * z).ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
      toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) *
        toConv (z.ofConv.comp (centralProductAlgHom (k := k) iT iD)) := by
  let A := CommAlgCat.of k k
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A)
    (H₁ := T) (H₂ := D)
  have hy := centralProductAlgHom_point_eq (k := k) iT iD A y
  have hz := centralProductAlgHom_point_eq (k := k) iT iD A z
  have hyz := centralProductAlgHom_point_eq (k := k) iT iD A (y * z)
  have hcomp : P (y * z) = P y * P z := map_mul P y z
  have hfst : (P (y * z)).1 = (P y).1 * (P z).1 := by
    rw [hcomp]
    rfl
  have hsnd : (P (y * z)).2 = (P y).2 * (P z).2 := by
    rw [hcomp]
    rfl
  have hcomm : Commute (TauCeti.AlgHom.mapDomain iT (P z).1)
      (TauCeti.AlgHom.mapDomain iD (P y).2) :=
    pointImage_commute (k := k) iT iD hT A (P z).1 (P y).2
  calc
    toConv ((y * z).ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
        TauCeti.AlgHom.mapDomain iT (P (y * z)).1 *
          TauCeti.AlgHom.mapDomain iD (P (y * z)).2 := hyz
    _ = TauCeti.AlgHom.mapDomain iT ((P y).1 * (P z).1) *
          TauCeti.AlgHom.mapDomain iD ((P y).2 * (P z).2) := by rw [hfst, hsnd]
    _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iT (P z).1) *
          (TauCeti.AlgHom.mapDomain iD (P y).2 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
      rw [map_mul, map_mul]
    _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iD (P y).2) *
          (TauCeti.AlgHom.mapDomain iT (P z).1 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
      calc
        (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iT (P z).1) *
            (TauCeti.AlgHom.mapDomain iD (P y).2 * TauCeti.AlgHom.mapDomain iD (P z).2) =
          TauCeti.AlgHom.mapDomain iT (P y).1 *
            ((TauCeti.AlgHom.mapDomain iT (P z).1 *
              TauCeti.AlgHom.mapDomain iD (P y).2) *
              TauCeti.AlgHom.mapDomain iD (P z).2) := by rw [mul_assoc, mul_assoc]
        _ = TauCeti.AlgHom.mapDomain iT (P y).1 *
            ((TauCeti.AlgHom.mapDomain iD (P y).2 *
              TauCeti.AlgHom.mapDomain iT (P z).1) *
              TauCeti.AlgHom.mapDomain iD (P z).2) := by rw [hcomm.eq]
        _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iD (P y).2) *
            (TauCeti.AlgHom.mapDomain iT (P z).1 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
          rw [mul_assoc, mul_assoc]
    _ = toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) *
          toConv (z.ofConv.comp (centralProductAlgHom (k := k) iT iD)) := by rw [hy, hz]

@[expose] def centralProductBialgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] : M →ₐc[k] (T ⊗[k] D) :=
  letI : Algebra.FiniteType k (T ⊗[k] D) :=
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) T D
  haveI : IsReduced (T ⊗[k] D) := inferInstance
  bialgHomOfPointMulTo (centralProductAlgHom (k := k) iT iD)
    (centralProductAlgHom_point_mul (k := k) iT iD hT)

@[simp] theorem coe_centralProductBialgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    (centralProductBialgHom (k := k) iT iD hT : M →ₐ[k] (T ⊗[k] D)) =
      centralProductAlgHom (k := k) iT iD := by
  rfl

@[expose] def centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    M ⟶ TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D :=
  TauCeti.FiniteTypeCommHopfAlgCat.ofHom (centralProductBialgHom (k := k) iT iD hT)

@[simp] theorem toBialgHom_centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (centralProductHom (k := k) iT iD hT) =
      centralProductBialgHom (k := k) iT iD hT :=
  rfl

theorem centralProductBialgHom_point_eq
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D]
    (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k) (H := T ⊗[k] D) A) :
    TauCeti.AlgHom.mapDomain (centralProductBialgHom (k := k) iT iD hT) y =
      TauCeti.AlgHom.mapDomain iT
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).1 *
        TauCeti.AlgHom.mapDomain iD
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).2 := by
  rw [← centralProductAlgHom_point_eq (k := k) iT iD A y]
  rw [TauCeti.AlgHom.mapDomain_apply, coe_centralProductBialgHom]

omit [IsAlgClosed k] in
theorem isCentralPoint_of_mapDomain_of_surjective
    {M T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (i : M →ₐc[k] T) (hi : Function.Surjective i)
    {A : CommAlgCat.{u} k} (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A)
    (ht : TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain i t)) :
    TauCeti.HopfAlgebra.IsCentralPoint t := by
  rw [TauCeti.HopfAlgebra.isCentralPoint_def] at ht ⊢
  intro B _ _ φ x
  rw [commute_iff_eq]
  apply TauCeti.CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective
    (_root_.CommHopfAlgCat.ofHom i) hi (CommAlgCat.of k B)
  change TauCeti.AlgHom.mapDomain i _ = TauCeti.AlgHom.mapDomain i _
  simp only [map_mul]
  have h := ht φ (TauCeti.AlgHom.mapDomain i x)
  have hn := DFunLike.congr_fun (TauCeti.AlgHom.mapValue_mapDomain i φ) t
  simp only [MonoidHom.comp_apply] at hn
  rw [hn]
  exact h.eq

omit [IsAlgClosed k] in
theorem isCentralPoint_product_of_components
    (T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {A : CommAlgCat.{u} k}
    (y : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D) A)
    (ht : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := D) (A := A) y).1)
    (hd : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := D) (A := A) y).2) :
    TauCeti.HopfAlgebra.IsCentralPoint y := by
  rw [TauCeti.HopfAlgebra.isCentralPoint_def] at ht hd ⊢
  intro B _ _ φ x
  rw [commute_iff_eq]
  let Bc := CommAlgCat.of k B
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := D) (A := Bc)
  apply P.injective
  simp only [P, map_mul,
    TauCeti.AffineGroup.Product.pointsMulEquiv_mapValue (R := k)
      (H₁ := T) (H₂ := D) (A := A) (B := Bc) φ y]
  exact Prod.ext (ht φ (P x).1).eq (hd φ (P x).2).eq

theorem isCentral_kernel_centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D)
    (hT : PointImageCentral iT)
    (hiT : Function.Surjective iT) (hiD : Function.Surjective iD)
    [IsReduced T] [IsReduced D] :
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom).IsCentral := by
  change ∀ (A : CommAlgCat.{u} k) (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A),
    TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain iT t) at hT
  apply (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint _ _).2
  intro A y hy
  have hy1 : TauCeti.AlgHom.mapDomain (centralProductBialgHom iT iD hT) y = 1 :=
    (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (centralProductHom iT iD hT).hom A y).2 hy
  have heq := centralProductBialgHom_point_eq iT iD hT A y
  rw [hy1] at heq
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := D) (A := A)
  have htimage : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain iT (P y).1) := hT A (P y).1
  have hdimage : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain iD (P y).2) := by
    have hprod : TauCeti.AlgHom.mapDomain iT (P y).1 *
        TauCeti.AlgHom.mapDomain iD (P y).2 = 1 := heq.symm
    have hdinv : TauCeti.AlgHom.mapDomain iD (P y).2 =
        (TauCeti.AlgHom.mapDomain iT (P y).1)⁻¹ := by
      have h := congrArg (fun x => (TauCeti.AlgHom.mapDomain iT (P y).1)⁻¹ * x) hprod
      simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using h
    rw [hdinv]
    exact htimage.inv
  apply isCentralPoint_product_of_components T D y
  · exact isCentralPoint_of_mapDomain_of_surjective iT hiT (P y).1 htimage
  · exact isCentralPoint_of_mapDomain_of_surjective iD hiD (P y).2 hdimage

omit [IsAlgClosed k] in
theorem isCentralPoint_snd_of_product
    (T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {A : CommAlgCat.{u} k}
    (q : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D) A)
    (hq : TauCeti.HopfAlgebra.IsCentralPoint q) :
    TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
        (H₁ := T) (H₂ := D) (A := A) q).2 := by
  rw [TauCeti.HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ x
  rw [commute_iff_eq]
  let Bc : CommAlgCat.{u} k := CommAlgCat.of k B
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
    (H₁ := T) (H₂ := D) (A := Bc)
  let x' : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D) Bc := P.symm (1, x)
  have hx' : (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
      (H₁ := T) (H₂ := D) (A := Bc) x').2 = x := by
    dsimp only [x']
    rw [MulEquiv.apply_symm_apply]
  have hcomm := ((TauCeti.HopfAlgebra.isCentralPoint_def _).1 hq) φ x'
  have hmap := hcomm.map (TauCeti.AlgHom.mapDomain
    (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)))
  have hnat := DFunLike.congr_fun
    (TauCeti.AlgHom.mapValue_mapDomain
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)) φ) q
  simp only [MonoidHom.comp_apply] at hnat
  rw [hnat] at hmap
  rw [show TauCeti.AlgHom.mapDomain
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)) x' =
        (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
          (H₁ := T) (H₂ := D) (A := Bc) x').2 from rfl] at hmap
  rw [hx'] at hmap
  simpa only [TauCeti.AffineGroup.Product.pointsMulEquiv_apply] using hmap.eq

abbrev kernelQuotient
    (M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D)
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom)

abbrev kernelQuotientMap
    (M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D ⟶
      kernelQuotient M T D iT iD hT :=
  TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D)
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom)

abbrev kernelProjection
    (M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    D →ₐc[k] kernelQuotient M T D iT iD hT :=
  (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (kernelQuotientMap M T D iT iD hT)).comp
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T D))

theorem kernelProjection_eq_includeLeft
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] (m : M) :
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (kernelQuotientMap M T D iT iD hT)
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T D) (iT m)) =
      kernelProjection M T D iT iD hT (iD (HopfAlgebra.antipode k m)) := by
  let TD := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom
  let K := kernelQuotient M T D iT iD hT
  let π : TD →ₐc[k] K := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (kernelQuotientMap M T D iT iD hT)
  let A : CommAlgCat.{u} k := CommAlgCat.of k K
  let q : TauCeti.HopfAlgebra.points (R := k) (H := TD) A := toConv π
  have hqmem : q ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup TD.obj I A := by
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change π x = 0
    exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff TD I x).2
      (TauCeti.HopfIdeal.mem_toIdeal.mpr hx)
  have hq1 : TauCeti.AlgHom.mapDomain (centralProductBialgHom iT iD hT) q = 1 := by
    have h := (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (centralProductHom iT iD hT).hom A q).2 hqmem
    change toConv (q.ofConv.comp
      (centralProductBialgHom iT iD hT : M →ₐ[k] TD)) = 1 at h
    simpa only [TauCeti.AlgHom.mapDomain_apply] using h
  have hpoint := centralProductBialgHom_point_eq iT iD hT A q
  rw [hq1] at hpoint
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
    (H₁ := T) (H₂ := D) (A := A)
  let t : WithConv (M →ₐ[k] K) := TauCeti.AlgHom.mapDomain iT (P q).1
  let d : WithConv (M →ₐ[k] K) := TauCeti.AlgHom.mapDomain iD (P q).2
  have hprod : t * d = 1 := hpoint.symm
  have ht : t = d⁻¹ := by
    calc
      t = t * 1 := (mul_one t).symm
      _ = t * (d * d⁻¹) := by rw [mul_inv_cancel]
      _ = (t * d) * d⁻¹ := by rw [mul_assoc]
      _ = d⁻¹ := by rw [hprod, one_mul]
  have heval := congrArg (fun w : WithConv (M →ₐ[k] K) => w.ofConv m) ht
  have hleft : t.ofConv m =
      π (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T D) (iT m)) := by
    dsimp only [t, P]
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply]
    simp only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv]
    rfl
  have hright : (d⁻¹).ofConv m =
      kernelProjection M T D iT iD hT (iD (HopfAlgebra.antipode k m)) := by
    rw [TauCeti.AlgHom.convInv_apply]
    dsimp only [d, P]
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply]
    simp only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv]
    rfl
  rw [← hleft, heval, hright]

theorem kernelProjection_surjective
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (hiT : Function.Surjective iT)
    [IsReduced T] [IsReduced D] :
    Function.Surjective (kernelProjection M T D iT iD hT) := by
  let TD := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom
  let K := kernelQuotient M T D iT iD hT
  let π : TD →ₐc[k] K := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (kernelQuotientMap M T D iT iD hT)
  let di : D →ₐc[k] K := kernelProjection M T D iT iD hT
  have hπ_surj : Function.Surjective π := by
    change Function.Surjective (TauCeti.CommHopfAlgCat.mkQuotient TD.obj I).hom
    exact TauCeti.CommHopfAlgCat.mkQuotient_surjective TD.obj I
  have hrange : ∀ x : T ⊗[k] D, π x ∈ Set.range di := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
        obtain ⟨m, hm⟩ := hiT a
        have hident := kernelProjection_eq_includeLeft iT iD hT m
        have ha : π (a ⊗ₜ[k] (1 : D)) =
            di (iD (HopfAlgebra.antipode k m)) := by
          rw [← hm]
          have hident' := hident
          rw [TauCeti.FiniteTypeCommHopfAlgCat.includeLeft_apply T D (iT m)] at hident'
          simpa only [π, di] using hident'
        have hb : π ((1 : T) ⊗ₜ[k] b) = di b := by
          rw [← TauCeti.FiniteTypeCommHopfAlgCat.includeRight_apply T D b]
          rfl
        refine ⟨iD (HopfAlgebra.antipode k m) * b, ?_⟩
        calc
          di (iD (HopfAlgebra.antipode k m) * b) =
              di (iD (HopfAlgebra.antipode k m)) * di b := map_mul _ _ _
          _ = π (a ⊗ₜ[k] (1 : D)) * π ((1 : T) ⊗ₜ[k] b) := by rw [← ha, ← hb]
          _ = π ((a ⊗ₜ[k] (1 : D)) * ((1 : T) ⊗ₜ[k] b)) := (map_mul _ _ _).symm
          _ = π (a ⊗ₜ[k] b) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
        obtain ⟨u, hu⟩ := hx
        obtain ⟨v, hv⟩ := hy
        refine ⟨u + v, ?_⟩
        rw [map_add, hu, hv, map_add]
  intro y
  obtain ⟨x, rfl⟩ := hπ_surj y
  exact hrange x

theorem kernelProjection_isCentralPoint
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (hiT : Function.Surjective iT) (hiD : Function.Surjective iD)
    [IsReduced T] [IsReduced D]
    {A : CommAlgCat.{u} k}
    (z : TauCeti.HopfAlgebra.points (R := k)
      (H := kernelQuotient M T D iT iD hT) A) :
    TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain (kernelProjection M T D iT iD hT) z) := by
  let TD := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom
  let K := kernelQuotient M T D iT iD hT
  let π : TD →ₐc[k] K := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (kernelQuotientMap M T D iT iD hT)
  let di : D →ₐc[k] K := kernelProjection M T D iT iD hT
  let q : TauCeti.HopfAlgebra.points (R := k) (H := TD) A :=
    TauCeti.AlgHom.mapDomain π z
  have hqmem : q ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup TD.obj I A := by
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change z.ofConv (π x) = 0
    rw [(TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff TD I x).2
      (TauCeti.HopfIdeal.mem_toIdeal.mpr hx), map_zero]
  have hqcentral : TauCeti.HopfAlgebra.IsCentralPoint q :=
    (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint TD.obj I).1
      (isCentral_kernel_centralProductHom iT iD hT hiT hiD) A q hqmem
  have hsnd := isCentralPoint_snd_of_product T D q hqcentral
  have hdi_eq : TauCeti.AlgHom.mapDomain di z =
      (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k)
        (H₁ := T) (H₂ := D) (A := A) q).2 := by
    dsimp only [di, q, π]
    rw [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapDomain_apply,
      TauCeti.AffineGroup.Product.pointsMulEquiv_apply]
    rfl
  simpa only [di, hdi_eq] using hsnd

theorem moduleFinite_kernelQuotient
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (hiT : Function.Surjective iT) (hiD : Function.Surjective iD)
    [IsReduced T] [IsReduced D]
    (hD : TauCeti.semisimpleCommHopfAlgProperty k D) :
    Module.Finite k (kernelQuotient M T D iT iD hT) := by
  let TD := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal (centralProductHom iT iD hT).hom
  let K := kernelQuotient M T D iT iD hT
  let di : D →ₐc[k] K := kernelProjection M T D iT iD hT
  have hdi : Function.Surjective di :=
    kernelProjection_surjective iT iD hT hiT
  have hker_central : (TauCeti.HopfIdeal.kerOfSurjective di hdi).IsCentral := by
    apply (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint D.obj _).2
    intro A z hz
    let f : D.obj ⟶ _root_.CommHopfAlgCat.of k K := _root_.CommHopfAlgCat.ofHom di
    have hf : Function.Surjective f.hom := hdi
    change z ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup D.obj
      (TauCeti.HopfIdeal.kerOfSurjective f.hom hf) A at hz
    rw [TauCeti.HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor
      f hf A] at hz
    obtain ⟨z', rfl⟩ := hz
    change TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.AlgHom.mapDomain (kernelProjection M T D iT iD hT) z')
    exact kernelProjection_isCentralPoint iT iD hT hiT hiD z'
  have hcenter_le : TauCeti.CommHopfAlgCat.centerDefiningIdeal D.obj ≤
      TauCeti.HopfIdeal.kerOfSurjective di hdi :=
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal_le_iff D.obj _).2 hker_central
  have hcenter_ring : (TauCeti.CommHopfAlgCat.centerDefiningIdeal D.obj).toIdeal ≤
      RingHom.ker di.toAlgHom.toRingHom := by
    intro x hx
    have hx' : x ∈ (TauCeti.HopfIdeal.kerOfSurjective di hdi).toIdeal :=
      (TauCeti.HopfIdeal.toIdeal_le_toIdeal.mpr hcenter_le) hx
    rw [TauCeti.HopfIdeal.kerOfSurjective_toIdeal] at hx'
    exact hx'
  let C := TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra D.obj
  let f : D.obj ⟶ _root_.CommHopfAlgCat.of k K := _root_.CommHopfAlgCat.ofHom di
  let diLift : C ⟶ _root_.CommHopfAlgCat.of k K :=
    TauCeti.CommHopfAlgCat.liftQuotient
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal D.obj) f hcenter_ring
  have hdiLift : Function.Surjective diLift.hom :=
    TauCeti.CommHopfAlgCat.liftQuotient_surjective_of_surjective
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal D.obj) f hcenter_ring hdi
  have hCfinite : Module.Finite k C := hD.moduleFinite_centerCoordinate
  exact Module.Finite.of_surjective diLift.hom.toAlgHom.toLinearMap hdiLift

theorem moduleFinite_kernel_centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (hiT : Function.Surjective iT) (hiD : Function.Surjective iD)
    [IsReduced T] [IsReduced D]
    (hD : TauCeti.semisimpleCommHopfAlgProperty k D) :
    Module.Finite k
      (T ⊗[k] D ⧸
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal
          (centralProductHom iT iD hT).hom).toIdeal) := by
  simpa only [kernelQuotient, TauCeti.FiniteTypeCommHopfAlgCat.quotient] using
    moduleFinite_kernelQuotient iT iD hT hiT hiD hD

omit [IsAlgClosed k] in
theorem centralProductAlgHom_comp
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D)
    (σM : M →ₐc[k] M) (σT : T →ₐc[k] T) (σD : D →ₐc[k] D)
    (hiT : iT.comp σM = σT.comp iT) (hiD : iD.comp σM = σD.comp iD) :
    (centralProductAlgHom (k := k) iT iD).comp σM =
      (Algebra.TensorProduct.map (σT : T →ₐ[k] T) (σD : D →ₐ[k] D)).comp
        (centralProductAlgHom (k := k) iT iD) := by
  have hiT' : (iT : M →ₐ[k] T).comp (σM : M →ₐ[k] M) =
      (σT : T →ₐ[k] T).comp (iT : M →ₐ[k] T) := by
    rw [← BialgHom.comp_toAlgHom, hiT, BialgHom.comp_toAlgHom]
  have hiD' : (iD : M →ₐ[k] D).comp (σM : M →ₐ[k] M) =
      (σD : D →ₐ[k] D).comp (iD : M →ₐ[k] D) := by
    rw [← BialgHom.comp_toAlgHom, hiD, BialgHom.comp_toAlgHom]
  unfold centralProductAlgHom
  rw [AlgHom.comp_assoc, ← BialgHom.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, hiT', hiD', Algebra.TensorProduct.map_comp,
    AlgHom.comp_assoc]

theorem centralProductBialgHom_comp
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D]
    (σM : M →ₐc[k] M) (σT : T →ₐc[k] T) (σD : D →ₐc[k] D)
    (hiT : iT.comp σM = σT.comp iT) (hiD : iD.comp σM = σD.comp iD) :
    (centralProductBialgHom (k := k) iT iD hT).comp σM =
      (Bialgebra.TensorProduct.map σT σD).comp
        (centralProductBialgHom (k := k) iT iD hT) := by
  apply BialgHom.ext
  intro m
  change (centralProductAlgHom (k := k) iT iD) (σM m) =
    (Algebra.TensorProduct.map (σT : T →ₐ[k] T) (σD : D →ₐ[k] D))
      ((centralProductAlgHom (k := k) iT iD) m)
  exact congrArg (fun f : M →ₐ[k] (T ⊗[k] D) => f m)
    (centralProductAlgHom_comp (k := k) iT iD σM σT σD hiT hiD)

end CFSG.LieType.AlgebraicGroups.CentralProduct
