module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.FixedProduct

open CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k]

instance tensorProductFiniteType (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) :
    Algebra.FiniteType k (T ⊗[k] S) :=
  TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) T S

section Definitions

variable (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)

abbrev productObj : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T S

abbrev productAut (σT : T →ₐc[k] T) (σS : S →ₐc[k] S) :
    productObj T S →ₐc[k] productObj T S :=
  Bialgebra.TensorProduct.map σT σS

abbrev fixedQuotientMapS (S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
    (σS : S →ₐc[k] S) : S →ₐc[k] fixedCoordinate S σS :=
  TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient S (fixedHopfIdeal S σS))

end Definitions

section Norm

variable (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
variable [Coalgebra.IsCocomm k T]
variable (σT : T →ₐc[k] T)
variable (σS : S →ₐc[k] S)

abbrev productTensorMap :
    productObj T S →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS) :=
  Bialgebra.TensorProduct.map (normThreeBialgHom T σT) (fixedQuotientMapS S σS)

theorem productTensorMap_comp_productAut
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (_hσS : (σS.comp σS).comp σS = BialgHom.id k S) :
    (productTensorMap T S σT σS).comp (productAut T S σT σS) =
      productTensorMap T S σT σS := by
  apply BialgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      have hnorm : (normThreeBialgHom T σT) (σT a) = (normThreeBialgHom T σT) a :=
        congrArg (fun f : T →ₐc[k] T => f a) (normThreeBialgHom_comp T σT hσT)
      have hq : fixedQuotientMapS S σS (σS b) = fixedQuotientMapS S σS b :=
        congrArg (fun f : S →ₐc[k] fixedCoordinate S σS => f b)
          (fixedCoordinateHom_comp S σS)
      simp only [BialgHom.comp_apply, productTensorMap, productAut,
        Bialgebra.TensorProduct.map_tmul, fixedQuotientMapS]
      rw [hnorm, hq]
  | add x y hx hy => simp [map_add, hx, hy]

theorem fixedHopfIdeal_le_ker_productTensorMap
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S) :
    (fixedHopfIdeal (productObj T S) (productAut T S σT σS)).toIdeal ≤
      RingHom.ker (productTensorMap T S σT σS).toAlgHom.toRingHom := by
  change (TauCeti.HopfIdeal.equalizer (productAut T S σT σS)
      (BialgHom.id k (productObj T S))).toIdeal ≤
    RingHom.ker (productTensorMap T S σT σS).toAlgHom.toRingHom
  rw [TauCeti.HopfIdeal.equalizer_le_ker_iff]
  intro x
  have h := congrArg (fun f : productObj T S →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS) => f x)
    (productTensorMap_comp_productAut T S σT σS hσT hσS)
  change (productTensorMap T S σT σS) ((productAut T S σT σS) x) =
    (productTensorMap T S σT σS) x
  simpa using h

abbrev productTensorMapHom :
    productObj T S ⟶ TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS) := by
  letI : Algebra.FiniteType k (T ⊗[k] S) := tensorProductFiniteType T S
  letI : Algebra.FiniteType k (T ⊗[k] fixedCoordinate S σS) :=
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) T
      (fixedCoordinate S σS)
  exact TauCeti.FiniteTypeCommHopfAlgCat.ofHom (productTensorMap T S σT σS)

theorem toBialgHom_productTensorMapHom :
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (productTensorMapHom T S σT σS) =
      productTensorMap T S σT σS :=
  rfl

def productFixedCoordinateMap
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S) :
    fixedCoordinate (productObj T S) (productAut T S σT σS) ⟶
      TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS) :=
  TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient
    (fixedHopfIdeal (productObj T S) (productAut T S σT σS))
    (productTensorMapHom T S σT σS)
    (fixedHopfIdeal_le_ker_productTensorMap T S σT σS hσT hσS)

theorem productFixedCoordinateMap_comp_mkQuotient
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S) :
    TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (productObj T S)
        (fixedHopfIdeal (productObj T S) (productAut T S σT σS)) ≫
      productFixedCoordinateMap T S σT σS hσT hσS =
    productTensorMapHom T S σT σS :=
  TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

omit [Coalgebra.IsCocomm k T] in
theorem includeLeft_comp_productAut :
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)).comp σT =
      (productAut T S σT σS).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) := by
  change (TauCeti.Bialgebra.TensorProduct.includeLeft : T →ₐc[k] T ⊗[k] S).comp σT =
    (Bialgebra.TensorProduct.map σT σS).comp
      (TauCeti.Bialgebra.TensorProduct.includeLeft : T →ₐc[k] T ⊗[k] S)
  apply BialgHom.ext
  intro a
  rw [BialgHom.comp_apply, BialgHom.comp_apply,
    TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
    TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
    Bialgebra.TensorProduct.map_tmul, map_one]

omit [Coalgebra.IsCocomm k T] in
theorem includeRight_comp_productAut :
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)).comp σS =
      (productAut T S σT σS).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)) := by
  change (TauCeti.Bialgebra.TensorProduct.includeRight : S →ₐc[k] T ⊗[k] S).comp σS =
    (Bialgebra.TensorProduct.map σT σS).comp
      (TauCeti.Bialgebra.TensorProduct.includeRight : S →ₐc[k] T ⊗[k] S)
  apply BialgHom.ext
  intro b
  rw [BialgHom.comp_apply, BialgHom.comp_apply,
    TauCeti.Bialgebra.TensorProduct.includeRight_apply,
    TauCeti.Bialgebra.TensorProduct.includeRight_apply,
    Bialgebra.TensorProduct.map_tmul, map_one]

theorem productTensorMap_comp_includeLeft :
    (productTensorMap T S σT σS).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) =
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T (fixedCoordinate S σS))).comp
        (normThreeBialgHom T σT) := by
  change (Bialgebra.TensorProduct.map (normThreeBialgHom T σT) (fixedQuotientMapS S σS)).comp
      (TauCeti.Bialgebra.TensorProduct.includeLeft : T →ₐc[k] T ⊗[k] S) =
    (TauCeti.Bialgebra.TensorProduct.includeLeft :
      T →ₐc[k] T ⊗[k] fixedCoordinate S σS).comp (normThreeBialgHom T σT)
  apply BialgHom.ext
  intro a
  rw [BialgHom.comp_apply, BialgHom.comp_apply,
    TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
    TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
    Bialgebra.TensorProduct.map_tmul, map_one]

theorem productTensorMap_comp_includeRight :
    (productTensorMap T S σT σS).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)) =
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T (fixedCoordinate S σS))).comp
        (fixedQuotientMapS S σS) := by
  change (Bialgebra.TensorProduct.map (normThreeBialgHom T σT) (fixedQuotientMapS S σS)).comp
      (TauCeti.Bialgebra.TensorProduct.includeRight : S →ₐc[k] T ⊗[k] S) =
    (TauCeti.Bialgebra.TensorProduct.includeRight :
      fixedCoordinate S σS →ₐc[k] T ⊗[k] fixedCoordinate S σS).comp
      (fixedQuotientMapS S σS)
  apply BialgHom.ext
  intro b
  rw [BialgHom.comp_apply, BialgHom.comp_apply,
    TauCeti.Bialgebra.TensorProduct.includeRight_apply,
    TauCeti.Bialgebra.TensorProduct.includeRight_apply,
    Bialgebra.TensorProduct.map_tmul, map_one]

omit [Coalgebra.IsCocomm k T] in
theorem pointsMulEquiv_fst_eq
    (A : CommAlgCat.{u} k)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := productObj T S) A) :
    (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S x).1 =
      TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) x := by
  rw [TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv_fst]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  rw [TauCeti.FiniteTypeCommHopfAlgCat.pointsFunctor_map_app_apply_apply]
  rfl

omit [Coalgebra.IsCocomm k T] in
theorem pointsMulEquiv_snd_eq
    (A : CommAlgCat.{u} k)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := productObj T S) A) :
    (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S x).2 =
      TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)) x := by
  rw [TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv_snd]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  rw [TauCeti.FiniteTypeCommHopfAlgCat.pointsFunctor_map_app_apply_apply]
  rfl

theorem exists_mapDomain_productFixedCoordinateMap_eq_pow_three
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S)
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (productObj T S) (productAut T S σT σS))
      (CommAlgCat.of k k)) :
    ∃ y : TauCeti.HopfAlgebra.points (R := k)
        (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS))
        (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (productFixedCoordinateMap T S σT σS hσT hσS)) y = x ^ 3 := by
  let A := CommAlgCat.of k k
  let P := productObj T S
  let X := fixedCoordinate P (productAut T S σT σS)
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS)
  let IP := fixedHopfIdeal P (productAut T S σT σS)
  let IS := fixedHopfIdeal S σS
  let qP : P →ₐc[k] X :=
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient P IP)
  let qS : S →ₐc[k] fixedCoordinate S σS := fixedQuotientMapS S σS
  let pMapP := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S
  let pMapQ := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T (fixedCoordinate S σS)
  let j : P →ₐc[k] Q := productTensorMap T S σT σS
  let xP : TauCeti.HopfAlgebra.points (R := k) (H := P) A :=
    TauCeti.AlgHom.mapDomain qP x
  let t : TauCeti.HopfAlgebra.points (R := k) (H := T) A := (pMapP xP).1
  let s : TauCeti.HopfAlgebra.points (R := k) (H := S) A := (pMapP xP).2
  have hxP : TauCeti.AlgHom.mapDomain (productAut T S σT σS) xP = xP := by
    change TauCeti.AlgHom.mapDomain (productAut T S σT σS)
        (TauCeti.AlgHom.mapDomain qP x) = TauCeti.AlgHom.mapDomain qP x
    rw [← MonoidHom.comp_apply]
    rw [← TauCeti.AlgHom.mapDomain_comp (ψ := qP) (φ := productAut T S σT σS)]
    rw [fixedCoordinateHom_comp P (productAut T S σT σS)]
  have hxT : TauCeti.AlgHom.mapDomain σT t = t := by
    have ht : t = TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) xP :=
      pointsMulEquiv_fst_eq T S A xP
    calc
      TauCeti.AlgHom.mapDomain σT t =
          TauCeti.AlgHom.mapDomain
            ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)).comp σT) xP := by
        rw [ht, ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp
          (ψ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))
          (φ := σT)]
      _ = TauCeti.AlgHom.mapDomain
            ((productAut T S σT σS).comp
              (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))) xP := by
        rw [includeLeft_comp_productAut]
      _ = TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))
            (TauCeti.AlgHom.mapDomain (productAut T S σT σS) xP) := by
        rw [TauCeti.AlgHom.mapDomain_comp
          (ψ := productAut T S σT σS)
          (φ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)), MonoidHom.comp_apply]
      _ = TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) xP := by
        rw [hxP]
      _ = t := ht.symm
  have hxS : TauCeti.AlgHom.mapDomain σS s = s := by
    have hs : s = TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)) xP :=
      pointsMulEquiv_snd_eq T S A xP
    calc
      TauCeti.AlgHom.mapDomain σS s =
          TauCeti.AlgHom.mapDomain
            ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)).comp σS) xP := by
        rw [hs, ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp
          (ψ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))
          (φ := σS)]
      _ = TauCeti.AlgHom.mapDomain
            ((productAut T S σT σS).comp
              (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))) xP := by
        rw [includeRight_comp_productAut]
      _ = TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))
            (TauCeti.AlgHom.mapDomain (productAut T S σT σS) xP) := by
        rw [TauCeti.AlgHom.mapDomain_comp
          (ψ := productAut T S σT σS)
          (φ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)), MonoidHom.comp_apply]
      _ = TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)) xP := by
        rw [hxP]
      _ = s := hs.symm
  have hs0 : ∀ h : S, h ∈ IS → s.ofConv h = 0 := by
    intro h hh
    have hker : IS.toIdeal ≤ RingHom.ker s.ofConv.toRingHom := by
      change (TauCeti.HopfIdeal.equalizer σS (BialgHom.id k S)).toIdeal ≤
        RingHom.ker s.ofConv.toRingHom
      rw [TauCeti.HopfIdeal.equalizer_le_ker_iff]
      intro a
      have ha := congrArg
        (fun p : TauCeti.HopfAlgebra.points (R := k) (H := S) A => p.ofConv a) hxS
      rw [TauCeti.AlgHom.mapDomain_apply_apply] at ha
      simpa using ha
    exact RingHom.mem_ker.mp (hker (TauCeti.HopfIdeal.mem_toIdeal.mpr hh))
  let s' : TauCeti.HopfAlgebra.points (R := k) (H := fixedCoordinate S σS) A :=
    TauCeti.CommHopfAlgCat.liftQuotientPoint S.obj IS A s hs0
  have hs' : TauCeti.AlgHom.mapDomain qS s' = s := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    change s'.ofConv ((TauCeti.CommHopfAlgCat.mkQuotient S.obj IS).hom a) = s.ofConv a
    rw [TauCeti.CommHopfAlgCat.mkQuotient_apply]
    exact TauCeti.CommHopfAlgCat.liftQuotientPoint_mk S.obj IS A s hs0 a
  let y : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS)) A :=
    pMapQ.symm (t, s' ^ 3)
  have hy : pMapQ y = (t, s' ^ 3) := by
    exact pMapQ.apply_symm_apply (t, s' ^ 3)
  have hy1 : (pMapQ y).1 = t := by
    rw [hy]
  have hy2 : (pMapQ y).2 = s' ^ 3 := by
    rw [hy]
  have hnormT : TauCeti.AlgHom.mapDomain (normThreeBialgHom T σT) t = t ^ 3 := by
    calc
      TauCeti.AlgHom.mapDomain (normThreeBialgHom T σT) t =
          t * TauCeti.AlgHom.mapDomain σT t *
            TauCeti.AlgHom.mapDomain (σT.comp σT) t :=
        normThreeBialgHom_on_points T σT t
      _ = t * t * t := by
        rw [hxT]
        have h2 : TauCeti.AlgHom.mapDomain (σT.comp σT) t = t := by
          rw [TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply, hxT, hxT]
        rw [h2]
      _ = t ^ 3 := by simp [pow_succ]
  have hfst : (pMapP (TauCeti.AlgHom.mapDomain j y)).1 = t ^ 3 := by
    calc
      (pMapP (TauCeti.AlgHom.mapDomain j y)).1 =
          TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))
            (TauCeti.AlgHom.mapDomain j y) :=
        pointsMulEquiv_fst_eq T S A _
      _ = TauCeti.AlgHom.mapDomain
            (j.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))) y := by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp
          (ψ := j)
          (φ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S))]
      _ = TauCeti.AlgHom.mapDomain
            ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T (fixedCoordinate S σS))).comp
              (normThreeBialgHom T σT)) y := by
        rw [productTensorMap_comp_includeLeft]
      _ = TauCeti.AlgHom.mapDomain (normThreeBialgHom T σT)
            (TauCeti.AlgHom.mapDomain
              (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T (fixedCoordinate S σS))) y) := by
        rw [TauCeti.AlgHom.mapDomain_comp
          (ψ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T (fixedCoordinate S σS)))
          (φ := normThreeBialgHom T σT), MonoidHom.comp_apply]
      _ = TauCeti.AlgHom.mapDomain (normThreeBialgHom T σT) t := by
        rw [← pointsMulEquiv_fst_eq T (fixedCoordinate S σS) A y, hy1]
      _ = t ^ 3 := hnormT
  have hsnd : (pMapP (TauCeti.AlgHom.mapDomain j y)).2 = s ^ 3 := by
    calc
      (pMapP (TauCeti.AlgHom.mapDomain j y)).2 =
          TauCeti.AlgHom.mapDomain
            (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))
            (TauCeti.AlgHom.mapDomain j y) :=
        pointsMulEquiv_snd_eq T S A _
      _ = TauCeti.AlgHom.mapDomain
            (j.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))) y := by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp
          (ψ := j)
          (φ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S))]
      _ = TauCeti.AlgHom.mapDomain
            ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
              (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T (fixedCoordinate S σS))).comp
              (fixedQuotientMapS S σS)) y := by
        rw [productTensorMap_comp_includeRight]
      _ = TauCeti.AlgHom.mapDomain (fixedQuotientMapS S σS)
            (TauCeti.AlgHom.mapDomain
              (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
                (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T (fixedCoordinate S σS))) y) := by
        rw [TauCeti.AlgHom.mapDomain_comp
          (ψ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T (fixedCoordinate S σS)))
          (φ := fixedQuotientMapS S σS), MonoidHom.comp_apply]
      _ = TauCeti.AlgHom.mapDomain qS (s' ^ 3) := by
        rw [← pointsMulEquiv_snd_eq T (fixedCoordinate S σS) A y, hy2]
      _ = (TauCeti.AlgHom.mapDomain qS s') ^ 3 := by
        rw [map_pow]
      _ = s ^ 3 := by
        rw [hs']
  have hpair : pMapP (TauCeti.AlgHom.mapDomain j y) = (t ^ 3, s ^ 3) :=
    Prod.ext hfst hsnd
  have hxP_pow : pMapP (xP ^ 3) = (t ^ 3, s ^ 3) := by
    rw [map_pow]
    rfl
  have hcalc : TauCeti.AlgHom.mapDomain j y = xP ^ 3 := by
    apply pMapP.injective
    rw [hpair, hxP_pow]
  have hΦcomp : (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (productFixedCoordinateMap T S σT σS hσT hσS)).comp qP = j := by
    have h := productFixedCoordinateMap_comp_mkQuotient T S σT σS hσT hσS
    have h' := congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom h
    simpa [qP, j, TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp,
      toBialgHom_productTensorMapHom] using h'
  refine ⟨y, ?_⟩
  apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective P.obj IP A
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply,
    TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
  change TauCeti.AlgHom.mapDomain qP
      (TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (productFixedCoordinateMap T S σT σS hσT hσS)) y) =
    TauCeti.AlgHom.mapDomain qP (x ^ 3)
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp
    (ψ := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (productFixedCoordinateMap T S σT σS hσT hσS))
    (φ := qP)]
  rw [hΦcomp, map_pow]
  change TauCeti.AlgHom.mapDomain j y = xP ^ 3
  exact hcalc

variable [IsAlgClosed k]

theorem componentPointsHom_fixedCoordinate_tensorProduct_pow_three
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (hS : ConnectedSpace (PrimeSpectrum (fixedCoordinate S σS)))
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (productObj T S) (productAut T S σT σS))
      (CommAlgCat.of k k)) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom
      (fixedCoordinate (productObj T S) (productAut T S σT σS))
      (CommAlgCat.of k k) (x ^ 3) = 1 := by
  have hTgc : TauCeti.geometricallyConnectedCommHopfAlgProperty k T.obj :=
    TauCeti.torusCommHopfAlgProperty.geometricallyConnected k T hT
  have hSgc : TauCeti.geometricallyConnectedCommHopfAlgProperty k
      (fixedCoordinate S σS).obj :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k
      (fixedCoordinate S σS).obj).2 (by simpa using hS)
  have hQgc : TauCeti.geometricallyConnectedCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS)).obj := by
    simpa using TauCeti.geometricallyConnectedCommHopfAlgProperty.tensorProduct
      T.obj (fixedCoordinate S σS).obj hTgc hSgc
  have hQconn : ConnectedSpace (PrimeSpectrum
      (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS))) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hQgc
  obtain ⟨y, hy⟩ := exists_mapDomain_productFixedCoordinateMap_eq_pow_three
    T S σT σS hσT hσS x
  rw [← hy]
  exact componentPointsHom_map_eq_one
    (fixedCoordinate (productObj T S) (productAut T S σT σS))
    (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T (fixedCoordinate S σS))
    (productFixedCoordinateMap T S σT σS hσT hσS).hom hQconn y

end Norm

section TorusWrapper

variable [IsAlgClosed k]

variable (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)
variable (σT : T →ₐc[k] T) (σS : S →ₐc[k] S)

theorem fixedCoordinate_tensorProduct_componentPointsHom_pow_three
    (hσT : (σT.comp σT).comp σT = BialgHom.id k T)
    (hσS : (σS.comp σS).comp σS = BialgHom.id k S)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (hS : ConnectedSpace (PrimeSpectrum (fixedCoordinate S σS)))
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (productObj T S) (productAut T S σT σS))
      (CommAlgCat.of k k)) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom
      (fixedCoordinate (productObj T S) (productAut T S σT σS))
      (CommAlgCat.of k k) (x ^ 3) = 1 := by
  let : Coalgebra.IsCocomm k T := TauCeti.torusCommHopfAlgProperty.isCocomm k T hT
  exact componentPointsHom_fixedCoordinate_tensorProduct_pow_three
    T S σT σS hσT hσS hT hS x

end TorusWrapper

end CFSG.LieType.AlgebraicGroups.FixedProduct
