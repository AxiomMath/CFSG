module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import CFSG.LieType.AlgebraicGroups.UnipotentCentralExtension
public import CFSG.LieType.AlgebraicGroups.UnipotentFinitePoints
public import CFSG.LieType.AlgebraicGroups.ReducedIdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality

public noncomputable section

open WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

def NormalUnipotentFree (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) : Prop :=
  ∀ I : TauCeti.HopfIdeal k H, I.IsNormal →
    ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)) →
    IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) →
    (∀ g : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint g) →
    I = TauCeti.HopfIdeal.augmentation k H

omit [IsAlgClosed k] in
theorem mem_quotientPointsSubgroup_map_iff {B P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (ψ : B →ₐc[k] P) (I : TauCeti.HopfIdeal k B) (x : WithConv (P →ₐ[k] k)) :
    x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj (I.map ψ) (CommAlgCat.of k k) ↔
      TauCeti.AlgHom.mapDomain ψ x ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I (CommAlgCat.of k k) := by
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hx h hh
    exact hx (ψ h) (TauCeti.HopfIdeal.mem_map_of_mem ψ hh)
  · intro hx h hh
    have hle : Ideal.map (ψ : B →+* P) I.toIdeal ≤ RingHom.ker x.ofConv.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact hx a ha
    have hh' : h ∈ (I.map ψ).toIdeal := hh
    rw [TauCeti.HopfIdeal.map_toIdeal] at hh'
    exact hle hh'

theorem normalUnipotentFree_of_finite_central_kernel_of_unipotent_lift
    {B P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} [IsReduced P] (hP : NormalUnipotentFree P)
    (ψ : B →ₐc[k] P)
    (hfin : ((TauCeti.AlgHom.mapDomain (A := k) ψ).ker :
      Set (WithConv (P →ₐ[k] k))).Finite)
    (hcen : ∀ z : WithConv (P →ₐ[k] k), TauCeti.AlgHom.mapDomain ψ z = 1 →
      ∀ y : WithConv (P →ₐ[k] k), z * y = y * z)
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hlift : ∀ n : WithConv (B →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint n →
      ∃ x : WithConv (P →ₐ[k] k), TauCeti.AlgHom.mapDomain ψ x = n ^ m) :
    NormalUnipotentFree B := by
  classical
  intro I hI hIconn hIred hIunip
  let g := TauCeti.AlgHom.mapDomain (A := k) ψ
  let N := TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I (CommAlgCat.of k k)
  have hNunip : ∀ n ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint n := by
    rintro n ⟨x, rfl⟩
    exact (hIunip x).mapDomain _
  let J₀ := I.map ψ
  have hJ₀ : J₀.IsNormal := hI.map ψ
  let W := TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J₀ (CommAlgCat.of k k)
  have hW : ∀ x, x ∈ W ↔ g x ∈ N := fun x => mem_quotientPointsSubgroup_map_iff ψ I x
  obtain ⟨J, hJn, hJc, hJr, hJW, hJfi⟩ := exists_reduced_identityComponent_of_isReduced P J₀ hJ₀
  let Y := TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J (CommAlgCat.of k k)
  let q := TauCeti.CommHopfAlgCat.quotientPointsHom P.obj J (CommAlgCat.of k k)
  have hq : ∀ y, q y ∈ Y := fun y => ⟨y, rfl⟩
  have hqinj : Function.Injective q :=
    TauCeti.CommHopfAlgCat.quotientPointsHom_injective P.obj J (CommAlgCat.of k k)
  have hYunip : ∀ y : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient P J →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint y := by
    let _ : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient P J) := hJr
    refine forall_isUnipotentPoint_of_semisimplePart_mem
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient P J) hJc {z | g (q z) = 1} ?_ ?_ ?_
    · exact (hfin.preimage (hqinj.injOn)).subset fun z hz => hz
    · intro z hz y
      apply hqinj
      rw [map_mul, map_mul]
      exact hcen (q z) hz (q y)
    · intro y
      have hgy : g (q y) ∈ N := (hW (q y)).1 (hJW (hq y))
      have hu : TauCeti.HopfAlgebra.IsUnipotentPoint (g (q y)) := hNunip _ hgy
      change g (q (TauCeti.HopfAlgebra.Point.semisimplePart k _ k y)) = 1
      have hqss : q (TauCeti.HopfAlgebra.Point.semisimplePart k _ k y) =
          TauCeti.HopfAlgebra.Point.semisimplePart k P k (q y) :=
        (TauCeti.HopfAlgebra.Point.semisimplePart_mapDomain
          (TauCeti.CommHopfAlgCat.mkQuotient P.obj J).hom y).symm
      rw [hqss]
      change TauCeti.AlgHom.mapDomain ψ (TauCeti.HopfAlgebra.Point.semisimplePart k P k (q y)) = 1
      rw [← TauCeti.HopfAlgebra.Point.semisimplePart_mapDomain]
      exact (TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one k B k _).1 hu
  have hJaug := hP J hJn hJc hJr hYunip
  have hYbot : ∀ y ∈ Y, y = 1 := by
    intro y hy
    have hy' : y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj
        (TauCeti.HopfIdeal.augmentation k P) (CommAlgCat.of k k) := hJaug ▸ hy
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff _ _ y).1 hy'
  have hWfin : (W : Set (WithConv (P →ₐ[k] k))).Finite := by
    have hbot : Y.subgroupOf W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hYbot _ hw)
    have hfi := hJfi
    rw [hbot] at hfi
    have hcard : Nat.card W ≠ 0 := by
      rw [← Subgroup.index_bot]
      exact hfi.index_ne_zero
    have : Finite W := Nat.finite_of_card_ne_zero hcard
    exact Set.toFinite _
  have hNm : (fun n : WithConv (B →ₐ[k] k) => n ^ m) '' (N : Set (WithConv (B →ₐ[k] k))) ⊆
      g '' (W : Set (WithConv (P →ₐ[k] k))) := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨x, hx⟩ := hlift n (hNunip n hn)
    refine ⟨x, (hW x).2 ?_, hx⟩
    rw [hx]
    exact N.pow_mem hn m
  have hNfin := finite_of_finite_pow_of_forall_isUnipotentPoint B N hNunip m hm
    ((hWfin.image g).subset hNm)
  exact eq_augmentation_of_finite_quotientPoints B I hIconn hIred hNfin

section LevelShift

variable {k₀ : Type u} [Field k₀]

theorem normalUnipotentFree_baseChange_of_reductive {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k₀}
    (hH : TauCeti.reductiveCommHopfAlgProperty k₀ H) :
    NormalUnipotentFree (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) := by
  intro I hI hconn hred hunip
  have hconnK : TauCeti.geometricallyConnectedCommHopfAlgProperty
      (AlgebraicClosure k₀)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace
      (AlgebraicClosure k₀)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj).2 hconn
  have hsm : Algebra.Smooth (AlgebraicClosure k₀)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I) := by
    have hredSmooth : TauCeti.smoothCommHopfAlgProperty (AlgebraicClosure k₀)
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient
          (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj :=
      (TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
        (AlgebraicClosure k₀)
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient
          (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj).2 hred
    exact (TauCeti.smoothCommHopfAlgProperty_iff
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj).1 hredSmooth
  have hgeom : TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty
      (AlgebraicClosure k₀)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj :=
    (TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.iff_forall_isUnipotentPoint
      (A := (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj)
      (AlgebraicClosure k₀)).2 hunip
  have hU : TauCeti.smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k₀)
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I) := by
    rw [TauCeti.smoothUnipotentCommHopfAlgProperty_iff]
    refine ⟨hsm, ?_⟩
    intro g
    exact TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint
      (A := (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H) I).obj)
      hgeom g
  exact TauCeti.reductiveCommHopfAlgProperty.eq_augmentation hH I hI hconnK hU

theorem reductive_of_normalUnipotentFree_baseChange (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k₀)
    [Algebra.Smooth k₀ H] (hH : TauCeti.geometricallyConnectedCommHopfAlgProperty k₀ H.obj)
    (htriv : NormalUnipotentFree
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k₀) H)) :
    TauCeti.reductiveCommHopfAlgProperty k₀ H := by
  rw [TauCeti.reductiveCommHopfAlgProperty_iff]
  refine ⟨inferInstance, hH, ?_⟩
  intro I hI hconn hU
  let K := AlgebraicClosure k₀
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient
    (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := K) H) I
  have hconn' : ConnectedSpace (PrimeSpectrum Q) :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace K Q.obj).1 hconn
  have hred' : IsReduced Q := by
    let _ : Algebra.Smooth K Q := (TauCeti.smoothUnipotentCommHopfAlgProperty_iff K Q).1 hU |>.1
    exact TauCeti.isReduced_of_smooth K Q
  have hunip' : ∀ g : WithConv (Q.obj →ₐ[K] K), TauCeti.HopfAlgebra.IsUnipotentPoint g := by
    intro g
    have hU' : ∀ g : WithConv (Q.obj →ₐ[K] AlgebraicClosure K),
        TauCeti.HopfAlgebra.IsUnipotentPoint g :=
      (TauCeti.smoothUnipotentCommHopfAlgProperty_iff K Q).1 hU |>.2
    have hinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
      RingHom.injective _
    have hmap : TauCeti.HopfAlgebra.IsUnipotentPoint
        (TauCeti.AlgHom.mapValue (H := Q) (Algebra.ofId K (AlgebraicClosure K)) g) :=
      hU' (TauCeti.AlgHom.mapValue (H := Q) (Algebra.ofId K (AlgebraicClosure K)) g)
    exact (TauCeti.HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g
      (Algebra.ofId K (AlgebraicClosure K)) hinj).1 hmap
  exact htriv I hI hconn' hred' hunip' 

end LevelShift

noncomputable def algebraicClosureAlgEquiv : AlgebraicClosure k ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

noncomputable def valueChangeMulEquiv (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    WithConv (H →ₐ[k] AlgebraicClosure k) ≃* WithConv (H →ₐ[k] k) where
  toFun := TauCeti.AlgHom.mapValue (H := H) (algebraicClosureAlgEquiv (k := k)).toAlgHom
  invFun := TauCeti.AlgHom.mapValue (H := H) (algebraicClosureAlgEquiv (k := k)).symm.toAlgHom
  left_inv x := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    simp [TauCeti.AlgHom.mapValue_apply]
  right_inv y := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    simp [TauCeti.AlgHom.mapValue_apply]
  map_mul' := map_mul _

noncomputable def baseChangePointsMulEquivOfIsAlgClosed (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    WithConv (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H →ₐ[AlgebraicClosure k]
      AlgebraicClosure k) ≃* WithConv (H →ₐ[k] k) :=
  (TauCeti.AlgHom.baseChangePointsMulEquiv (k := k) (K := AlgebraicClosure k) (A := H)
    (R := AlgebraicClosure k)).symm.trans (valueChangeMulEquiv H)

theorem baseChangePointsMulEquivOfIsAlgClosed_apply_apply
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (x : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H →ₐ[AlgebraicClosure k]
      AlgebraicClosure k)) (h : H) :
    (baseChangePointsMulEquivOfIsAlgClosed H x).ofConv h =
      algebraicClosureAlgEquiv (k := k) (x.ofConv (1 ⊗ₜ[k] h)) := by
  rw [baseChangePointsMulEquivOfIsAlgClosed, MulEquiv.trans_apply]
  change (TauCeti.AlgHom.mapValue (H := H) (algebraicClosureAlgEquiv (k := k)).toAlgHom
    ((TauCeti.AlgHom.baseChangePointsMulEquiv (k := k) (K := AlgebraicClosure k) (A := H)
      (R := AlgebraicClosure k)).symm x)).ofConv h = _
  rw [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    TauCeti.AlgHom.baseChangePointsMulEquiv_symm_ofConv, AlgHom.liftEquiv_symm_apply]
  rfl

theorem baseChangePointsMulEquivOfIsAlgClosed_mapDomain
    {B P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} (ψ : B ⟶ P)
    (x : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) P →ₐ[AlgebraicClosure k]
      AlgebraicClosure k)) :
    baseChangePointsMulEquivOfIsAlgClosed B
        (TauCeti.AlgHom.mapDomain
          (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) ψ)) x) =
      TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ)
        (baseChangePointsMulEquivOfIsAlgClosed P x) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [baseChangePointsMulEquivOfIsAlgClosed_apply_apply, TauCeti.AlgHom.mapDomain_apply_apply,
    TauCeti.AlgHom.mapDomain_apply_apply, baseChangePointsMulEquivOfIsAlgClosed_apply_apply,
    TauCeti.FiniteTypeCommHopfAlgCat.baseChangeMap_apply_tmul]

theorem isUnipotentPoint_baseChangePointsMulEquivOfIsAlgClosed_iff
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (x : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H →ₐ[AlgebraicClosure k]
      AlgebraicClosure k)) :
    TauCeti.HopfAlgebra.IsUnipotentPoint (baseChangePointsMulEquivOfIsAlgClosed H x) ↔
      TauCeti.HopfAlgebra.IsUnipotentPoint x := by
  classical
  let K := AlgebraicClosure k
  obtain ⟨M, d, b, hb⟩ :=
    TauCeti.Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k M := Module.Free.of_basis b
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hM : TauCeti.Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
  let _ := TauCeti.Comodule.baseChange (R := k) (H := H) (M := M) K
  let bK := b.baseChange K
  let _ : Module.Finite K (K ⊗[k] M) := Module.Finite.of_basis bK
  have hMK := TauCeti.Comodule.IsFaithful.baseChange (K := K) hM
  let y : H →ₐ[k] K := (AlgHom.liftEquiv k K H K).symm x.ofConv
  have hy : ∀ h : H, y h = x.ofConv (1 ⊗ₜ[k] h) := fun h => AlgHom.liftEquiv_symm_apply _ h
  let P : Polynomial K := ((TauCeti.Comodule.coefficientMatrix (C := H) b).charpoly).map
    y.toRingHom
  have hK : ((TauCeti.Comodule.coefficientMatrix (C := K ⊗[k] H) bK).charpoly).map
      x.ofConv.toRingHom = P := by
    have hmatrix : (TauCeti.Comodule.coefficientMatrix (C := H) b).map
          ((TensorProduct.mk k K H) 1) =
        (TauCeti.Comodule.coefficientMatrix (C := H) b).map
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H).toRingHom := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, TensorProduct.mk_apply]
      exact (Algebra.TensorProduct.includeRight_apply _).symm
    rw [TauCeti.Comodule.coefficientMatrix_baseChange, hmatrix, Matrix.charpoly_map,
      Polynomial.map_map]
    congr 1
  have hk : ((TauCeti.Comodule.coefficientMatrix (C := H) b).charpoly).map
      (baseChangePointsMulEquivOfIsAlgClosed H x).ofConv.toRingHom =
      P.map (algebraicClosureAlgEquiv (k := k)).toAlgHom.toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    ext h
    exact (baseChangePointsMulEquivOfIsAlgClosed_apply_apply H x h).trans
      (congrArg _ (hy h).symm)
  rw [isUnipotentPoint_iff_charpoly_map hM b, isUnipotentPoint_iff_charpoly_map hMK bK, hK, hk]
  constructor
  · intro h
    have h' := congrArg (Polynomial.map (algebraicClosureAlgEquiv (k := k)).symm.toAlgHom.toRingHom) h
    rw [Polynomial.map_map] at h'
    have hid : (algebraicClosureAlgEquiv (k := k)).symm.toAlgHom.toRingHom.comp
        (algebraicClosureAlgEquiv (k := k)).toAlgHom.toRingHom = RingHom.id K := by
      ext z
      change (algebraicClosureAlgEquiv (k := k)).symm (algebraicClosureAlgEquiv (k := k) z) = z
      exact AlgEquiv.symm_apply_apply _ z
    rw [hid, Polynomial.map_id] at h'
    rw [h']
    simp [Polynomial.map_pow, Polynomial.map_sub]
  · intro h
    rw [h]
    simp [Polynomial.map_pow, Polynomial.map_sub]

theorem reductive_of_finite_central_kernel_of_unipotent_lift
    (B P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hP : TauCeti.reductiveCommHopfAlgProperty k P)
    [Algebra.Smooth k B] (hB : ConnectedSpace (PrimeSpectrum B))
    (ψ : B ⟶ P)
    (hfin : ((TauCeti.AlgHom.mapDomain (A := k) (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ)).ker :
      Set (WithConv (P →ₐ[k] k))).Finite)
    (hcen : ∀ z : WithConv (P →ₐ[k] k),
      TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) z = 1 →
      ∀ y : WithConv (P →ₐ[k] k), z * y = y * z)
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hlift : ∀ n : WithConv (B →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint n →
      ∃ x : WithConv (P →ₐ[k] k),
        TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) x = n ^ m) :
    TauCeti.reductiveCommHopfAlgProperty k B := by
  classical
  let K := AlgebraicClosure k
  let eB := baseChangePointsMulEquivOfIsAlgClosed B
  let eP := baseChangePointsMulEquivOfIsAlgClosed P
  let ψK := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) ψ)
  have hcomm : ∀ x, eB (TauCeti.AlgHom.mapDomain ψK x) =
      TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) (eP x) :=
    baseChangePointsMulEquivOfIsAlgClosed_mapDomain ψ
  have hBconn : TauCeti.geometricallyConnectedCommHopfAlgProperty k B.obj :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2 hB
  refine reductive_of_normalUnipotentFree_baseChange B hBconn ?_
  have hmK : (m : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k K)]
    exact (map_ne_zero_iff _ (algebraMap k K).injective).2 hm
  have : Algebra.Smooth k P := hP.smooth
  have : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := K) P) :=
    TauCeti.isReduced_of_smooth K _
  refine normalUnipotentFree_of_finite_central_kernel_of_unipotent_lift
    (normalUnipotentFree_baseChange_of_reductive hP) ψK ?_ ?_ m hmK ?_
  · refine (hfin.preimage eP.injective.injOn).subset ?_
    intro x hx
    change TauCeti.AlgHom.mapDomain ψK x = 1 at hx
    change TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) (eP x) = 1
    rw [← hcomm, hx, map_one]
  · intro z hz y
    apply eP.injective
    rw [map_mul, map_mul]
    refine hcen (eP z) ?_ (eP y)
    rw [← hcomm, hz, map_one]
  · intro n hn
    obtain ⟨x, hx⟩ := hlift (eB n)
      ((isUnipotentPoint_baseChangePointsMulEquivOfIsAlgClosed_iff B n).2 hn)
    refine ⟨eP.symm x, eB.injective ?_⟩
    rw [hcomm, MulEquiv.apply_symm_apply, hx, map_pow]

end CFSG.LieType.AlgebraicGroups.ReductiveDescent
