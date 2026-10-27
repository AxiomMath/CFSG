module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic

public noncomputable section

open WithConv
open TauCeti
open Module
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section CharpolyTest

variable {Y : Type u} [CommRing Y] [_root_.HopfAlgebra k Y]

omit [IsAlgClosed k] in
theorem isUnipotent_pointsAction_iff_charpoly_map
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k Y V] [Module.Finite k V]
    {d : ℕ} (b : Basis (Fin d) k V) (g : WithConv (Y →ₐ[k] k)) :
    LinearMap.GeneralLinearGroup.IsUnipotent
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction V g)) ↔
      ((Comodule.coefficientMatrix (C := Y) b).charpoly).map g.ofConv.toRingHom =
        (Polynomial.X - 1) ^ d := by
  classical
  let _ : Module.Free k V := Module.Free.of_divisionRing k V
  let C : Matrix (Fin d) (Fin d) Y := Comodule.coefficientMatrix (C := Y) b
  have hcoe : ((LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction V g)) :
      Module.End _ _) = Comodule.endOfPoint V g.ofConv :=
    Comodule.pointsAction_toLinearMap V g
  have hcomp : (Comodule.endOfPoint V g.ofConv).charpoly =
      C.charpoly.map g.ofConv.toRingHom := by
    rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint V g.ofConv) (b.baseChange k),
      Comodule.toMatrix_endOfPoint]
    exact Matrix.charpoly_map (Comodule.coefficientMatrix b) g.ofConv.toRingHom
  have hfr : Module.finrank k (k ⊗[k] V) = d := by
    rw [Module.finrank_baseChange, Module.finrank_eq_card_basis b]
    simp
  constructor
  · intro h
    rw [LinearMap.GeneralLinearGroup.isUnipotent_iff_charpoly] at h
    rwa [hcoe, hcomp, hfr] at h
  · intro h
    refine LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction V g)) (n := d) ?_
    rw [hcoe, hcomp]
    exact h

theorem isUnipotentPoint_iff_charpoly_map
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k Y V] [Module.Finite k V]
    (hfaith : Comodule.IsFaithful (k := k) (H := Y) (V := V))
    {d : ℕ} (b : Basis (Fin d) k V) (g : WithConv (Y →ₐ[k] k)) :
    TauCeti.HopfAlgebra.IsUnipotentPoint g ↔
      ((Comodule.coefficientMatrix (C := Y) b).charpoly).map g.ofConv.toRingHom =
        (Polynomial.X - 1) ^ d := by
  classical
  have hdetect := TauCeti.HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (k := k) (H := Y) (K := k) (M := TauCeti.FGComoduleCat.of (R := k) (C := Y) V) hfaith g
  exact hdetect.trans (isUnipotent_pointsAction_iff_charpoly_map b g)

noncomputable def translatedCharpoly {d : ℕ} (C : Matrix (Fin d) (Fin d) Y)
    (z : WithConv (Y →ₐ[k] k)) : Polynomial Y :=
  C.charpoly.map (TauCeti.HopfAlgebra.rightTranslationAlgEquiv z⁻¹).toAlgHom.toRingHom -
    ((Polynomial.X - (1 : Polynomial k)) ^ d).map (algebraMap k Y)

noncomputable def translatedCharpolyIdeal {d : ℕ} (C : Matrix (Fin d) (Fin d) Y)
    (z : WithConv (Y →ₐ[k] k)) : Ideal Y :=
  Ideal.span (Set.range (translatedCharpoly C z).coeff)

omit [IsAlgClosed k] in
theorem translatedCharpolyIdeal_le_ker_iff {d : ℕ} (C : Matrix (Fin d) (Fin d) Y)
    (g z : WithConv (Y →ₐ[k] k)) :
    translatedCharpolyIdeal C z ≤ RingHom.ker g.ofConv.toRingHom ↔
      C.charpoly.map (g * z⁻¹).ofConv.toRingHom = (Polynomial.X - 1) ^ d := by
  have hspan : translatedCharpolyIdeal C z ≤ RingHom.ker g.ofConv.toRingHom ↔
      (translatedCharpoly C z).map g.ofConv.toRingHom = 0 := by
    rw [translatedCharpolyIdeal, Ideal.span_le]
    constructor
    · intro h
      rw [Polynomial.ext_iff]
      intro n
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      simpa using h (Set.mem_range_self n)
    · intro h n hn
      obtain ⟨m, rfl⟩ := Set.mem_range.mp hn
      have hzero : g.ofConv.toRingHom ((translatedCharpoly C z).coeff m) = 0 := by
        rw [← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      simpa using hzero
  have hτ : g.ofConv.toRingHom.comp
        (TauCeti.HopfAlgebra.rightTranslationAlgEquiv z⁻¹).toAlgHom.toRingHom =
      (g * z⁻¹).ofConv.toRingHom := by
    have hcomp : g.ofConv.comp (TauCeti.HopfAlgebra.rightTranslationAlgEquiv z⁻¹).toAlgHom =
        (g * z⁻¹).ofConv := by
      rw [← TauCeti.HopfAlgebra.toConv_comp_rightTranslationAlgHom (f := g) (g := z⁻¹),
        WithConv.ofConv_toConv, TauCeti.HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
    rw [← hcomp]
    rfl
  have hQ : (((Polynomial.X - (1 : Polynomial k)) ^ d).map (algebraMap k Y)).map
        g.ofConv.toRingHom = (Polynomial.X - 1) ^ d := by
    rw [Polynomial.map_map]
    have hcomp : g.ofConv.toRingHom.comp (algebraMap k Y) = RingHom.id k := by
      ext x
      change g.ofConv (algebraMap k Y x) = x
      rw [AlgHom.commutes]
      simp
    rw [hcomp, Polynomial.map_id]
  have hmain : (translatedCharpoly C z).map g.ofConv.toRingHom =
      C.charpoly.map (g * z⁻¹).ofConv.toRingHom - (Polynomial.X - 1) ^ d := by
    rw [translatedCharpoly, Polynomial.map_sub, Polynomial.map_map, hτ, hQ]
  rw [hspan, hmain, sub_eq_zero]

theorem semisimplePart_eq_iff_isUnipotentPoint_mul_inv
    (z : WithConv (Y →ₐ[k] k))
    (hzsem : TauCeti.HopfAlgebra.IsSemisimplePoint z)
    (hzc : ∀ y : WithConv (Y →ₐ[k] k), z * y = y * z)
    (y : WithConv (Y →ₐ[k] k)) :
    TauCeti.HopfAlgebra.Point.semisimplePart k Y k y = z ↔
      TauCeti.HopfAlgebra.IsUnipotentPoint (y * z⁻¹) := by
  constructor
  · intro h
    have hcentral : z * TauCeti.HopfAlgebra.Point.unipotentPart k Y k y =
        TauCeti.HopfAlgebra.Point.unipotentPart k Y k y * z := hzc _
    have hstep : y * z⁻¹ = TauCeti.HopfAlgebra.Point.unipotentPart k Y k y := by
      calc y * z⁻¹ = (TauCeti.HopfAlgebra.Point.semisimplePart k Y k y *
            TauCeti.HopfAlgebra.Point.unipotentPart k Y k y) * z⁻¹ := by
            rw [TauCeti.HopfAlgebra.Point.semisimplePart_mul_unipotentPart]
        _ = (z * TauCeti.HopfAlgebra.Point.unipotentPart k Y k y) * z⁻¹ := by rw [h]
        _ = (TauCeti.HopfAlgebra.Point.unipotentPart k Y k y * z) * z⁻¹ := by rw [hcentral]
        _ = TauCeti.HopfAlgebra.Point.unipotentPart k Y k y * (z * z⁻¹) := by rw [mul_assoc]
        _ = TauCeti.HopfAlgebra.Point.unipotentPart k Y k y := by rw [mul_inv_cancel, mul_one]
    rw [hstep]
    have hu := (TauCeti.HopfAlgebra.Point.jordanDecomposition_spec k Y k y).2.1
    rwa [TauCeti.HopfAlgebra.Point.jordanDecomposition_snd] at hu
  · intro hu
    have hcomm : Commute z (y * z⁻¹) := hzc (y * z⁻¹)
    have hmul : z * (y * z⁻¹) = y := by
      calc z * (y * z⁻¹) = (z * y) * z⁻¹ := by rw [mul_assoc]
        _ = (y * z) * z⁻¹ := by rw [hzc y]
        _ = y * (z * z⁻¹) := by rw [mul_assoc]
        _ = y := by rw [mul_inv_cancel, mul_one]
    exact (TauCeti.HopfAlgebra.Point.isSemisimple_isUnipotent_unique k Y k y z (y * z⁻¹)
      hcomm hmul (fun M => (TauCeti.HopfAlgebra.isSemisimplePoint_def z).mp hzsem M) hu).1.symm

theorem isSemisimplePoint_of_eq_semisimplePart {z : WithConv (Y →ₐ[k] k)}
    (hz : ∃ y : WithConv (Y →ₐ[k] k), TauCeti.HopfAlgebra.Point.semisimplePart k Y k y = z) :
    TauCeti.HopfAlgebra.IsSemisimplePoint z := by
  obtain ⟨y, rfl⟩ := hz
  rw [TauCeti.HopfAlgebra.isSemisimplePoint_def]
  intro M
  exact TauCeti.HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart
    (k := k) (H := Y) (K := k) (g := y) (M := M)

theorem translatedCharpolyIdeal_le_ker_iff_semisimplePart
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k Y V] [Module.Finite k V]
    (hfaith : Comodule.IsFaithful (k := k) (H := Y) (V := V))
    {d : ℕ} (b : Basis (Fin d) k V) (z : WithConv (Y →ₐ[k] k))
    (hzsem : TauCeti.HopfAlgebra.IsSemisimplePoint z)
    (hzc : ∀ y : WithConv (Y →ₐ[k] k), z * y = y * z)
    (g : WithConv (Y →ₐ[k] k)) :
    translatedCharpolyIdeal (Comodule.coefficientMatrix (C := Y) b) z ≤
        RingHom.ker g.ofConv.toRingHom ↔
      TauCeti.HopfAlgebra.Point.semisimplePart k Y k g = z := by
  rw [translatedCharpolyIdeal_le_ker_iff]
  exact (isUnipotentPoint_iff_charpoly_map hfaith b (g * z⁻¹)).symm.trans
    (semisimplePart_eq_iff_isUnipotentPoint_mul_inv z hzsem hzc g).symm

end CharpolyTest

theorem exists_algHom_le_ker_of_ne_top {Y : Type u} [CommRing Y] [Algebra k Y]
    [Algebra.FiniteType k Y] (I : Ideal Y) (hI : I ≠ ⊤) :
    ∃ y : Y →ₐ[k] k, I ≤ RingHom.ker y.toRingHom := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have : m.IsMaximal := hm
  let _ : Field (Y ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (Y ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (Y ⧸ m)
  let iota : Y ⧸ m →ₐ[k] k := IsAlgClosed.lift
  refine ⟨iota.comp (Ideal.Quotient.mkₐ k m), fun x hx => ?_⟩
  rw [RingHom.mem_ker]
  change iota ((Ideal.Quotient.mkₐ k m) x) = 0
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (hIm hx), map_zero]

theorem forall_isUnipotentPoint_of_semisimplePart_mem
    (Y : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hY : ConnectedSpace (PrimeSpectrum Y))
    [IsReduced Y] (Z : Set (WithConv (Y →ₐ[k] k))) (hZ : Z.Finite)
    (hZc : ∀ z ∈ Z, ∀ y : WithConv (Y →ₐ[k] k), z * y = y * z)
    (hs : ∀ y : WithConv (Y →ₐ[k] k),
      TauCeti.HopfAlgebra.Point.semisimplePart k Y k y ∈ Z) :
    ∀ y : WithConv (Y →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint y := by
  classical
  obtain ⟨M, d, b, hb⟩ :=
    TauCeti.Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := Y)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k M := Module.Free.of_basis b
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hfaith : Comodule.IsFaithful (k := k) (H := Y) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
  let C : Matrix (Fin d) (Fin d) Y := Comodule.coefficientMatrix (C := Y) b
  let Z' : Set (WithConv (Y →ₐ[k] k)) :=
    Set.range (TauCeti.HopfAlgebra.Point.semisimplePart k Y k)
  have hZ'sub : Z' ⊆ Z := by
    rintro z ⟨y, rfl⟩
    exact hs y
  have hZ'fin : Z'.Finite := hZ.subset hZ'sub
  have hZ'fintype : Fintype Z' := hZ'fin.fintype
  let I : Z' → Ideal Y := fun z => translatedCharpolyIdeal C z.1
  have hI : ∀ (z : Z') (y : WithConv (Y →ₐ[k] k)),
      I z ≤ RingHom.ker y.ofConv.toRingHom ↔
        TauCeti.HopfAlgebra.Point.semisimplePart k Y k y = z.1 := by
    intro z y
    exact translatedCharpolyIdeal_le_ker_iff_semisimplePart hfaith b z.1
      (isSemisimplePoint_of_eq_semisimplePart z.2)
      (fun y => hZc z.1 (hZ'sub z.2) y) y
  have hInter : (⨅ z : Z', I z) = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    rw [Ideal.mem_bot]
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (A := Y) (K := k)
    intro q
    have hmem : f ∈ I ⟨TauCeti.HopfAlgebra.Point.semisimplePart k Y k (WithConv.toConv q),
        WithConv.toConv q, rfl⟩ := Ideal.mem_iInf.mp hf _
    have hle := (hI ⟨TauCeti.HopfAlgebra.Point.semisimplePart k Y k (WithConv.toConv q),
        WithConv.toConv q, rfl⟩ (WithConv.toConv q)).mpr rfl
    have hzero : (WithConv.toConv q).ofConv f = 0 := by
      simpa using (hle hmem)
    simpa using hzero
  have hcover : (⋃ z : Z', PrimeSpectrum.zeroLocus (I z : Set Y)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    by_contra hp
    simp only [Set.mem_iUnion, not_exists] at hp
    have hmiss : ∀ z : Z', ∃ f : Y, f ∈ I z ∧ f ∉ p.asIdeal := by
      intro z
      have h' : ¬ (I z ≤ p.asIdeal) := fun hle =>
        hp z ((PrimeSpectrum.mem_zeroLocus p (I z : Set Y)).mpr hle)
      exact Set.not_subset.mp h'
    choose f hfI hfp using hmiss
    have hprod_mem : (∏ z : Z', f z) ∈ ⨅ z : Z', I z := by
      rw [Ideal.mem_iInf]
      intro z0
      exact Ideal.prod_mem (I z0) (Finset.mem_univ z0) (hfI z0)
    rw [hInter] at hprod_mem
    have hprod_zero : (∏ z : Z', f z) = 0 := hprod_mem
    have hprod_ne : (∏ z : Z', f z) ∉ p.asIdeal := by
      intro h
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hfp i hi
    exact hprod_ne (by rw [hprod_zero]; exact p.asIdeal.zero_mem)
  have hclosed : ∀ z : Z', IsClosed (PrimeSpectrum.zeroLocus (I z : Set Y)) :=
    fun z => PrimeSpectrum.isClosed_zeroLocus _
  have hnonempty : ∀ z : Z', (PrimeSpectrum.zeroLocus (I z : Set Y)).Nonempty := by
    intro z
    obtain ⟨y, hy⟩ := z.2
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have htop : I z = ⊤ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hempty
    have hle : I z ≤ RingHom.ker y.ofConv.toRingHom := (hI z y).mpr hy
    rw [htop] at hle
    have h1 : (1 : Y) ∈ RingHom.ker y.ofConv.toRingHom := hle (by simp)
    simp at h1
  have hdisj : Pairwise (Function.onFun Disjoint (fun z : Z' =>
      PrimeSpectrum.zeroLocus (I z : Set Y))) := by
    intro z w hzw
    have hsup : I z ⊔ I w = ⊤ := by
      by_contra h
      obtain ⟨y, hy⟩ := exists_algHom_le_ker_of_ne_top (k := k) (I z ⊔ I w) h
      have hzy : TauCeti.HopfAlgebra.Point.semisimplePart k Y k (WithConv.toConv y) = z.1 :=
        (hI z (WithConv.toConv y)).mp (by simpa using le_trans le_sup_left hy)
      have hwy : TauCeti.HopfAlgebra.Point.semisimplePart k Y k (WithConv.toConv y) = w.1 :=
        (hI w (WithConv.toConv y)).mp (by simpa using le_trans le_sup_right hy)
      exact hzw (Subtype.ext (hzy.symm.trans hwy))
    change Disjoint (PrimeSpectrum.zeroLocus (I z : Set Y))
      (PrimeSpectrum.zeroLocus (I w : Set Y))
    rw [Set.disjoint_iff_inter_eq_empty, ← PrimeSpectrum.zeroLocus_sup, hsup,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have hsub : Subsingleton Z' :=
    subsingleton_of_disjoint_isClosed_iUnion_eq_univ hnonempty hdisj hclosed hcover
  intro y
  have hone : TauCeti.HopfAlgebra.Point.semisimplePart k Y k y = 1 := by
    have := hsub
    have h := Subsingleton.elim
      (⟨TauCeti.HopfAlgebra.Point.semisimplePart k Y k y, y, rfl⟩ : Z')
      (⟨TauCeti.HopfAlgebra.Point.semisimplePart k Y k (1 : WithConv (Y →ₐ[k] k)),
        (1 : WithConv (Y →ₐ[k] k)), rfl⟩ : Z')
    have hval := congrArg Subtype.val h
    simpa [TauCeti.HopfAlgebra.Point.semisimplePart_one] using hval
  rw [TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one]
  exact hone

end CFSG.LieType.AlgebraicGroups.ReductiveDescent
