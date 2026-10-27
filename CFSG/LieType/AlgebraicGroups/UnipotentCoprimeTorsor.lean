module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Nilpotent
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LieType.AlgebraicGroups.UnipotentFinitePoints
public import CFSG.LinearAlgebra.UnipotentPolynomialPowers
public import CFSG.GroupTheory.CoprimeNilpotentHomogeneous
public import TauCeti.Algebra.AlgebraicGroup.Torus.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Existence
public import CFSG.LieType.AlgebraicGroups.ConnectedCenterAutomorphism
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory WithConv
open scoped TensorProduct

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem isNilpotent_points_of_forall_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    Group.IsNilpotent (WithConv (H →ₐ[k] k)) := by
  obtain ⟨M, n, b, hb, hclosed⟩ :=
    TauCeti.Comodule.upperUnitriangularCoordinateGroupSchemeHom.exists_isClosedImmersion_of_forall_isUnipotentPoint
      (k := k) (H := H) hH
  let f := TauCeti.Comodule.upperUnitriangularCoordinateBialgHom (H := H) b hb
  have hf : Function.Surjective f :=
    (TauCeti.Comodule.isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff b hb).mp
      hclosed
  let ρ := TauCeti.AlgHom.mapDomain (A := k) f
  have hinj : Function.Injective ρ := by
    intro g h heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hf x
    have h := congrArg (fun g : WithConv
      (TauCeti.UpperUnitriangular.coordinateHopfAlgebra k (Fin n) →ₐ[k] k) => g.ofConv y) heq
    simpa only [ρ, TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  let := TauCeti.UpperUnitriangular.isNilpotent_points k (Fin n) k
  apply Subgroup.isNilpotent_of_ker_le_center ρ
  intro g hg
  have hg1 : g = 1 := hinj ((MonoidHom.mem_ker.mp hg).trans (map_one ρ).symm)
  rw [hg1]
  exact Subgroup.one_mem _

omit [IsAlgClosed k] in
theorem exists_uniform_pow_eq_one_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {p : ℕ} [CharP k p] (hp : p.Prime) :
    ∃ e : ℕ, ∀ g ∈ N, g ^ (p ^ e) = 1 := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k H).out
  obtain ⟨D, hD, hsD⟩ := TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) (s : Set H) s.finite_toSet
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  have hgen : Algebra.adjoin k (D : Set H) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_mono hsD
  let e := Nat.log p (Module.finrank k (k ⊗[k] D.toRegularSubcomodule)) + 1
  have hbound : Module.finrank k (k ⊗[k] D.toRegularSubcomodule) ≤ p ^ e :=
    le_of_lt (Nat.lt_pow_succ_log_self hp.one_lt _)
  refine ⟨e, fun g hg => ?_⟩
  have hnil : IsNilpotent
      (TauCeti.Comodule.endOfPoint D.toRegularSubcomodule g.ofConv - 1) :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
      (hN g hg) (TauCeti.FGComoduleCat.of (R := k) (C := H) D.toRegularSubcomodule)
  have hpow := ReductiveDescent.endOfPoint_pow_prime_pow_eq_one hp e hbound g hnil
  apply basePointsRepresentation_injective_of_generating_subcoalgebra D hgen
  apply LinearMap.ext
  intro x
  apply ReductiveDescent.mk_one_tmul_injective (K := k)
  rw [ReductiveDescent.mk_one_tmul_basePointsRepresentation,
    ReductiveDescent.mk_one_tmul_basePointsRepresentation,
    ReductiveDescent.endOfPoint_pow, hpow, TauCeti.Comodule.endOfPoint_convOne]
  rfl

omit [IsAlgClosed k] in
theorem isPGroup_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {p : ℕ} [CharP k p] (hp : p.Prime) : IsPGroup p N := by
  obtain ⟨e, he⟩ := exists_uniform_pow_eq_one_of_unipotent H N hN hp
  exact fun g => ⟨e, Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using he g g.property)⟩

omit [IsAlgClosed k] in
theorem cube_bijective_of_unipotent_of_charP
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {p : ℕ} [CharP k p] (hp : p.Prime) (h3 : (3 : k) ≠ 0) :
    Function.Bijective (fun g : N => g ^ 3) := by
  let : Fact p.Prime := ⟨hp⟩
  have hcop : ¬p ∣ 3 := fun h => h3 ((CharP.cast_eq_zero_iff k p 3).mpr h)
  exact (IsPGroup.powEquiv' (isPGroup_of_unipotent H N hN hp) hcop).bijective

section CharZero

variable [CharZero k]

omit [IsAlgClosed k] [CharZero k] in
theorem isNilpotent_toMatrix_basePointsRepresentation_sub_one
    {H M : Type u} [CommRing H] [HopfAlgebra k H]
    [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M] [Module.Finite k M]
    {n : ℕ} (b : Module.Basis (Fin n) k M) (g : WithConv (H →ₐ[k] k))
    (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    IsNilpotent
      (LinearMap.toMatrixAlgEquiv b
        (TauCeti.Comodule.basePointsRepresentation (H := H) M g) - 1) := by
  have hn : IsNilpotent (TauCeti.Comodule.endOfPoint M g.ofConv - 1) :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
      hg (TauCeti.FGComoduleCat.of (R := k) (C := H) M)
  have heq : (TensorProduct.lid k M).conjRingEquiv
      (TauCeti.Comodule.endOfPoint M g.ofConv) =
    TauCeti.Comodule.basePointsRepresentation (H := H) M g := by
    apply LinearMap.ext
    intro m
    rw [LinearEquiv.conjRingEquiv_apply_apply,
      TauCeti.Comodule.basePointsRepresentation_apply]
    congr 1
  let e : Module.End k (k ⊗[k] M) ≃+* Module.End k M := (TensorProduct.lid k M).conjRingEquiv
  have heq' : e (TauCeti.Comodule.endOfPoint M g.ofConv) =
      TauCeti.Comodule.basePointsRepresentation (H := H) M g := heq
  have hbase := hn.map e
  have hbase' : IsNilpotent (TauCeti.Comodule.basePointsRepresentation (H := H) M g - 1) := by
    have hs := e.map_sub (TauCeti.Comodule.endOfPoint M g.ofConv) 1
    have h1 : e (1 : Module.End k (k ⊗[k] M)) = 1 := e.map_one
    rw [heq', h1] at hs
    exact hs ▸ hbase
  have hmat := hbase'.map (LinearMap.toMatrixAlgEquiv b)
  simpa only [map_sub, map_one] using hmat

omit [IsAlgClosed k] in
theorem exists_unipotentPowerCurve_of_matrix_image
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (f : TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H)
    (hf : Function.Surjective f) (g : WithConv (H →ₐ[k] k)) {d : ℕ}
    (hU : ((TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain f g) : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0) :
    ∃ b : H →ₐ[k] Polynomial k,
      b.comp f.toAlgHom = CFSG.LinearAlgebra.unipotentPowerCoordinate
        (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)) hU := by
  let U := TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)
  let c := CFSG.LinearAlgebra.unipotentPowerCoordinate U hU
  have hkill : ∀ a : TauCeti.GeneralLinear.coordinateHopfAlgebra k n,
      f a = 0 → c a = 0 := by
    intro a ha
    apply CFSG.LinearAlgebra.polynomial_eq_of_eval_natCast
    intro r
    have hc := CFSG.LinearAlgebra.unipotentPowerCoordinate_eval_natCast U hU r
    have hUpt : TauCeti.GeneralLinear.generalLinearToPoint (R := k) n U =
        TauCeti.AlgHom.mapDomain f g := by
      simpa only [TauCeti.GeneralLinear.pointsMulEquiv_symm_apply, U] using
        (TauCeti.GeneralLinear.pointsMulEquiv (R := k) (A := k) n).symm_apply_apply
          (TauCeti.AlgHom.mapDomain f g)
    rw [hUpt, ← map_pow] at hc
    have heval := congrArg (fun p : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k) => p.ofConv a) hc
    simpa [c, TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_apply, ha] using heval
  let q : (TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⧸
      RingHom.ker f.toAlgHom.toRingHom) →ₐ[k] Polynomial k :=
    Ideal.Quotient.liftₐ _ c (fun a ha => hkill a ha)
  have hfA : Function.Surjective f.toAlgHom := by
    intro x
    obtain ⟨a, ha⟩ := hf x
    exact ⟨a, ha⟩
  let e : (TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⧸
      RingHom.ker f.toAlgHom.toRingHom) ≃ₐ[k] H :=
    Ideal.quotientKerAlgEquivOfSurjective hfA
  let b : H →ₐ[k] Polynomial k := q.comp e.symm.toAlgHom
  refine ⟨b, ?_⟩
  apply AlgHom.ext
  intro a
  change q ((Ideal.quotientKerAlgEquivOfSurjective (f := f.toAlgHom) hfA).symm
    (f.toAlgHom a)) = c a
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

omit [IsAlgClosed k] in
theorem exists_unipotentPowerCurve
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (g : WithConv (H →ₐ[k] k))
    (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    ∃ b : H →ₐ[k] Polynomial k, ∀ r : ℕ,
      toConv ((Polynomial.aeval (r : k)).comp b) = g ^ r := by
  obtain ⟨D, hD, _, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H
    (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  let f := TauCeti.Comodule.coordinateBialgHom (H := H) b
  have hf := coordinateBialgHom_surjective_of_generating_subcoalgebra D hgen b
  have hnil := isNilpotent_toMatrix_basePointsRepresentation_sub_one b g hg
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g] at hnil
  obtain ⟨d, hd⟩ := hnil
  obtain ⟨c, hc⟩ := exists_unipotentPowerCurve_of_matrix_image H f hf g hd
  refine ⟨c, fun r => ?_⟩
  have hinj : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) f) := by
    intro x y heq
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := hf a
    have h := congrArg (fun x : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra k (Module.finrank k D.toRegularSubcomodule) →ₐ[k] k)
      => x.ofConv a) heq
    simpa only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  apply hinj
  rw [map_pow]
  have hcurve := CFSG.LinearAlgebra.unipotentPowerCoordinate_eval_natCast
    (TauCeti.GeneralLinear.pointsMulEquiv _ (TauCeti.AlgHom.mapDomain f g)) hd r
  have hU : TauCeti.GeneralLinear.generalLinearToPoint (R := k) _
      (TauCeti.GeneralLinear.pointsMulEquiv _ (TauCeti.AlgHom.mapDomain f g)) =
    TauCeti.AlgHom.mapDomain f g := by
    simpa only [TauCeti.GeneralLinear.pointsMulEquiv_symm_apply] using
      (TauCeti.GeneralLinear.pointsMulEquiv (R := k) (A := k)
        (Module.finrank k D.toRegularSubcomodule)).symm_apply_apply (TauCeti.AlgHom.mapDomain f g)
  rw [hU] at hcurve
  simpa only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc, hc] using hcurve

theorem le_conjugate_of_curve_natCast
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)]
    (b : H →ₐ[k] Polynomial k)
    (hnat : ∀ r : ℕ, I ≤ I.conjugate (toConv ((Polynomial.aeval (r : k)).comp b)))
    (t : k) :
    I ≤ I.conjugate (toConv ((Polynomial.aeval t).comp b)) := by
  intro a ha
  rw [TauCeti.HopfIdeal.mem_conjugate]
  apply TauCeti.HopfIdeal.mem_toIdeal.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro x
  let y : WithConv (H →ₐ[k] k) :=
    TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) (toConv x)
  have hy : y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
    TauCeti.CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _
  let cy : H →ₐ[k] Polynomial k := (Algebra.ofId k (Polynomial k)).comp y.ofConv
  let P : Polynomial k :=
    ((Algebra.TensorProduct.productMap b cy).comp
      (TauCeti.HopfAlgebra.conjugationAlgHom (R := k) (H := H))) a
  have hvalue (s : k) : P.eval s = y.ofConv
      (TauCeti.HopfAlgebra.pointConjugationAlgHom (toConv ((Polynomial.aeval s).comp b)) a) := by
    have hL := TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom
      (toConv b) (toConv cy)
    have hpoint := congrArg (TauCeti.AlgHom.mapValue (H := H) (Polynomial.aeval s))
      (congrArg toConv hL)
    rw [map_mul, map_mul, map_inv] at hpoint
    have hcy : TauCeti.AlgHom.mapValue (Polynomial.aeval s) (toConv cy) = y := by
      apply WithConv.ext
      apply AlgHom.ext
      intro a
      simp [TauCeti.AlgHom.mapValue_apply, cy, AlgHom.comp_apply]
    rw [hcy] at hpoint
    have hR := TauCeti.HopfAlgebra.comp_pointConjugationAlgHom
      (toConv ((Polynomial.aeval s).comp b)) y
    have hself : TauCeti.AlgHom.mapValue (Algebra.ofId k k)
        (toConv ((Polynomial.aeval s).comp b)) = toConv ((Polynomial.aeval s).comp b) := by
      apply WithConv.ext
      apply AlgHom.ext
      intro a
      simp
    rw [hself] at hR
    have hbval : TauCeti.AlgHom.mapValue (Polynomial.aeval s) (toConv b) =
        toConv ((Polynomial.aeval s).comp b) :=
      TauCeti.AlgHom.mapValue_apply _ _
    rw [hbval] at hpoint
    have hp := hpoint.trans hR.symm
    have heval := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) hp
    simpa [P, TauCeti.AlgHom.mapValue_apply, AlgHom.comp_apply] using heval
  have hz : P = 0 := by
    apply CFSG.LinearAlgebra.polynomial_eq_of_eval_natCast
    intro r
    have ha' : TauCeti.HopfAlgebra.pointConjugationAlgHom
        (toConv ((Polynomial.aeval (r : k)).comp b)) a ∈ I :=
      TauCeti.HopfIdeal.mem_conjugate.mp (hnat r ha)
    have hkill := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I
      (CommAlgCat.of k k) y).mp hy _ ha'
    rw [hvalue, hkill, Polynomial.eval_zero]
  have hkill : y.ofConv
      (TauCeti.HopfAlgebra.pointConjugationAlgHom (toConv ((Polynomial.aeval t).comp b)) a) = 0 :=
    (hvalue t).symm.trans (by rw [hz, Polynomial.eval_zero])
  have hyval : y.ofConv =
      x.comp (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom.toAlgHom :=
    (rfl)
  rw [hyval, AlgHom.comp_apply] at hkill
  exact hkill.trans (map_zero x).symm

theorem conjugate_eq_of_unipotentPowerCurve
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)]
    (g : WithConv (H →ₐ[k] k)) (b : H →ₐ[k] Polynomial k)
    (hb : ∀ r : ℕ, toConv ((Polynomial.aeval (r : k)).comp b) = g ^ r)
    (hgI : I.conjugate g = I) (t : k) :
    I.conjugate (toConv ((Polynomial.aeval t).comp b)) = I := by
  have hpow : ∀ r : ℕ, I.conjugate (g ^ r) = I := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, TauCeti.HopfIdeal.conjugate_mul, hgI, ih]
  have hle := le_conjugate_of_curve_natCast H I b (fun r => by rw [hb r, hpow r]) t
  let binv : H →ₐ[k] Polynomial k := (toConv b)⁻¹.ofConv
  have hginvI : I.conjugate g⁻¹ = I := by
    simpa only [TauCeti.HopfIdeal.conjugate_inv_conjugate] using
      (congrArg (fun I : TauCeti.HopfIdeal k H => I.conjugate g⁻¹) hgI).symm
  have hpowinv : ∀ r : ℕ, I.conjugate (g⁻¹ ^ r) = I := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, TauCeti.HopfIdeal.conjugate_mul, hginvI, ih]
  have hinv (s : k) : toConv ((Polynomial.aeval s).comp binv) =
      (toConv ((Polynomial.aeval s).comp b))⁻¹ := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    simp only [binv, AlgHom.comp_apply, TauCeti.AlgHom.convInv_apply]
  have hleinv := le_conjugate_of_curve_natCast H I binv
    (fun r => by rw [hinv, hb, ← inv_pow, hpowinv]) t
  have hleback := TauCeti.HopfIdeal.conjugate_mono (toConv ((Polynomial.aeval t).comp b)) hleinv
  rw [hinv, TauCeti.HopfIdeal.conjugate_conjugate_inv] at hleback
  exact le_antisymm hleback hle

theorem exists_pow_eq_of_isUnipotentPoint_map_conjugate_eq
    (H B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (f : B →ₐc[k] H)
    (g : WithConv (H →ₐ[k] k)) (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g)
    (I : TauCeti.HopfIdeal k B)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I)]
    (hgI : I.conjugate (TauCeti.AlgHom.mapDomain f g) = I)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ h : WithConv (H →ₐ[k] k), h ^ m = g ∧
      I.conjugate (TauCeti.AlgHom.mapDomain f h) = I := by
  obtain ⟨b, hb⟩ := exists_unipotentPowerCurve H g hg
  let bp : WithConv (H →ₐ[k] Polynomial k) := toConv b
  let bscale : H →ₐ[k] Polynomial k :=
    (Polynomial.aeval (Polynomial.C (m : k) * Polynomial.X)).comp b
  have heq : (bp ^ m).ofConv = bscale := by
    apply AlgHom.ext
    intro a
    apply CFSG.LinearAlgebra.polynomial_eq_of_eval_natCast
    intro r
    have hpow := map_pow (TauCeti.AlgHom.mapValue (H := H) (Polynomial.aeval (r : k))) bp m
    have hnat : TauCeti.AlgHom.mapValue (Polynomial.aeval (r : k)) bp = g ^ r := by
      simpa only [TauCeti.AlgHom.mapValue_apply, bp] using hb r
    rw [hnat] at hpow
    have ha := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) hpow
    have hscale : (Polynomial.aeval (r : k)).comp
        (Polynomial.aeval (Polynomial.C (m : k) * Polynomial.X)) =
        Polynomial.aeval ((m * r : ℕ) : k) := by
      apply Polynomial.algHom_ext
      simp [AlgHom.comp_apply, Polynomial.aeval_X]
    have hright := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) (hb (m * r))
    have hscalea : (Polynomial.aeval (r : k)) (bscale a) =
        (Polynomial.aeval ((m * r : ℕ) : k)) (b a) := by
      exact congrArg (fun f : Polynomial k →ₐ[k] k => f (b a)) hscale
    have hleft : ((bp ^ m).ofConv a).eval (r : k) = ((g ^ r) ^ m).ofConv a := by
      simpa [TauCeti.AlgHom.mapValue_apply, AlgHom.comp_apply] using ha
    have heval : Polynomial.aeval (r : k) (bscale a) = (bscale a).eval (r : k) := by
      simp
    have hvalue : Polynomial.aeval ((m * r : ℕ) : k) (b a) =
        (g ^ (m * r)).ofConv a := by
      simpa only [ofConv_toConv, AlgHom.comp_apply] using hright
    have hpows : (g ^ r) ^ m = g ^ (m * r) := by
      rw [← pow_mul, Nat.mul_comm]
    exact hleft.trans ((congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) hpows).trans
      (heval.symm.trans (hscalea.trans hvalue)).symm)
  let h : WithConv (H →ₐ[k] k) := toConv ((Polynomial.aeval ((m : k)⁻¹)).comp b)
  have hpow : h ^ m = g := by
    have hp := map_pow (TauCeti.AlgHom.mapValue (H := H)
      (Polynomial.aeval ((m : k)⁻¹))) bp m
    have hscale : (Polynomial.aeval ((m : k)⁻¹)).comp
        (Polynomial.aeval (Polynomial.C (m : k) * Polynomial.X)) = Polynomial.aeval (1 : k) := by
      apply Polynomial.algHom_ext
      simp [AlgHom.comp_apply, Polynomial.aeval_X,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm : (m : k) ≠ 0)]
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    have ha := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) hp
    simp only [TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at ha
    rw [heq] at ha
    have hscalea : Polynomial.aeval ((m : k)⁻¹) (bscale a) =
        Polynomial.aeval (1 : k) (b a) := by
      simpa only [bscale, AlgHom.comp_apply] using
        congrArg (fun f : Polynomial k →ₐ[k] k => f (b a)) hscale
    have hnat1 := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) (hb 1)
    have hnat1' : Polynomial.aeval (1 : k) (b a) = g.ofConv a := by
      simpa only [ofConv_toConv, AlgHom.comp_apply, Nat.cast_one, pow_one] using hnat1
    have ha' : (h ^ m).ofConv a = Polynomial.aeval ((m : k)⁻¹) (bscale a) := by
      simpa only [h, bp, ofConv_toConv] using ha.symm
    exact ha'.trans (hscalea.trans hnat1')
  let bB : B →ₐ[k] Polynomial k := b.comp f.toAlgHom
  have hbB (r : ℕ) : toConv ((Polynomial.aeval (r : k)).comp bB) =
      (TauCeti.AlgHom.mapDomain f g) ^ r := by
    calc
      _ = TauCeti.AlgHom.mapDomain f (toConv ((Polynomial.aeval (r : k)).comp b)) := by
        simp only [TauCeti.AlgHom.mapDomain_apply, bB, AlgHom.comp_assoc]
      _ = TauCeti.AlgHom.mapDomain f (g ^ r) := by rw [hb]
      _ = _ := map_pow _ _ _
  have hhB : toConv ((Polynomial.aeval ((m : k)⁻¹)).comp bB) =
      TauCeti.AlgHom.mapDomain f h := by
    simp only [TauCeti.AlgHom.mapDomain_apply, bB, h, AlgHom.comp_assoc]
  refine ⟨h, hpow, ?_⟩
  simpa only [hhB] using conjugate_eq_of_unipotentPowerCurve B I
    (TauCeti.AlgHom.mapDomain f g) bB hbB hgI ((m : k)⁻¹)

omit [IsAlgClosed k] in
theorem exists_pow_eq_of_unipotent_matrix_image
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (f : TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H)
    (hf : Function.Surjective f) (g : WithConv (H →ₐ[k] k)) {d : ℕ}
    (hU : ((TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain f g) : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ h : WithConv (H →ₐ[k] k), h ^ m = g := by
  let U := TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)
  let c := CFSG.LinearAlgebra.unipotentPowerCoordinate U hU
  obtain ⟨b, hb⟩ := exists_unipotentPowerCurve_of_matrix_image H f hf g hU
  have hb' : b.comp f.toAlgHom = c := hb
  let h : WithConv (H →ₐ[k] k) := toConv ((Polynomial.aeval ((m : k)⁻¹)).comp b)
  refine ⟨h, ?_⟩
  have hinj : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) f) := by
    intro x y hxy
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := hf a
    have he := congrArg (fun p : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k) => p.ofConv a) hxy
    simpa only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using he
  apply hinj
  rw [map_pow]
  apply (TauCeti.GeneralLinear.pointsMulEquiv n).injective
  rw [map_pow]
  have hh : TauCeti.AlgHom.mapDomain f h =
      toConv ((Polynomial.aeval ((m : k)⁻¹)).comp c) := by
    simp only [h, TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_assoc, hb']
  rw [hh, CFSG.LinearAlgebra.unipotentPowerCoordinate_eval]
  rw [← TauCeti.GeneralLinear.pointsMulEquiv_symm_apply, MulEquiv.apply_symm_apply]
  exact CFSG.LinearAlgebra.map_unipotentPolynomialPowersUnit_inv_natCast_pow U hU hm

omit [IsAlgClosed k] in
theorem exists_pow_eq_of_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (g : WithConv (H →ₐ[k] k)) (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ h : WithConv (H →ₐ[k] k), h ^ m = g := by
  obtain ⟨D, hD, _, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H
    (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  let f := TauCeti.Comodule.coordinateBialgHom (H := H) b
  have hnil := isNilpotent_toMatrix_basePointsRepresentation_sub_one b g hg
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g] at hnil
  obtain ⟨d, hd⟩ := hnil
  exact exists_pow_eq_of_unipotent_matrix_image H f
    (coordinateBialgHom_surjective_of_generating_subcoalgebra D hgen b) g hd hm

omit [IsAlgClosed k] in
theorem pow_injective_of_forall_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (fun g : WithConv (H →ₐ[k] k) => g ^ m) := by
  obtain ⟨D, hD, _, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H
    (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  let f := TauCeti.Comodule.coordinateBialgHom (H := H) b
  let ρ : WithConv (H →ₐ[k] k) →* Matrix.GeneralLinearGroup (Fin
      (Module.finrank k D.toRegularSubcomodule)) k :=
    (TauCeti.GeneralLinear.pointsMulEquiv _).toMonoidHom.comp (TauCeti.AlgHom.mapDomain f)
  intro g h hpow
  have hg := isNilpotent_toMatrix_basePointsRepresentation_sub_one b g (hH g)
  have hh := isNilpotent_toMatrix_basePointsRepresentation_sub_one b h (hH h)
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g] at hg
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b h] at hh
  have hmatrix : ρ g = ρ h := CFSG.LinearAlgebra.eq_of_pow_eq_of_isUnipotent
    (ρ g) (ρ h) hg hh hm (by simpa only [map_pow] using congrArg ρ hpow)
  apply basePointsRepresentation_injective_of_generating_subcoalgebra D hgen
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g,
    ← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b h]
  exact congrArg Units.val hmatrix

omit [IsAlgClosed k] in
theorem cube_bijective_of_unipotent_of_charZero
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    Function.Bijective (fun g : WithConv (H →ₐ[k] k) => g ^ 3) :=
  ⟨pow_injective_of_forall_isUnipotentPoint H hH (by decide),
    fun g => exists_pow_eq_of_isUnipotentPoint H g (hH g) (by decide)⟩

end CharZero

omit [IsAlgClosed k] in
theorem cube_bijective_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    (h3 : (3 : k) ≠ 0) :
    Function.Bijective (fun g : WithConv (H →ₐ[k] k) => g ^ 3) := by
  by_cases hchar : CharZero k
  · let := hchar
    exact cube_bijective_of_unipotent_of_charZero H hH
  · have hp0 : ringChar k ≠ 0 := fun h =>
      hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : (ringChar k).Prime := (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp0
    have htop := cube_bijective_of_unipotent_of_charP H (⊤ : Subgroup (WithConv (H →ₐ[k] k)))
      (fun g _ => hH g) hp h3
    constructor
    · intro g h heq
      have h := htop.1 (show (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup _)) ^ 3 =
        ⟨h, Subgroup.mem_top h⟩ ^ 3 from Subtype.ext heq)
      exact congrArg Subtype.val h
    · intro g
      obtain ⟨h, hh⟩ := htop.2 ⟨g, Subgroup.mem_top g⟩
      exact ⟨h, congrArg Subtype.val hh⟩

omit [IsAlgClosed k] in
theorem pow_bijective_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : (m : k) ≠ 0) :
    Function.Bijective (fun g : WithConv (H →ₐ[k] k) => g ^ m) := by
  by_cases hchar : CharZero k
  · let := hchar
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    exact ⟨pow_injective_of_forall_isUnipotentPoint H hH hm0,
      fun g => exists_pow_eq_of_isUnipotentPoint H g (hH g) hm0⟩
  · have hp0 : ringChar k ≠ 0 := fun h =>
      hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp0
    let : Fact (ringChar k).Prime := ⟨hp⟩
    have hcop : ¬ ringChar k ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k (ringChar k) m).mpr h)
    let N := (⊤ : Subgroup (WithConv (H →ₐ[k] k)))
    have hN : Function.Bijective (fun g : N => g ^ m) :=
      (IsPGroup.powEquiv' (isPGroup_of_unipotent H N (fun g _ => hH g) hp) hcop).bijective
    constructor
    · intro g h heq
      have h := hN.1 (show (⟨g, Subgroup.mem_top g⟩ : N) ^ m =
        ⟨h, Subgroup.mem_top h⟩ ^ m from Subtype.ext heq)
      exact congrArg Subtype.val h
    · intro g
      obtain ⟨h, hh⟩ := hN.2 ⟨g, Subgroup.mem_top g⟩
      exact ⟨h, congrArg Subtype.val hh⟩

theorem cube_bijective_of_unipotent_conjugate_stabilizer
    (H B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (f : B →ₐc[k] H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    (I : TauCeti.HopfIdeal k B)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I)]
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g, g ∈ N ↔ I.conjugate (TauCeti.AlgHom.mapDomain f g) = I)
    (h3 : (3 : k) ≠ 0) :
    Function.Bijective (fun g : N => g ^ 3) := by
  by_cases hchar : CharZero k
  · let := hchar
    constructor
    · intro g h heq
      apply Subtype.ext
      exact pow_injective_of_forall_isUnipotentPoint H hH (by decide)
        (congrArg Subtype.val heq)
    · intro g
      obtain ⟨h, hpow, hI⟩ := exists_pow_eq_of_isUnipotentPoint_map_conjugate_eq
        H B f g (hH g) I ((hN g).mp g.property) (m := 3) (by decide)
      exact ⟨⟨h, (hN h).mpr hI⟩, Subtype.ext hpow⟩
  · have hp0 : ringChar k ≠ 0 := fun h =>
      hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp0
    exact cube_bijective_of_unipotent_of_charP H N (fun g _ => hH g) hp h3

abbrev MaximalTorusIdeals (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :=
  {I : TauCeti.HopfIdeal k B // TauCeti.HopfIdeal.IsMaximalTorus k B.obj I}

noncomputable instance maximalTorusIdealsMulAction
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    MulAction (WithConv (B →ₐ[k] k)) (MaximalTorusIdeals B) where
  smul g I := ⟨I.val.conjugate g, I.property.conjugate g⟩
  one_smul I := Subtype.ext (TauCeti.HopfIdeal.conjugate_one I.val)
  mul_smul g h I := Subtype.ext (TauCeti.HopfIdeal.conjugate_mul I.val g h)

instance maximalTorusIdealsNonempty (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Nonempty (MaximalTorusIdeals B) := by
  obtain ⟨I, hI⟩ := TauCeti.HopfIdeal.exists_isMaximalTorus B
  exact ⟨⟨I, hI⟩⟩

def maximalTorusIdealsEnd
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : B →ₐc[k] B)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k B) :
    MaximalTorusIdeals B → MaximalTorusIdeals B := fun I =>
  let e : B ≅ B := ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (CanonicalReductive.autIso B σ hσ)
  ⟨I.val.comapOfSurjective σ (CanonicalReductive.aut_bijective B σ hσ).2,
    by
      have he : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom = σ :=
        CanonicalReductive.autIso_hom_hom B σ hσ
      simpa only [he] using I.property.comapOfIso e⟩

omit [IsAlgClosed k] in
theorem maximalTorusIdealsEnd_cube
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : B →ₐc[k] B)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k B) (I : MaximalTorusIdeals B) :
    maximalTorusIdealsEnd B σ hσ (maximalTorusIdealsEnd B σ hσ
      (maximalTorusIdealsEnd B σ hσ I)) = I := by
  apply Subtype.ext
  apply TauCeti.HopfIdeal.ext
  intro x
  change x ∈ ((I.val.comapOfSurjective σ _).comapOfSurjective σ _).comapOfSurjective σ _ ↔
    x ∈ I.val
  simp only [TauCeti.HopfIdeal.mem_comapOfSurjective]
  have hx : σ (σ (σ x)) = x := congrArg (fun f : B →ₐc[k] B => f x) hσ
  rw [hx]

theorem pointConjugation_comp_naturality
    (B C : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced C]
    (f : B →ₐc[k] C) (g : WithConv (C →ₐ[k] k)) :
    f.toAlgHom.comp (TauCeti.HopfAlgebra.pointConjugationAlgHom
      (TauCeti.AlgHom.mapDomain f g)) =
      (TauCeti.HopfAlgebra.pointConjugationAlgHom g).comp f.toAlgHom := by
  apply AlgHom.ext
  intro a
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro x
  let y : WithConv (C →ₐ[k] k) := toConv x
  have hL := TauCeti.HopfAlgebra.comp_pointConjugationAlgHom
    (TauCeti.AlgHom.mapDomain f g) (TauCeti.AlgHom.mapDomain f y)
  have hR := TauCeti.HopfAlgebra.comp_pointConjugationAlgHom g y
  have hself (z : WithConv (C →ₐ[k] k)) :
      TauCeti.AlgHom.mapValue (Algebra.ofId k k) z = z := by
    apply WithConv.ext
    ext a
    simp
  have hselfB (z : WithConv (B →ₐ[k] k)) :
      TauCeti.AlgHom.mapValue (Algebra.ofId k k) z = z := by
    apply WithConv.ext
    ext a
    simp
  rw [hselfB] at hL
  rw [hself] at hR
  have hR' := congrArg (TauCeti.AlgHom.mapDomain f) hR
  rw [map_mul, map_mul, map_inv] at hR'
  have hp := hL.trans hR'.symm
  have ha := congrArg (fun p : WithConv (B →ₐ[k] k) => p.ofConv a) hp
  simpa only [y, TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply] using ha

theorem comap_conjugate_naturality
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced B]
    (σ : B →ₐc[k] B) (hσ : Function.Surjective σ)
    (I : TauCeti.HopfIdeal k B) (g : WithConv (B →ₐ[k] k)) :
    (I.conjugate g).comapOfSurjective σ hσ =
      (I.comapOfSurjective σ hσ).conjugate (TauCeti.AlgHom.mapDomain σ g) := by
  apply TauCeti.HopfIdeal.ext
  intro a
  simp only [TauCeti.HopfIdeal.mem_comapOfSurjective, TauCeti.HopfIdeal.mem_conjugate]
  have h := congrArg (fun f : B →ₐ[k] B => f a)
    (pointConjugation_comp_naturality B B σ g)
  have h' : σ (TauCeti.HopfAlgebra.pointConjugationAlgHom
      (TauCeti.AlgHom.mapDomain σ g) a) =
    TauCeti.HopfAlgebra.pointConjugationAlgHom g (σ a) := by
    simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] using h
  change TauCeti.HopfAlgebra.pointConjugationAlgHom g (σ a) ∈ I ↔
    σ (TauCeti.HopfAlgebra.pointConjugationAlgHom (TauCeti.AlgHom.mapDomain σ g) a) ∈ I
  rw [h']

theorem maximalTorusIdealsEnd_equivariant
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced B]
    (σ : B →ₐc[k] B) (hσ : (σ.comp σ).comp σ = BialgHom.id k B)
    (g : WithConv (B →ₐ[k] k)) (I : MaximalTorusIdeals B) :
    maximalTorusIdealsEnd B σ hσ (g • I) =
      TauCeti.AlgHom.mapDomain σ g • maximalTorusIdealsEnd B σ hσ I := by
  apply Subtype.ext
  exact comap_conjugate_naturality B σ (CanonicalReductive.aut_bijective B σ hσ).2 I.val g

abbrev unipotentRadicalActor
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : B →ₐc[k] B)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k B) :
    MulAut (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k)) :=
  let e : B ≅ B := ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (CanonicalReductive.autIso B σ hσ)
  let eU := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalIsoOfIso e
  TauCeti.AlgHom.mapDomainMulEquiv
    (BialgEquiv.ofBijective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom eU.hom)
      (ConcreteCategory.bijective_of_isIso eU.hom))

abbrev unipotentRadicalPointsHom (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k) →*
      WithConv (B →ₐ[k] k) :=
  TauCeti.AlgHom.mapDomain
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap B))

omit [IsAlgClosed k] in
theorem unipotentRadicalActor_equivariant
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : B →ₐc[k] B)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k B)
    (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k)) :
    unipotentRadicalPointsHom B (unipotentRadicalActor B σ hσ u) =
      TauCeti.AlgHom.mapDomain σ (unipotentRadicalPointsHom B u) := by
  let e : B ≅ B := ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (CanonicalReductive.autIso B σ hσ)
  let eU := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalIsoOfIso e
  have he := congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom e)
  have hσ' : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom = σ :=
    CanonicalReductive.autIso_hom_hom B σ hσ
  simp only [TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, hσ'] at he
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  have ha := congrArg (fun f : B →ₐc[k]
      TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B => u.ofConv (f a)) he
  have hactor : unipotentRadicalActor B σ hσ u =
      TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom eU.hom) u := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    simp only [unipotentRadicalActor, TauCeti.AlgHom.mapDomainMulEquiv_apply,
      TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    rfl
  rw [hactor]
  simpa only [unipotentRadicalPointsHom, TauCeti.AlgHom.mapDomain_apply,
    ofConv_toConv, AlgHom.comp_apply, BialgHom.comp_apply, BialgHom.coe_toAlgHom] using ha

omit [IsAlgClosed k] in
theorem unipotentRadicalPointsHom_injective
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Function.Injective (unipotentRadicalPointsHom B) := by
  intro u v huv
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  have hsurj : Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap B)) := by
    rw [TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_def]
    exact TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _
  obtain ⟨a, rfl⟩ := hsurj x
  have h := congrArg (fun p : WithConv (B →ₐ[k] k) => p.ofConv a) huv
  simpa only [unipotentRadicalPointsHom, TauCeti.AlgHom.mapDomain_apply,
    ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom] using h

omit [IsAlgClosed k] in
theorem unipotentRadicalActor_cube
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : B →ₐc[k] B)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k B) :
    unipotentRadicalActor B σ hσ ^ 3 = 1 := by
  apply MulEquiv.ext
  intro u
  apply unipotentRadicalPointsHom_injective B
  have hactor : (unipotentRadicalActor B σ hσ ^ 3) u =
      unipotentRadicalActor B σ hσ (unipotentRadicalActor B σ hσ
        (unipotentRadicalActor B σ hσ u)) := by
    rfl
  rw [hactor, unipotentRadicalActor_equivariant,
    unipotentRadicalActor_equivariant, unipotentRadicalActor_equivariant]
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  simp only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, MulAut.one_apply]
  rw [show σ (σ (σ a)) = a from congrArg (fun f : B →ₐc[k] B => f a) hσ]

omit [IsAlgClosed k] in
theorem unipotentRadical_points_unipotent
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    ∀ g : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  have hu := TauCeti.FiniteTypeCommHopfAlgCat.smoothUnipotent_unipotentRadical B
  have hgeom : TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B).obj :=
    by
      rw [TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff]
      exact ((TauCeti.smoothUnipotentCommHopfAlgProperty_iff k _).mp hu).2
  exact TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint hgeom

omit [IsAlgClosed k] in
theorem unipotentRadical_isReduced
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B) := by
  have hu := TauCeti.FiniteTypeCommHopfAlgCat.smoothUnipotent_unipotentRadical B
  let : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B) :=
    ((TauCeti.smoothUnipotentCommHopfAlgProperty_iff k _).mp hu).1
  exact TauCeti.isReduced_of_smooth k _

noncomputable instance unipotentRadicalMaximalTorusAction
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    MulAction (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k))
      (MaximalTorusIdeals B) :=
  MulAction.compHom (MaximalTorusIdeals B) (unipotentRadicalPointsHom B)

theorem cube_bijective_unipotentRadical_maximalTorus_stabilizer
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : MaximalTorusIdeals B) (h3 : (3 : k) ≠ 0) :
    Function.Bijective (fun g : MulAction.stabilizer
      (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k)) I => g ^ 3) := by
  let T := TauCeti.FiniteTypeCommHopfAlgCat.quotient B I.val
  have hT : TauCeti.torusCommHopfAlgProperty k T :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k B.obj I.val).mp I.property).1
  let : Algebra.Smooth k T :=
    (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  apply cube_bijective_of_unipotent_conjugate_stabilizer
    (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B) B
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap B))
    (unipotentRadical_points_unipotent B) I.val
    (MulAction.stabilizer _ I) ?_ h3
  intro g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨I.val.conjugate (unipotentRadicalPointsHom B g), I.property.conjugate _⟩ :
    MaximalTorusIdeals B) = I ↔ I.val.conjugate (unipotentRadicalPointsHom B g) = I.val
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

theorem exists_stable_maximalTorus_of_unipotent_conjugacy
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced B]
    (σ : B →ₐc[k] B) (hσ : (σ.comp σ).comp σ = BialgHom.id k B)
    (h3 : (3 : k) ≠ 0)
    (htrans : ∀ I J : MaximalTorusIdeals B,
      ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k),
        I.val.conjugate (unipotentRadicalPointsHom B u) = J.val) :
    ∃ I : TauCeti.HopfIdeal k B, TauCeti.HopfIdeal.IsMaximalTorus k B.obj I ∧
      I.comapOfSurjective σ (CanonicalReductive.aut_bijective B σ hσ).2 = I := by
  let U := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B
  let : IsReduced U := unipotentRadical_isReduced B
  let : Group.IsNilpotent (WithConv (U →ₐ[k] k)) :=
    isNilpotent_points_of_forall_isUnipotentPoint U (unipotentRadical_points_unipotent B)
  obtain ⟨I, hI⟩ := CFSG.GroupTheory.exists_fixed_of_transitive_of_nilpotent
    (G := WithConv (U →ₐ[k] k)) (P := MaximalTorusIdeals B)
    (fun I J => by obtain ⟨u, hu⟩ := htrans I J; exact ⟨u, Subtype.ext hu⟩)
    (cube_bijective_of_unipotent U (unipotentRadical_points_unipotent B) h3)
    (fun I => cube_bijective_unipotentRadical_maximalTorus_stabilizer B I h3)
    (unipotentRadicalActor B σ hσ) (unipotentRadicalActor_cube B σ hσ)
    (maximalTorusIdealsEnd B σ hσ) (maximalTorusIdealsEnd_cube B σ hσ)
    (by
      intro u I
      change maximalTorusIdealsEnd B σ hσ (unipotentRadicalPointsHom B u • I) =
        unipotentRadicalPointsHom B (unipotentRadicalActor B σ hσ u) •
          maximalTorusIdealsEnd B σ hσ I
      rw [maximalTorusIdealsEnd_equivariant, unipotentRadicalActor_equivariant])
  exact ⟨I.val, I.property, congrArg Subtype.val hI⟩

end CFSG.LieType.AlgebraicGroups
