module

public import CFSG.LieType.AlgebraicGroups.InnerTwistDifferential
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.CartanCentralizer
public import CFSG.LieType.AlgebraicGroups.GradedRepresentationKernel
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.Mathlib.RingTheory.FiniteFiberInjective
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import CFSG.LinearAlgebra.FiniteSpanningAction
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial
public import CFSG.Mathlib.FieldTheory.InfiniteUnitPowers
public import CFSG.ThirdParty.TauCeti.DynamicRepresentability
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.ChangeBasis
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
public import TauCeti.RingTheory.Polynomial.BinomialBasis
public import TauCeti.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.TensorProduct.PointSeparation

public noncomputable section

open TauCeti WithConv TauCeti.Comodule
open scoped CFSG.ConvolutionPoints

namespace CFSG.LieType.AlgebraicGroups

variable {k : Type} [Field k]

section FiniteCentralizer

variable [IsAlgClosed k] (H : TauCeti.FiniteTypeCommHopfAlgCat.{0,0} k) [IsDomain H]

theorem pointMap_one_eq (g : WithConv (H →ₐ[k] k)) :
    pointMap (A := H) (1 : H →ₐc[k] H) g = g := by
  rw [pointMap_apply]
  change toConv (g.ofConv.comp (AlgHom.id k H)) = g
  rw [AlgHom.comp_id, ofConv_toConv]

theorem finite_centralizer_fibre (x : WithConv (H →ₐ[k] k))
    (hcentral : {h : WithConv (H →ₐ[k] k) | Commute h x}.Finite) :
    {s' : H →ₐ[k] k |
      s'.comp (twistOrbitCo (A := H) (1 : H →ₐc[k] H) x) = x.ofConv.comp (twistOrbitCo (A := H) (1 : H →ₐc[k] H) x)}.Finite := by
  classical
  let f : H →ₐ[k] H := twistOrbitCo (A := H) (1 : H →ₐc[k] H) x
  let toFib : {g : WithConv (H →ₐ[k] k) // Commute g x} →
      {s' : H →ₐ[k] k // s'.comp f = x.ofConv.comp f} := fun g => by
    refine ⟨g.1.ofConv, ?_⟩
    apply WithConv.toConv_injective
    have hconj : g.1 * x * g.1⁻¹ = x := by
      rw [g.2.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [point_comp_twistOrbitCo, point_comp_twistOrbitCo, pointMap_one_eq, pointMap_one_eq,
      hconj]
    group
  letI : Finite {g : WithConv (H →ₐ[k] k) // Commute g x} := hcentral.to_subtype
  have hsurj : Function.Surjective toFib := by
    intro s
    let g : WithConv (H →ₐ[k] k) := toConv s.1
    have hconj : g * x * g⁻¹ = x := by
      have hs := congrArg WithConv.toConv s.2
      change toConv (g.ofConv.comp (twistOrbitCo (A := H)
        (1 : H →ₐc[k] H) x)) =
        toConv (x.ofConv.comp (twistOrbitCo (A := H)
        (1 : H →ₐc[k] H) x)) at hs
      rw [point_comp_twistOrbitCo, point_comp_twistOrbitCo,
        pointMap_one_eq, pointMap_one_eq] at hs
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hs
    refine ⟨⟨g, mul_inv_eq_iff_eq_mul.mp hconj⟩, ?_⟩
    apply Subtype.ext
    rfl
  letI : Finite {g : WithConv (H →ₐ[k] k) // Commute g x} := hcentral.to_subtype
  let toBase : {g : WithConv (H →ₐ[k] k) // Commute g x} → H →ₐ[k] k := fun g => g.1.ofConv
  have hrange : toBase '' Set.univ = {s' : H →ₐ[k] k | s'.comp f = x.ofConv.comp f} := by
    ext s
    constructor
    · rintro ⟨g, -, rfl⟩
      exact (toFib g).2
    · intro hs
      obtain ⟨g, hg⟩ := hsurj ⟨s, hs⟩
      exact ⟨g, Set.mem_univ _, congrArg Subtype.val hg⟩
  rw [← hrange]
  exact Set.Finite.image toBase Set.finite_univ

theorem exists_coeff_charpoly_const_of_finite_centralizer
    (x : WithConv (H →ₐ[k] k))
    (hcentral : {h : WithConv (H →ₐ[k] k) | Commute h x}.Finite)
    {W : Type} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
    [Module.Finite k W] :
    ∃ c : ℕ → H, (∀ (g : WithConv (H →ₐ[k] k)) (i : ℕ),
        g.ofConv (c i) =
          (LinearMap.charpoly
            (basePointsRepresentation (H := H) W g)).coeff i) ∧
      ∀ i, c i = algebraMap k H (x.ofConv (c i)) := by
  classical
  obtain ⟨c, hc⟩ := CartanComponent.exists_apply_eq_coeff_charpoly
    (k := k) (M := H) (W := W)
  let f : H →ₐ[k] H := twistOrbitCo (A := H) (1 : H →ₐc[k] H) x
  have hfib : {s' : H →ₐ[k] k | s'.comp f = x.ofConv.comp f}.Finite := by
    simpa only [f] using finite_centralizer_fibre H x hcentral
  have hinj : Function.Injective f :=
    CFSG.algHom_injective_of_finite_fiber f x.ofConv hfib
  refine ⟨c, hc, ?_⟩
  intro i
  let b : H := c i - algebraMap k H (x.ofConv (c i))
  have hbzero : f b = 0 := by
    by_contra hne
    obtain ⟨z, hz⟩ := TauCeti.exists_algHom_apply_ne_zero_of_ne_zero (k := k) (K := k) hne
    let g : WithConv (H →ₐ[k] k) := toConv z
    have hzcf : toConv (z.comp f) = g * x * g⁻¹ := by
      have h' := point_comp_twistOrbitCo (A := H) (1 : H →ₐc[k] H) x g
      simpa only [g, ofConv_toConv, pointMap_one_eq] using h'
    have hchar : (LinearMap.charpoly
          (basePointsRepresentation (H := H) W (g * x * g⁻¹))).coeff i =
        (LinearMap.charpoly (basePointsRepresentation (H := H) W x)).coeff i := by
      let ρ : WithConv (H →ₐ[k] k) →* Module.End k W :=
        basePointsRepresentation (H := H) W
      let e : W ≃ₗ[k] W := LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      have hconj : ρ (g * x * g⁻¹) = e.conj (ρ x) := by
        apply LinearMap.ext
        intro v
        simp [e, LinearEquiv.conj_apply, map_mul]
      rw [show basePointsRepresentation (H := H) W (g * x * g⁻¹) = ρ (g * x * g⁻¹) from rfl,
        show basePointsRepresentation (H := H) W x = ρ x from rfl,
        hconj, LinearEquiv.charpoly_conj]
    have hcoeffg : (z.comp f) (c i) = x.ofConv (c i) := by
      calc
        (z.comp f) (c i) = (toConv (z.comp f)).ofConv (c i) := by rw [ofConv_toConv]
        _ = (g * x * g⁻¹).ofConv (c i) := by rw [hzcf]
        _ = (LinearMap.charpoly
              (basePointsRepresentation (H := H) W (g * x * g⁻¹))).coeff i := hc (g * x * g⁻¹) i
        _ = (LinearMap.charpoly (basePointsRepresentation (H := H) W x)).coeff i := hchar
        _ = x.ofConv (c i) := (hc x i).symm
    have hzval : z (f b) = 0 := by
      change (z.comp f) b = 0
      simp only [b, map_sub, AlgHom.comp_apply, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
      rw [← AlgHom.comp_apply, hcoeffg, sub_self]
    exact hz hzval
  have hb : b = 0 := by
    apply hinj
    simpa using hbzero
  exact sub_eq_zero.mp hb

theorem isUnipotentPoint_of_finite_centralizer
    {x : WithConv (H →ₐ[k] k)}
    (hcentral : {h : WithConv (H →ₐ[k] k) | Commute h x}.Finite) :
    TauCeti.HopfAlgebra.IsUnipotentPoint x := by
  classical
  obtain ⟨V, d, b, hb⟩ :=
    TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k V := Module.Finite.of_basis b
  have hfaith : TauCeti.Comodule.IsFaithful (k := k) (H := H) (V := V) := by
    rw [TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
      TauCeti.Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff]
    exact hb
  obtain ⟨c, hc, hconst⟩ :=
    exists_coeff_charpoly_const_of_finite_centralizer H x hcentral (W := V)
  have hchar : LinearMap.charpoly (basePointsRepresentation (H := H) V x) =
      (Polynomial.X - 1 : Polynomial k) ^ d := by
    ext i
    have hchar1 : LinearMap.charpoly
        (basePointsRepresentation (H := H) V (1 : WithConv (H →ₐ[k] k))) =
        (Polynomial.X - 1 : Polynomial k) ^ d := by
      rw [map_one, LinearMap.charpoly_one, Module.finrank_eq_card_basis b]
      simp
    have h1eq : (1 : WithConv (H →ₐ[k] k)).ofConv (c i) = x.ofConv (c i) := by
      rw [hconst i]
      simpa using (AlgHom.commutes ((1 : WithConv (H →ₐ[k] k)).ofConv) (x.ofConv (c i)))
    calc
      (LinearMap.charpoly (basePointsRepresentation (H := H) V x)).coeff i =
          x.ofConv (c i) := (hc x i).symm
      _ = (1 : WithConv (H →ₐ[k] k)).ofConv (c i) := h1eq.symm
      _ = (LinearMap.charpoly
            (basePointsRepresentation (H := H) V (1 : WithConv (H →ₐ[k] k)))).coeff i := hc 1 i
      _ = ((Polynomial.X - 1 : Polynomial k) ^ d).coeff i := by rw [hchar1]
  have hCH := LinearMap.aeval_self_charpoly (basePointsRepresentation (H := H) V x)
  rw [hchar, map_pow, map_sub, Polynomial.aeval_X, map_one] at hCH
  exact GradedKernel.isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one
    (M := H) (V := V) hfaith x ⟨d, hCH⟩

theorem eq_one_of_finite_centralizer_of_pow_eq_one
    {x : WithConv (H →ₐ[k] k)}
    (hcentral : {h : WithConv (H →ₐ[k] k) | Commute h x}.Finite)
    {n : ℕ} (hn : (n : k) ≠ 0) (hpow : x ^ n = 1) : x = 1 := by
  have hss : TauCeti.HopfAlgebra.IsSemisimplePoint x :=
    isSemisimplePoint_of_pow_eq_one (K := k) x hn hpow
  have hu : TauCeti.HopfAlgebra.IsUnipotentPoint x :=
    isUnipotentPoint_of_finite_centralizer H hcentral
  exact hss.eq_one_of_isUnipotent hu

theorem not_finite_centralizer_of_cube_eq_one_of_ne_one
    (h3 : (3 : k) ≠ 0) {x : WithConv (H →ₐ[k] k)}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ {h : WithConv (H →ₐ[k] k) | Commute h x}.Finite := by
  intro hfin
  exact hx1 (eq_one_of_finite_centralizer_of_pow_eq_one H hfin h3 hx3)

end FiniteCentralizer

end CFSG.LieType.AlgebraicGroups
