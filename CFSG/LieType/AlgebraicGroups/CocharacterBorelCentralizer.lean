module

public import CFSG.LieType.AlgebraicGroups.DynamicUnipotentSmooth
public import CFSG.LieType.AlgebraicGroups.DynamicOpenCellDensity
public import CFSG.LieType.AlgebraicGroups.DynamicAdjointWeights
public import CFSG.LieType.AlgebraicGroups.OrbitConeLowestWeight
public import CFSG.LieType.AlgebraicGroups.RegularCocharacter
public import CFSG.LieType.AlgebraicGroups.TwistedBorelDensity
public import CFSG.Mathlib.RingTheory.MonoidAlgebraPointSeparation
public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import CFSG.LinearAlgebra.FiniteSpanningAction
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial
public import CFSG.Mathlib.FieldTheory.InfiniteUnitPowers
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.ChangeBasis
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
public import TauCeti.RingTheory.Polynomial.BinomialBasis
public import TauCeti.RingTheory.TensorProduct.PointSeparation

public noncomputable section

open WithConv TauCeti.Comodule
open CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar
open CFSG.LieType.AlgebraicGroups.OrbitConeLowestWeight

namespace CFSG.LieType.AlgebraicGroups.CocharacterBorel

universe u

section Weights

variable {k : Type u} [Field k] {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

theorem weightProj_basePointsRepresentation_pointsHom (l : M →ₐc[k] LaurentPolynomial k)
    (t : kˣ) (m : Multiplicative ℤ) (v : W) :
    weightProj W l m
        (basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k l t) v) =
      ((t : k) ^ Multiplicative.toAdd m) • weightProj W l m v := by
  classical
  obtain ⟨f, hfW, rfl⟩ := exists_finsupp_mem_weightSpace l v
  rw [weightProj_finsupp_sum l hfW, Finsupp.sum, map_sum, map_sum]
  simp_rw [basePointsRepresentation_pointsHom_of_mem_weightSpace l t (hfW _), map_smul]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [weightProj_of_mem_of_ne l (Ne.symm hb) (hfW b),
      smul_zero]) (fun h => absurd hm h), weightProj_of_mem l (hfW m)]
  · rw [Finset.sum_eq_zero fun b hb => by
      rw [weightProj_of_mem_of_ne l (by rintro rfl; exact hm hb) (hfW b), smul_zero]]
    rw [Finsupp.notMem_support_iff.mp hm, smul_zero]

theorem eigenWeight_le_weightSpace [Infinite k] (l : M →ₐc[k] LaurentPolynomial k) (m : ℤ) :
    eigenWeight W l m ≤ weightSpace W l (Multiplicative.ofAdd m) := by
  intro v hv
  have hzero : ∀ n : Multiplicative ℤ, n ≠ Multiplicative.ofAdd m → weightProj W l n v = 0 := by
    intro n hn
    have hne : Multiplicative.toAdd n - m ≠ 0 := by
      intro h
      apply hn
      rw [← ofAdd_toAdd n, show Multiplicative.toAdd n = m by omega]
    obtain ⟨t, ht⟩ := CFSG.MonoidAlgebra.exists_zpow_ne_one_of_infinite (k := k) hne
    have h1 := weightProj_basePointsRepresentation_pointsHom l t n v
    rw [hv t, map_smul] at h1
    have ht' : (t : k) ^ m ≠ (t : k) ^ Multiplicative.toAdd n := by
      intro h
      apply ht
      rw [← Units.val_eq_one, Units.val_zpow_eq_zpow_val, zpow_sub₀ t.ne_zero, ← h,
        div_self (zpow_ne_zero _ t.ne_zero)]
    have h3 : ((t : k) ^ m - (t : k) ^ Multiplicative.toAdd n) • weightProj W l n v = 0 := by
      rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ht')
  obtain ⟨f, hfW, hfsum⟩ := exists_finsupp_mem_weightSpace l v
  have hf : ∀ n, f n = weightProj W l n v := fun n => by
    rw [← weightProj_finsupp_sum l hfW n, hfsum]
  have hv' : v = f (Multiplicative.ofAdd m) := by
    calc v = f.sum fun _ x => x := hfsum.symm
      _ = f (Multiplicative.ofAdd m) := by
        rw [Finsupp.sum]
        refine Finset.sum_eq_single (Multiplicative.ofAdd m) (fun n _ hn => ?_) (fun h => ?_)
        · rw [hf, hzero n hn]
        · exact Finsupp.notMem_support_iff.mp h
  rw [hv']
  exact hfW _

theorem exists_mem_weightSpace_of_forall_pointsHom_mem_span [Infinite k]
    (l : M →ₐc[k] LaurentPolynomial k) {ω : W}
    (hω : ∀ t : kˣ, basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k l t) ω ∈
      k ∙ ω) :
    ∃ m : ℤ, ω ∈ weightSpace W l (Multiplicative.ofAdd m) := by
  classical
  by_cases h0 : ω = 0
  · exact ⟨0, h0 ▸ Submodule.zero_mem _⟩
  obtain ⟨f, hfW, hfsum⟩ := exists_finsupp_mem_weightSpace l ω
  obtain ⟨n, hn⟩ : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
    rintro rfl
    exact h0 (by rw [← hfsum, Finsupp.sum_zero_index])
  have hfn : weightProj W l n ω ≠ 0 := by
    rw [← hfsum, weightProj_finsupp_sum l hfW]
    exact Finsupp.mem_support_iff.mp hn
  refine ⟨Multiplicative.toAdd n, eigenWeight_le_weightSpace l _ fun t => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hω t)
  have h1 := weightProj_basePointsRepresentation_pointsHom l t n ω
  rw [← hc, map_smul] at h1
  have hct : c = (t : k) ^ Multiplicative.toAdd n := by
    have h3 : (c - (t : k) ^ Multiplicative.toAdd n) • weightProj W l n ω = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hfn)
  rw [← hc, hct]

end Weights

section Unipotent

variable {k : Type u} [Field k] [IsAlgClosed k] {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

omit [IsAlgClosed k] in
theorem point_conjugate_ofConv (l : M →ₐc[k] LaurentPolynomial k) (u : WithConv (M →ₐ[k] k))
    (t : kˣ) (h : M) :
    TauCeti.MultiplicativeGroup.point (R := k) t
        ((TauCeti.Cocharacter.conjugate k l u).ofConv h) =
      (TauCeti.Cocharacter.pointsHom k l t * u * (TauCeti.Cocharacter.pointsHom k l t)⁻¹).ofConv
        h := by
  have hunit : Units.map (TauCeti.MultiplicativeGroup.point (R := k) t).toMonoidHom
      (TauCeti.MultiplicativeGroup.genericUnit k) = t := by
    ext
    rw [Units.coe_map, TauCeti.MultiplicativeGroup.genericUnit_val]
    change TauCeti.MultiplicativeGroup.point (R := k) t (LaurentPolynomial.T 1) = (t : k)
    rw [TauCeti.MultiplicativeGroup.point_T, zpow_one]
  have hid : (TauCeti.MultiplicativeGroup.point (R := k) t).comp
      (IsScalarTower.toAlgHom k k (LaurentPolynomial k)) = AlgHom.id k k := by
    ext
  have hu : TauCeti.AlgHom.mapValue ((TauCeti.MultiplicativeGroup.point (R := k) t).comp
      (IsScalarTower.toAlgHom k k (LaurentPolynomial k))) u = u := by
    rw [hid, TauCeti.AlgHom.mapValue_apply, AlgHom.id_comp, toConv_ofConv]
  have key := TauCeti.Cocharacter.mapValue_conjugate (A := k) (l := l)
    (TauCeti.MultiplicativeGroup.point (R := k) t) u
  rw [hunit, hu] at key
  rw [← key, TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]

theorem weightProj_basePointsRepresentation_of_mem_unipotent (l : M →ₐc[k] LaurentPolynomial k)
    {m' : ℤ} {ω : W} (hω : ω ∈ weightSpace W l (Multiplicative.ofAdd m'))
    {u : WithConv (M →ₐ[k] k)} (hu : u ∈ TauCeti.Cocharacter.unipotent k l) {m : ℤ}
    (hm : m ≤ m') :
    weightProj W l (Multiplicative.ofAdd m) (basePointsRepresentation (H := M) W u ω) =
      if m = m' then ω else 0 := by
  obtain ⟨hpar, hlim⟩ := TauCeti.Cocharacter.mem_unipotent_iff.mp hu
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k _).mp fun θ => ?_
  rw [map_sub, sub_eq_zero]
  set φ := θ ∘ₗ weightProj W l (Multiplicative.ofAdd m)
  set F := TauCeti.Comodule.matrixCoefficient (C := M) φ ω
  set p := (TauCeti.Cocharacter.conjugate k l u).ofConv F
  set c := φ (basePointsRepresentation (H := M) W u ω)
  have hpt : ∀ t : kˣ, TauCeti.MultiplicativeGroup.point (R := k) t p = (t : k) ^ (m - m') * c := by
    intro t
    have ht0 : (t : k) ≠ 0 := t.ne_zero
    rw [point_conjugate_ofConv, TauCeti.Comodule.apply_matrixCoefficient, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, ← map_inv,
      basePointsRepresentation_pointsHom_of_mem_weightSpace l t⁻¹ hω, map_smul, map_smul,
      map_smul]
    simp only [φ, LinearMap.comp_apply, weightProj_basePointsRepresentation_pointsHom, map_smul,
      toAdd_ofAdd, smul_eq_mul, c, Units.val_inv_eq_inv_val]
    rw [zpow_sub₀ ht0, inv_zpow, div_eq_mul_inv]
    ring
  have hp : p = LaurentPolynomial.C c * LaurentPolynomial.T (m - m') := by
    rw [← sub_eq_zero]
    apply RegularCocharacter.laurentPolynomial_eq_zero_of_forall_point
    intro t
    rw [map_sub, map_mul, TauCeti.MultiplicativeGroup.point_C, TauCeti.MultiplicativeGroup.point_T,
      hpt, Units.val_zpow_eq_zpow_val, Algebra.algebraMap_self, RingHom.id_apply, mul_comm,
      sub_self]
  have hcoeff : ∀ n : ℤ, p.coeff n = if n = m - m' then c else 0 := by
    intro n
    rw [hp, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hn : n = m - m'
    · rw [if_pos hn, if_pos hn.symm]
    · rw [if_neg hn, if_neg (Ne.symm hn)]
  by_cases hmm : m = m'
  · subst hmm
    rw [if_pos rfl]
    have h0 := CFSG.ThirdParty.TauCeti.Cocharacter.limit_apply_eq_coeff_conjugate l ⟨u, hpar⟩ F
    rw [hlim, hcoeff, if_pos (by omega)] at h0
    change c = θ ω
    rw [← h0, show (1 : WithConv (M →ₐ[k] k)) = 1 from rfl,
      TauCeti.Comodule.apply_matrixCoefficient, map_one, Module.End.one_apply]
    simp only [φ, LinearMap.comp_apply, weightProj_of_mem l hω]
  · rw [if_neg hmm, map_zero]
    have h0 := (CFSG.ThirdParty.TauCeti.Cocharacter.mem_parabolic_iff_forall_coeff_conjugate_eq_zero
      l).mp hpar F (m - m') (by omega)
    rw [hcoeff, if_pos rfl] at h0
    exact h0

end Unipotent

section Density

open TauCeti
open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem eq_zero_of_forall_unipotent_mul_of_sup
    (M : FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M] [IsDomain M]
    (l : M →ₐc[k] LaurentPolynomial k) (B : HopfIdeal k M)
    (hB : smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient M B).obj)
    (hsup : ∀ d : Derivation k M (Bialgebra.CounitAlgebra k M k),
      ∃ d₁ ∈ (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).lieSubalgebra
        (B := k), ∃ d₂ ∈ B.lieSubalgebra (B := k), d = d₁ + d₂)
    {p : M} (hp : ∀ u ∈ Cocharacter.unipotent k l,
      ∀ b ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k),
        (u * b).ofConv p = 0) : p = 0 := by
  set IU := CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l
  have hUsm := DynamicUnipotent.smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
    (M := M) l
  let A := (M ⧸ IU.toIdeal) ⊗[k] (M ⧸ B.toIdeal)
  let : Algebra.Smooth k A :=
    (smoothCommHopfAlgProperty_iff (_root_.CommHopfAlgCat.of k A)).mp
      (smoothCommHopfAlgProperty.tensorProduct (FiniteTypeCommHopfAlgCat.quotient M IU).obj
        (FiniteTypeCommHopfAlgCat.quotient M B).obj hUsm hB)
  let : IsRegularRing A := TauCeti.IsRegularRing.of_smooth (R := k)
  let : IsReduced A := TauCeti.isReduced_of_smooth k A
  let L := TauCeti.Bialgebra.TensorProduct.includeLeft
    (R := k) (H₁ := M ⧸ IU.toIdeal) (H₂ := M ⧸ B.toIdeal)
  let R := TauCeti.Bialgebra.TensorProduct.includeRight
    (R := k) (H₁ := M ⧸ IU.toIdeal) (H₂ := M ⧸ B.toIdeal)
  let πU := _root_.Bialgebra.Quotient.mkBialgHom (R := k) IU.toIdeal
  let πB := _root_.Bialgebra.Quotient.mkBialgHom (R := k) B.toIdeal
  let f₁ := (L.comp πU).toAlgHom
  let f₂ := (R.comp πB).toAlgHom
  have hf₁ := _root_.BialgHom.counitAlgHom_comp (L.comp πU)
  have hf₂ := _root_.BialgHom.counitAlgHom_comp (R.comp πB)
  let f : M →ₐ[k] A := (toConv f₁ * toConv f₂).ofConv
  have hf := Derivation.counit_comp_convMul f₁ f₂ hf₁ hf₂
  have hs : Function.Surjective (Derivation.compCounit f hf) := by
    intro d
    obtain ⟨d₁, hd₁, d₂, hd₂B, rfl⟩ := hsup d
    obtain ⟨q₁, hq₁⟩ : d₁ ∈ LinearMap.range (IU.quotientLieHom (B := k)).toLinearMap := by
      rw [range_quotientLieHom_eq_lieSubalgebra]
      exact hd₁
    obtain ⟨q₂, hq₂⟩ : d₂ ∈ LinearMap.range (B.quotientLieHom (B := k)).toLinearMap := by
      rw [range_quotientLieHom_eq_lieSubalgebra]
      exact hd₂B
    let E := Derivation.tensorProductLieEquiv (R := k) (H₁ := M ⧸ IU.toIdeal)
      (H₂ := M ⧸ B.toIdeal) (B := k)
    let D := E.toLinearEquiv.symm (q₁, q₂)
    have hE : (derivationComp (B := k) L D, derivationComp (B := k) R D) = (q₁, q₂) := by
      rw [← Derivation.tensorProductLieEquiv_apply]
      exact E.toLinearEquiv.apply_symm_apply (q₁, q₂)
    have hL : derivationComp (B := k) L D = q₁ := congrArg Prod.fst hE
    have hR : derivationComp (B := k) R D = q₂ := congrArg Prod.snd hE
    refine ⟨D, ?_⟩
    rw [Derivation.compCounit_convMul f₁ f₂ hf₁ hf₂, LinearMap.add_apply,
      Derivation.compCounit_toAlgHom (L.comp πU) D, Derivation.compCounit_toAlgHom (R.comp πB) D,
      derivationComp_comp, derivationComp_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      hL, hR, ← hq₁, ← hq₂]
    simp only [LieHom.coe_toLinearMap]
    rw [IU.quotientLieHom_apply q₁, B.quotientLieHom_apply q₂]
  apply eq_zero_of_compCounit_surjective_of_forall_apply_eq_zero f hf hs
  intro y
  let u : WithConv (M →ₐ[k] k) := toConv (y.comp f₁)
  let b : WithConv (M →ₐ[k] k) := toConv (y.comp f₂)
  have hu : u ∈ Cocharacter.unipotent k l := by
    rw [← CFSG.ThirdParty.TauCeti.BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal l,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change y (L (πU x)) = 0
    rw [show πU x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hx),
      map_zero, map_zero]
  have hb : b ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    change y (R (πB x)) = 0
    rw [show πB x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hx),
      map_zero, map_zero]
  have hyf : toConv (y.comp f) = u * b := by
    have h1 : TauCeti.AlgHom.mapValue y (toConv f₁ * toConv f₂) = toConv (y.comp f) := by
      rw [TauCeti.AlgHom.mapValue_apply]
    rw [← h1, map_mul, TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapValue_apply,
      ofConv_toConv, ofConv_toConv]
  have h := congrArg (fun g : WithConv (M →ₐ[k] k) => g.ofConv p) hyf
  simp only [AlgHom.comp_apply] at h
  rw [h]
  exact hp u hu b hb

end Density

section Centralizer

open TauCeti

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem mem_quotientPointsSubgroup_of_commute_pointsHom_of_sup
    (M : FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M] [IsDomain M]
    (B : HopfIdeal k M)
    (hB : smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient M B).obj)
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W] {ω : W}
    (hstab : ∀ g : WithConv (M →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) ↔
        basePointsRepresentation (H := M) W g ω ∈ k ∙ ω)
    (l : M →ₐc[k] LaurentPolynomial k) {m' : ℤ}
    (hω : ω ∈ weightSpace W l (Multiplicative.ofAdd m'))
    (hsup : ∀ d : Derivation k M (Bialgebra.CounitAlgebra k M k),
      ∃ d₁ ∈ (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).lieSubalgebra
        (B := k), ∃ d₂ ∈ B.lieSubalgebra (B := k), d = d₁ + d₂)
    {z : WithConv (M →ₐ[k] k)} (hz : ∀ t : kˣ, Commute z (Cocharacter.pointsHom k l t)) :
    z ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) := by
  classical
  have hvanish : ∀ θ : Module.Dual k W, ∀ m : ℤ, m ≤ m' →
      (∀ u ∈ Cocharacter.unipotent k l,
        θ (weightProj W l (Multiplicative.ofAdd m) (basePointsRepresentation (H := M) W u ω)) = 0) →
      ∀ g : WithConv (M →ₐ[k] k),
        θ (weightProj W l (Multiplicative.ofAdd m) (basePointsRepresentation (H := M) W g ω)) = 0 := by
    intro θ m _ hu g
    have hF : TauCeti.Comodule.matrixCoefficient (C := M)
        (θ ∘ₗ weightProj W l (Multiplicative.ofAdd m)) ω = 0 := by
      apply eq_zero_of_forall_unipotent_mul_of_sup M l B hB hsup
      intro u hu' b hb
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hstab b).mp hb)
      rw [TauCeti.Comodule.apply_matrixCoefficient, map_mul, Module.End.mul_apply, ← hc, map_smul,
        LinearMap.comp_apply, map_smul, map_smul, hu u hu', smul_zero]
    have h := congrArg (fun F => g.ofConv F) hF
    simp only [TauCeti.Comodule.apply_matrixCoefficient, LinearMap.comp_apply, map_zero] at h
    exact h
  have hbelow : ∀ g : WithConv (M →ₐ[k] k), ∀ m : ℤ, m < m' →
      weightProj W l (Multiplicative.ofAdd m) (basePointsRepresentation (H := M) W g ω) = 0 := by
    intro g m hm
    refine (Module.forall_dual_apply_eq_zero_iff k _).mp fun θ => ?_
    refine hvanish θ m hm.le (fun u hu => ?_) g
    rw [weightProj_basePointsRepresentation_of_mem_unipotent l hω hu hm.le, if_neg hm.ne,
      map_zero]
  have hat : ∀ g : WithConv (M →ₐ[k] k),
      weightProj W l (Multiplicative.ofAdd m') (basePointsRepresentation (H := M) W g ω) ∈
        k ∙ ω := by
    intro g
    by_contra hnot
    obtain ⟨θ, hθ, hθω⟩ := Submodule.exists_le_ker_of_notMem hnot
    apply hθ
    refine hvanish θ m' le_rfl (fun u hu => ?_) g
    rw [weightProj_basePointsRepresentation_of_mem_unipotent l hω hu le_rfl, if_pos rfl]
    exact LinearMap.mem_ker.mp (hθω (Submodule.mem_span_singleton_self ω))
  set v := basePointsRepresentation (H := M) W z ω
  have hvW : v ∈ weightSpace W l (Multiplicative.ofAdd m') :=
    eigenWeight_le_weightSpace l m' (basePointsRepresentation_mem_eigenWeight
      (fun t => (hz t).symm) (weightSpace_le_eigenWeight l _ hω))
  have hv : v = weightProj W l (Multiplicative.ofAdd m') v := (weightProj_of_mem l hvW).symm
  rw [hstab]
  change v ∈ k ∙ ω
  rw [hv]
  exact hat z

theorem mem_quotientPointsSubgroup_of_commute_pointsHom_of_nonpos
    (M : FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M] [IsDomain M]
    (B : HopfIdeal k M)
    (hB : smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient M B).obj)
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W] {ω : W}
    (hstab : ∀ g : WithConv (M →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) ↔
        basePointsRepresentation (H := M) W g ω ∈ k ∙ ω)
    (l : M →ₐc[k] LaurentPolynomial k) {m' : ℤ}
    (hω : ω ∈ weightSpace W l (Multiplicative.ofAdd m'))
    (hle : ∀ n : ℤ, n ≤ 0 → ∀ x ∈ Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n),
      Derivation.cotangentDualLieEquiv (R := k) (H := M) x ∈ B.lieSubalgebra (B := k))
    {z : WithConv (M →ₐ[k] k)} (hz : ∀ t : kˣ, Commute z (Cocharacter.pointsHom k l t)) :
    z ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) :=
  mem_quotientPointsSubgroup_of_commute_pointsHom_of_sup M B hB hstab l hω
    (DynamicAdjointWeights.exists_add_mem_lieSubalgebra_unipotent_of_nonpos l B hle) hz

end Centralizer

end CFSG.LieType.AlgebraicGroups.CocharacterBorel
