module

public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension
public import CFSG.LieType.AlgebraicGroups.DynamicUnipotentDerived
public import Mathlib.Algebra.Module.Submodule.Union

public noncomputable section

open WithConv
open TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.RegularCocharacter

universe u

variable {k : Type u} [Field k]

theorem eq_of_basePointsRepresentation_eq
    (M : Type u) [CommRing M] [HopfAlgebra k M]
    (E : TauCeti.Subcomodule k M M)
    (hE : TauCeti.Comodule.matrixCoefficientSubalgebra (R := k) (C := M) (M := E) = ⊤)
    {g g' : WithConv (M →ₐ[k] k)}
    (h : TauCeti.Comodule.basePointsRepresentation (H := M) E g =
      TauCeti.Comodule.basePointsRepresentation (H := M) E g') : g = g' := by
  apply WithConv.ofConv_injective
  refine AlgHom.ext_of_adjoin_eq_top (s := TauCeti.Comodule.matrixCoefficientSet
    (R := k) (C := M) (M := E)) ?_ ?_
  · rw [← TauCeti.Comodule.matrixCoefficientSubalgebra_def]
    exact hE
  · intro c hc
    obtain ⟨φ, e, rfl⟩ := (TauCeti.Comodule.mem_matrixCoefficientSet_iff
      (R := k) (C := M) (M := E) c).mp hc
    rw [TauCeti.Comodule.apply_matrixCoefficient, TauCeti.Comodule.apply_matrixCoefficient]
    exact congrArg φ (DFunLike.congr_fun h e)

theorem basePointsRepresentation_comp_pi_eq_smul
    {C : Type u} [CommRing C] [HopfAlgebra k C]
    {V : Type u} [AddCommMonoid V] [Module k V] [TauCeti.Comodule k C V]
    {X : Type u} [Monoid X]
    (π : C →ₐc[k] MonoidAlgebra k X) (σ : MonoidAlgebra k X →ₐ[k] k)
    {χ : X} {v : V}
    (hv : v ∈ TauCeti.DiagonalizableGroup.weightSpace V (π : C →ₗc[k] MonoidAlgebra k X) χ) :
    TauCeti.Comodule.basePointsRepresentation (H := C) V (toConv (σ.comp (π : C →ₐ[k] MonoidAlgebra k X))) v =
      σ (MonoidAlgebra.single χ 1) • v := by
  rw [TauCeti.Comodule.basePointsRepresentation_apply]
  change TensorProduct.lid k V
    (TauCeti.Comodule.endOfPoint V (σ.comp (π : C →ₐ[k] MonoidAlgebra k X)) (1 ⊗ₜ[k] v)) =
      σ (MonoidAlgebra.single χ 1) • v
  rw [TauCeti.DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace (V := V) (π := π) (f := σ)
    (a := 1) hv]
  simp

@[expose] noncomputable def additiveToLaurentBialg :
    MonoidAlgebra k (Multiplicative ℤ) →ₐc[k] LaurentPolynomial k :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm.toBialgHom

@[expose] noncomputable def characterMapAlg {n : ℕ}
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) :
    MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k]
      MonoidAlgebra k (Multiplicative ℤ) :=
  (MonoidAlgebra.mapDomainBialgHom k (AddMonoidHom.toMultiplicative ψ₀)).toAlgHom

@[expose] noncomputable def cocharacterOfAddHom {n : ℕ}
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    {M : Type u} [CommRing M] [HopfAlgebra k M]
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) :
    M →ₐc[k] LaurentPolynomial k :=
  additiveToLaurentBialg.comp ((MonoidAlgebra.mapDomainBialgHom k
    (AddMonoidHom.toMultiplicative ψ₀)).comp π)

theorem point_cocharacterOfAddHom_single {n : ℕ}
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t : kˣ)
    (χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) :
    ((MultiplicativeGroup.point (R := k) t).comp
        (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] LaurentPolynomial k)).comp
      (characterMapAlg (k := k) ψ₀)
      (MonoidAlgebra.single χ 1) = (t : k) ^ (ψ₀ (Multiplicative.toAdd χ)) := by
  have hsymm : (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
      (MonoidAlgebra.single (Multiplicative.ofAdd (ψ₀ (Multiplicative.toAdd χ))) 1) =
        (AddMonoidAlgebra.single (ψ₀ (Multiplicative.toAdd χ)) 1 : AddMonoidAlgebra k ℤ) := by
    rw [← AddMonoidAlgebra.toMultiplicativeBialgEquiv_single
      (R := k) (A := k) (M := ℤ) (ψ₀ (Multiplicative.toAdd χ)) 1,
      BialgEquiv.symm_apply_apply]
  have hT : (AddMonoidAlgebra.single (ψ₀ (Multiplicative.toAdd χ)) (1 : k) :
      LaurentPolynomial k) = LaurentPolynomial.T (ψ₀ (Multiplicative.toAdd χ)) := by
    rw [LaurentPolynomial.single_eq_C_mul_T]
    simp
  change (MultiplicativeGroup.point (R := k) t)
    ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
      ((characterMapAlg (k := k) ψ₀) (MonoidAlgebra.single χ 1))) = _
  rw [characterMapAlg, BialgHom.coe_toAlgHom, MonoidAlgebra.mapDomainBialgHom_single,
    AddMonoidHom.toMultiplicative_apply_apply, hsymm, hT, MultiplicativeGroup.point_T]
  simp

section Separating

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

theorem exists_addHom_separating (S : Finset (σ →₀ ℤ)) :
    ∃ ψ : (σ →₀ ℤ) →+ ℤ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ψ a ≠ ψ b := by
  classical
  let dot : (σ →₀ ℤ) → (σ → ℚ) →ₗ[ℚ] ℚ := fun d =>
    ∑ i : σ, (d i : ℚ) • (LinearMap.proj i : (σ → ℚ) →ₗ[ℚ] ℚ)
  have hdot : ∀ (d : σ →₀ ℤ) (w : σ → ℚ),
      dot d w = ∑ i : σ, (d i : ℚ) * w i := by
    intro d w
    simp [dot, Finset.sum_apply, mul_comm]
  let D : Finset (σ →₀ ℤ) :=
    ((S.product S).filter (fun p => p.1 ≠ p.2)).image (fun p => p.1 - p.2)
  have hD : ∀ d ∈ D, d ≠ 0 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hp
    exact sub_ne_zero.mpr hne
  have hK : ∀ d : {d // d ∈ D}, LinearMap.ker (dot d.1) ≠ ⊤ := by
    intro d htop
    have hzero : ∀ w : σ → ℚ, dot d.1 w = 0 := by
      intro w
      have hw : w ∈ LinearMap.ker (dot d.1) := by rw [htop]; exact Submodule.mem_top
      simpa using hw
    have hex : ∃ i : σ, d.1 i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hD d.1 d.2 (Finsupp.ext h)
    obtain ⟨i, hi⟩ := hex
    have hsingle := hzero (Pi.single i (1 : ℚ))
    rw [hdot] at hsingle
    rw [Finset.sum_eq_single i] at hsingle
    · simp only [Pi.single_eq_same, mul_one] at hsingle
      exact hi (by exact_mod_cast hsingle)
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, mul_comm]
    · simp
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun d : {d // d ∈ D} => LinearMap.ker (dot d.1)) hK
  let N : ℕ := ∏ i : σ, (w i).den
  have hN : N ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Rat.den_ne_zero (w i)
  let w' : σ → ℤ := fun i => ((N / (w i).den : ℕ) : ℤ) * (w i).num
  let w'Q : σ → ℚ := fun i => (w' i : ℚ)
  have hw' : ∀ i, w'Q i = (N : ℚ) * w i := by
    intro i
    have hdvd : (w i).den ∣ N :=
      Finset.dvd_prod_of_mem (fun j => (w j).den) (Finset.mem_univ i)
    have hNi : ((N / (w i).den : ℕ) : ℚ) = (N : ℚ) / ((w i).den : ℚ) :=
      Nat.cast_div_charZero hdvd
    have hnum : ((w i).num : ℚ) = ((w i).den : ℚ) * w i := by
      rw [← Rat.den_mul_eq_num (w i)]
    have hden : ((w i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_ne_zero (w i))
    have hcoe : w'Q i = ((N / (w i).den : ℕ) : ℚ) * ((w i).num : ℚ) := by
      change ((((N / (w i).den : ℕ) : ℤ) * (w i).num : ℤ) : ℚ) =
        ((N / (w i).den : ℕ) : ℚ) * ((w i).num : ℚ)
      rw [Int.cast_mul, Int.cast_natCast]
    calc w'Q i = ((N / (w i).den : ℕ) : ℚ) * ((w i).num : ℚ) := hcoe
      _ = ((N : ℚ) / ((w i).den : ℚ)) * (((w i).den : ℚ) * w i) := by rw [hNi, hnum]
      _ = (((N : ℚ) / ((w i).den : ℚ)) * ((w i).den : ℚ)) * w i := by ring
      _ = (N : ℚ) * w i := by rw [div_mul_cancel₀ _ hden]
  refine ⟨(Finsupp.linearCombination ℤ w').toAddMonoidHom, ?_⟩
  intro a ha b hb hab
  have hd : a - b ∈ D := by
    refine Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hab⟩
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨ha, hb⟩
  have hnot : w ∉ LinearMap.ker (dot (a - b)) := hw ⟨a - b, hd⟩
  have hne : dot (a - b) w ≠ 0 := by
    intro h
    exact hnot (by rw [LinearMap.mem_ker]; exact h)
  have hscale : dot (a - b) w'Q = (N : ℚ) * dot (a - b) w := by
    rw [hdot, hdot, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hw' i]
    ring
  intro hψ
  have hzero : (Finsupp.linearCombination ℤ w') (a - b) = 0 := by
    rw [map_sub]
    rw [show (Finsupp.linearCombination ℤ w') a = (Finsupp.linearCombination ℤ w') b
      from hψ, sub_self]
  have hcast : (((Finsupp.linearCombination ℤ w') (a - b) : ℤ) : ℚ) =
      dot (a - b) w'Q := by
    have hleft : ((((a - b).support).sum (fun i => (a - b) i • w' i) : ℤ) : ℚ) =
        ((a - b).support).sum (fun i => ((a - b) i : ℚ) * w'Q i) := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [zsmul_eq_mul]
      simp only [Int.cast_mul]
      rfl
    rw [Finsupp.linearCombination_apply, Finsupp.sum, hdot, hleft]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [Finsupp.mem_support_iff] at hi
      simp [not_not.mp hi])
  have hz : (N : ℚ) * dot (a - b) w = 0 := by
    rw [← hscale, ← hcast, hzero]
    norm_num
  exact hne ((mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hN))

theorem exists_unit_pow_separating [IsAlgClosed k] (E : Finset ℤ) :
    ∃ t : kˣ, ∀ a ∈ E, ∀ b ∈ E, a ≠ b → (t : k) ^ a ≠ (t : k) ^ b := by
  classical
  let D : Finset ℤ :=
    ((E.product E).filter (fun p => p.1 ≠ p.2)).image (fun p => p.1 - p.2)
  have hD : ∀ d ∈ D, d ≠ 0 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hp
    exact sub_ne_zero.mpr hne
  let bad : Set k := ({0} : Set k) ∪ ⋃ d ∈ (D : Set ℤ), {x : k | x ^ (d.natAbs : ℤ) = 1}
  have hbad : bad.Finite := by
    refine Set.Finite.union (Set.finite_singleton 0) ?_
    refine Set.Finite.biUnion D.finite_toSet ?_
    intro d hd
    have hdne : d ≠ 0 := hD d (by simpa using hd)
    have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hdne
    have hp : (Polynomial.X ^ d.natAbs - (1 : Polynomial k)) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (n := d.natAbs) hpos (1 : k)
    refine (Polynomial.finite_setOf_isRoot hp).subset ?_
    intro x hx
    have hx' : x ^ d.natAbs = 1 := by
      rw [← zpow_natCast]
      simpa [Int.natCast_natAbs] using hx
    simp [Polynomial.IsRoot, hx']
  obtain ⟨t, ht⟩ := hbad.exists_notMem
  have ht0 : t ≠ 0 := by
    intro h0
    apply ht
    simp [bad, h0]
  refine ⟨Units.mk0 t ht0, ?_⟩
  intro a ha b hb hab hpow
  have hpow' : t ^ a = t ^ b := by simpa using hpow
  have hsub : t ^ (a - b) = 1 := by
    rw [zpow_sub₀ ht0, hpow', div_self (zpow_ne_zero b ht0)]
  have hnat : t ^ (((a - b).natAbs : ℤ)) = 1 := by
    rcases Int.natAbs_eq (a - b) with h | h
    · rwa [h] at hsub
    · rw [h, zpow_neg, inv_eq_one] at hsub
      exact hsub
  have hd : a - b ∈ D := by
    refine Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hab⟩
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨ha, hb⟩
  apply ht
  refine Set.mem_union_right _ ?_
  exact Set.mem_biUnion (x := a - b) (by simpa using hd) (by simpa using hnat)

end Separating

theorem mapValue_point_constPoint {M : Type u} [CommRing M] [HopfAlgebra k M]
    (t : kˣ) (g : WithConv (M →ₐ[k] k)) :
    AlgHom.mapValue (MultiplicativeGroup.point (R := k) t)
        (TauCeti.Cocharacter.constPoint k g) = g := by
  rw [TauCeti.Cocharacter.constPoint_apply, TauCeti.AlgHom.mapValue_apply]
  have h : (MultiplicativeGroup.point (R := k) t).comp
      (IsScalarTower.toAlgHom k k (LaurentPolynomial k)) = AlgHom.id k k := by
    apply AlgHom.ext
    intro a
    simp
  rw [← AlgHom.comp_assoc, h, AlgHom.id_comp, WithConv.toConv_ofConv]

theorem laurentPolynomial_eq_zero_of_forall_point [IsAlgClosed k] (f : LaurentPolynomial k)
    (hf : ∀ t : kˣ, TauCeti.MultiplicativeGroup.point (R := k) t f = 0) : f = 0 := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have hp0 : p = 0 := by
    apply CFSG.LieType.AlgebraicGroups.CanonicalReductive.polynomial_eq_zero_of_eval_eq_zero_of_ne
    intro t ht
    have h1 := AlgHom.congr_fun
      (CFSG.LieType.AlgebraicGroups.CanonicalReductive.point_comp_toLaurent (Units.mk0 t ht)) p
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply,
      Polynomial.toLaurentAlg_apply, hp, map_mul, hf, zero_mul,
      CFSG.LieType.AlgebraicGroups.CanonicalReductive.aeval_eq_eval] at h1
    exact h1.symm
  rw [hp0, map_zero] at hp
  have hT : LaurentPolynomial.T (n : ℤ) * LaurentPolynomial.T (-(n : ℤ)) =
      (1 : LaurentPolynomial k) := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  calc f = f * (LaurentPolynomial.T (n : ℤ) * LaurentPolynomial.T (-(n : ℤ))) := by
        rw [hT, mul_one]
    _ = 0 := by rw [← mul_assoc, ← hp, zero_mul]

theorem mem_levi_iff_forall_pointsHom_commute [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (l : M →ₐc[k] LaurentPolynomial k)
    {g : WithConv (M →ₐ[k] k)} :
    g ∈ TauCeti.Cocharacter.levi k l ↔
      ∀ t : kˣ, Commute (TauCeti.Cocharacter.pointsHom k l t) g := by
  constructor
  · intro hg t
    have h := congrArg (AlgHom.mapValue (MultiplicativeGroup.point (R := k) t))
      (TauCeti.Cocharacter.mem_levi_iff.mp hg)
    rw [CFSG.LieType.AlgebraicGroups.CanonicalReductive.mapValue_point_conjugate M l t g,
      mapValue_point_constPoint] at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  · intro hcomm
    apply TauCeti.Cocharacter.mem_levi_iff.mpr
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    apply sub_eq_zero.mp
    apply laurentPolynomial_eq_zero_of_forall_point
    intro t
    rw [map_sub]
    apply sub_eq_zero.mpr
    have h : AlgHom.mapValue (MultiplicativeGroup.point (R := k) t)
        (TauCeti.Cocharacter.conjugate k l g) =
        AlgHom.mapValue (MultiplicativeGroup.point (R := k) t)
          (TauCeti.Cocharacter.constPoint k g) := by
      rw [CFSG.LieType.AlgebraicGroups.CanonicalReductive.mapValue_point_conjugate M l t g,
        mapValue_point_constPoint, (hcomm t).eq, mul_inv_cancel_right]
    simpa only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply] using
      congrArg (fun p : WithConv (M →ₐ[k] k) => p.ofConv a) h

theorem centralizer_le_levi_of_pointsHom_mem [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (l : M →ₐc[k] LaurentPolynomial k)
    (T : Subgroup (WithConv (M →ₐ[k] k)))
    (hl : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k l t ∈ T) :
    Subgroup.centralizer (T : Set (WithConv (M →ₐ[k] k))) ≤ TauCeti.Cocharacter.levi k l := by
  intro g hg
  apply (mem_levi_iff_forall_pointsHom_commute M l).mpr
  intro t
  exact Subgroup.mem_centralizer_iff.mp hg _ (hl t)

section SplitCoordinates

theorem exists_splitCoordinates [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k M)
    (hI : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)) :
    ∃ (n : ℕ) (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))),
      Function.Surjective π ∧ ∀ h : M, π h = 0 ↔ h ∈ I := by
  have hsplit : TauCeti.splitTorusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I) :=
    (TauCeti.torusCommHopfAlgProperty_iff_split k _).mp hI
  rw [TauCeti.splitTorusCommHopfAlgProperty_iff] at hsplit
  obtain ⟨n, ⟨e⟩⟩ := hsplit
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M I
  let X := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let πq : M →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M I)
  let einv : Q →ₐc[k] MonoidAlgebra k X := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  let eh : MonoidAlgebra k X →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  have hcomp : eh.comp einv = BialgHom.id k Q := by
    rw [← TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.inv_hom_id,
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_id]
  have hcomp' : einv.comp eh = BialgHom.id k (MonoidAlgebra k X) := by
    rw [← TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.hom_inv_id,
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_id]
  have hπq : ∀ h : M, πq h = Ideal.Quotient.mk I.toIdeal h := fun h => rfl
  refine ⟨n, einv.comp πq, ?_, ?_⟩
  · intro y
    obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective (I := I.toIdeal) (eh y)
    refine ⟨h, ?_⟩
    rw [BialgHom.comp_apply, hπq, hh]
    exact DFunLike.congr_fun hcomp' y
  · intro h
    rw [BialgHom.comp_apply, hπq, ← TauCeti.HopfIdeal.mem_toIdeal,
      ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h0
      have := DFunLike.congr_fun hcomp (Ideal.Quotient.mk I.toIdeal h)
      rw [BialgHom.comp_apply, h0, map_zero] at this
      exact this.symm
    · intro h0
      rw [h0, map_zero]

theorem mem_quotientPointsSubgroup_iff_exists_mapDomain
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k M) {n : ℕ}
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (hπ : Function.Surjective π) (hker : ∀ h : M, π h = 0 ↔ h ∈ I)
    (s : WithConv (M →ₐ[k] k)) :
    s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) ↔
      ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = s := by
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hs
    let πa : M →ₐ[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) := π
    have hsurj : Function.Surjective πa := hπ
    let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    have hk : ∀ a ∈ RingHom.ker πa, s.ofConv a = 0 := fun a ha =>
      hs a ((hker a).mp (RingHom.mem_ker.mp ha))
    let σ := (Ideal.Quotient.liftₐ (RingHom.ker πa) s.ofConv hk).comp e.symm.toAlgHom
    refine ⟨toConv σ, ?_⟩
    apply WithConv.ofConv_injective
    ext a
    rw [TauCeti.AlgHom.mapDomain_apply_apply]
    change Ideal.Quotient.liftₐ (RingHom.ker πa) s.ofConv hk (e.symm (πa a)) = s.ofConv a
    have he : e.symm (πa a) = Ideal.Quotient.mk (RingHom.ker πa) a := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    rw [he]
    rfl
  · rintro ⟨σ, rfl⟩ h hh
    rw [TauCeti.AlgHom.mapDomain_apply_apply, (hker h).mpr hh, map_zero]

theorem pointsHom_cocharacterOfAddHom {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) (t : kˣ) :
    TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t =
      TauCeti.AlgHom.mapDomain (A := k) π (toConv (((MultiplicativeGroup.point (R := k) t).comp
        (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k]
          LaurentPolynomial k)).comp (characterMapAlg (k := k) ψ₀))) := by
  rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply,
    TauCeti.AlgHom.mapDomain_apply]
  congr 1

theorem commute_of_mem_range_mapDomain {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    {x y : WithConv (M →ₐ[k] k)} (hx : ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = x)
    (hy : ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = y) : Commute x y := by
  obtain ⟨σ₁, rfl⟩ := hx
  obtain ⟨σ₂, rfl⟩ := hy
  have h : σ₁ * σ₂ = σ₂ * σ₁ := TauCeti.SplitTorus.pointsMulEquiv.injective (by
    rw [map_mul, map_mul, mul_comm])
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, h]

theorem pointsMulEquiv_cocharacterOfAddHom_apply {n : ℕ} (i : ULift.{u} (Fin n)) (v : kˣ) :
    TauCeti.SplitTorus.pointsMulEquiv
        (toConv (((MultiplicativeGroup.point (R := k) v).comp
          (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k]
            LaurentPolynomial k)).comp (characterMapAlg (k := k) (Finsupp.applyAddHom i)))) =
      Pi.mulSingle i v := by
  funext j
  apply Units.ext
  rw [TauCeti.SplitTorus.pointsMulEquiv_apply_coe, ofConv_toConv,
    point_cocharacterOfAddHom_single, toAdd_ofAdd, Finsupp.applyAddHom_apply,
    Finsupp.single_apply]
  by_cases hji : j = i
  · subst hji
    simp
  · rw [if_neg hji, Pi.mulSingle_eq_of_ne hji]
    simp

theorem mapDomain_mem_of_pointsHom_mem {M : Type u} [CommRing M] [HopfAlgebra k M]
    {n : ℕ} (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (H : Subgroup (WithConv (M →ₐ[k] k)))
    (hH : ∀ (i : ULift.{u} (Fin n)) (t : kˣ),
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom (Finsupp.applyAddHom i) π) t ∈ H)
    (σ : WithConv (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k)) :
    TauCeti.AlgHom.mapDomain (A := k) π σ ∈ H := by
  classical
  let F : (ULift.{u} (Fin n) → kˣ) →* WithConv (M →ₐ[k] k) :=
    (TauCeti.AlgHom.mapDomain (A := k) π).comp
      (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)).symm.toMonoidHom
  let H' : Subgroup (ULift.{u} (Fin n) → kˣ) := H.comap F
  have hsingle : ∀ (i : ULift.{u} (Fin n)) (v : kˣ), Pi.mulSingle i v ∈ H' := by
    intro i v
    change F (Pi.mulSingle i v) ∈ H
    have h := hH i v
    rw [TauCeti.Cocharacter.pointsHom_apply] at h
    have he : (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)).symm (Pi.mulSingle i v) =
        toConv (((MultiplicativeGroup.point (R := k) v).comp
          (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k]
            LaurentPolynomial k)).comp (characterMapAlg (k := k) (Finsupp.applyAddHom i))) := by
      rw [MulEquiv.symm_apply_eq, pointsMulEquiv_cocharacterOfAddHom_apply]
    change TauCeti.AlgHom.mapDomain (A := k) π
      ((TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)).symm (Pi.mulSingle i v)) ∈ H
    rw [he]
    exact h
  have hc : TauCeti.SplitTorus.pointsMulEquiv σ ∈ H' := by
    rw [← Finset.univ_prod_mulSingle (TauCeti.SplitTorus.pointsMulEquiv σ)]
    exact Subgroup.prod_mem _ fun i _ => hsingle i _
  have hσ : F (TauCeti.SplitTorus.pointsMulEquiv σ) = TauCeti.AlgHom.mapDomain (A := k) π σ := by
    change TauCeti.AlgHom.mapDomain (A := k) π
      ((TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
        (TauCeti.SplitTorus.pointsMulEquiv σ)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [← hσ]
  exact hc

end SplitCoordinates

theorem exists_cocharacter_pointsHom_mem_levi_le_centralizer [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k M)
    (hI : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)) :
    ∃ l : M →ₐc[k] LaurentPolynomial k,
      (∀ t : kˣ, TauCeti.Cocharacter.pointsHom k l t ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) ∧
      TauCeti.Cocharacter.levi k l ≤ Subgroup.centralizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))) := by
  classical
  have hsplit : TauCeti.splitTorusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I) :=
    (TauCeti.torusCommHopfAlgProperty_iff_split k _).mp hI
  rw [TauCeti.splitTorusCommHopfAlgProperty_iff] at hsplit
  obtain ⟨n, ⟨e⟩⟩ := hsplit
  let X := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M I
  let πq : M →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M I)
  let einv : Q →ₐc[k] MonoidAlgebra k X := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  let eh : MonoidAlgebra k X →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  let π : M →ₐc[k] MonoidAlgebra k X := einv.comp πq
  obtain ⟨E, hEfin, hEtop⟩ :=
    TauCeti.Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top
      (k := k) (C := M)
  let : Module.Finite k E := hEfin
  let : DecidableEq X := Classical.decEq X
  let A : X → Submodule k E := fun χ =>
    TauCeti.DiagonalizableGroup.weightSpace E (π : M →ₗc[k] MonoidAlgebra k X) χ
  have hSfin : Set.Finite {χ : X | A χ ≠ ⊥} :=
    TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot (V := E)
      (π := (π : M →ₗc[k] MonoidAlgebra k X))
  let S := {χ : X // A χ ≠ ⊥}
  let : Fintype S := hSfin.fintype
  let U : S → Submodule k E := fun χ => A χ.1
  have hA : DirectSum.IsInternal A :=
    TauCeti.DiagonalizableGroup.isInternal_weightSpace E (π : M →ₗc[k] MonoidAlgebra k X)
  have hU : DirectSum.IsInternal U := by
    let _ : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
    exact (DirectSum.isInternal_ne_bot_iff (R := k) (A := A)).mpr hA
  obtain ⟨ψ₀, hψ₀⟩ := exists_addHom_separating (σ := ULift.{u} (Fin n))
    (hSfin.toFinset.image Multiplicative.toAdd)
  let Eim : Finset ℤ := hSfin.toFinset.image (fun χ => ψ₀ (Multiplicative.toAdd χ))
  obtain ⟨t, ht⟩ := exists_unit_pow_separating (k := k) Eim
  let σt : MonoidAlgebra k X →ₐ[k] k :=
    ((MultiplicativeGroup.point (R := k) t).comp
      (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k]
        LaurentPolynomial k)).comp (characterMapAlg (k := k) ψ₀)
  let l : M →ₐc[k] LaurentPolynomial k := cocharacterOfAddHom ψ₀ π
  have hpoint : ∀ v : kˣ, TauCeti.Cocharacter.pointsHom k l v ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := by
    intro v
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro a ha
    have hq0 : πq a = 0 := by
      change Ideal.Quotient.mk I.toIdeal a = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (TauCeti.HopfIdeal.mem_toIdeal.mpr ha)
    have hπ0 : π a = 0 := by
      change einv (πq a) = 0
      rw [hq0, map_zero]
    have hl0 : l a = 0 := by
      simp only [l, cocharacterOfAddHom, BialgHom.comp_apply, hπ0, map_zero]
    rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply]
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
    rw [hl0, map_zero]
  refine ⟨l, hpoint, ?_⟩
  have hfactor : ∀ s : WithConv (M →ₐ[k] k),
      s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) →
      ∃ σ : MonoidAlgebra k X →ₐ[k] k,
        s = toConv (σ.comp (π : M →ₐ[k] MonoidAlgebra k X)) := by
    intro s hs
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hs
    obtain ⟨q, hq⟩ := (TauCeti.CommHopfAlgCat.mem_range_quotientPointsHom_iff M.obj I
      (CommAlgCat.of k k) s).mpr hs
    have hcomp : eh.comp einv = BialgHom.id k Q := by
      rw [← TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.inv_hom_id,
        TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_id]
    have heval : ∀ x : M, eh (einv (πq x)) = πq x := by
      intro x
      have h := congrArg (fun f : Q →ₐc[k] Q => f (πq x)) hcomp
      simpa using h
    refine ⟨q.ofConv.comp eh, ?_⟩
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    rw [WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply]
    have hπx : (π : M →ₐ[k] MonoidAlgebra k X) x = einv (πq x) := rfl
    rw [hπx]
    simp only [BialgHom.coe_toAlgHom]
    rw [heval x]
    have hqx : q.ofConv (πq x) = s.ofConv x := by
      have h := congrArg (fun f : WithConv (M →ₐ[k] k) => f.ofConv x) hq
      rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply] at h
      rw [← h]
      congr 1
    exact hqx.symm
  have hσt : TauCeti.Cocharacter.pointsHom k l t =
      toConv (σt.comp (π : M →ₐ[k] MonoidAlgebra k X)) := by
    rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply]
    congr 1
  have hσt_single : ∀ χ : S, σt (MonoidAlgebra.single χ.1 1) =
      (t : k) ^ (ψ₀ (Multiplicative.toAdd χ.1)) := by
    intro χ
    exact point_cocharacterOfAddHom_single ψ₀ t χ.1
  let c : S → k := fun χ => σt (MonoidAlgebra.single χ.1 1)
  have hc_inj : Function.Injective c := by
    intro χ χ' h
    by_contra hne
    have hχ : χ.1 ∈ hSfin.toFinset := by simp
    have hχ' : χ'.1 ∈ hSfin.toFinset := by simp
    have hpow : (t : k) ^ (ψ₀ (Multiplicative.toAdd χ.1)) =
        (t : k) ^ (ψ₀ (Multiplicative.toAdd χ'.1)) := by
      rw [← hσt_single χ, ← hσt_single χ']
      exact h
    have hψne : ψ₀ (Multiplicative.toAdd χ.1) ≠
        ψ₀ (Multiplicative.toAdd χ'.1) := by
      intro hψ
      apply hne
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      by_contra htoAdd
      exact (hψ₀ (Multiplicative.toAdd χ.1)
        (Finset.mem_image.mpr ⟨χ.1, hχ, rfl⟩)
        (Multiplicative.toAdd χ'.1)
        (Finset.mem_image.mpr ⟨χ'.1, hχ', rfl⟩) htoAdd) hψ
    exact ht _ (Finset.mem_image.mpr ⟨χ.1, hχ, rfl⟩) _
      (Finset.mem_image.mpr ⟨χ'.1, hχ', rfl⟩) hψne hpow
  have hT : ∀ χ : S, ∀ v ∈ U χ,
      TauCeti.Comodule.basePointsRepresentation E
        (TauCeti.Cocharacter.pointsHom k l t) v = c χ • v := by
    intro χ v hv
    have hv' : v ∈ A χ.1 := hv
    rw [hσt]
    exact basePointsRepresentation_comp_pi_eq_smul π σt hv'
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨σ, hσ⟩ := hfactor s hs
  have hcomm : g * TauCeti.Cocharacter.pointsHom k l t =
      TauCeti.Cocharacter.pointsHom k l t * g :=
    ((mem_levi_iff_forall_pointsHom_commute M l).mp hg t).eq.symm
  have hρcomm : TauCeti.Comodule.basePointsRepresentation E g *
      TauCeti.Comodule.basePointsRepresentation E
        (TauCeti.Cocharacter.pointsHom k l t) =
      TauCeti.Comodule.basePointsRepresentation E
        (TauCeti.Cocharacter.pointsHom k l t) *
        TauCeti.Comodule.basePointsRepresentation E g := by
    rw [← map_mul, ← map_mul, hcomm]
  let _ : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
  have hpres : ∀ χ : S, ∀ v ∈ U χ,
      TauCeti.Comodule.basePointsRepresentation E g v ∈ U χ :=
    fun χ v hv => CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.maps_to
      hc_inj hU hT hρcomm χ v hv
  have hsact : ∀ χ : S, ∀ v ∈ U χ,
      TauCeti.Comodule.basePointsRepresentation E s v =
        σ (MonoidAlgebra.single χ.1 1) • v := by
    intro χ v hv
    have hv' : v ∈ A χ.1 := hv
    rw [hσ]
    exact basePointsRepresentation_comp_pi_eq_smul π σ hv'
  have heq : TauCeti.Comodule.basePointsRepresentation E g *
      TauCeti.Comodule.basePointsRepresentation E s =
      TauCeti.Comodule.basePointsRepresentation E s *
        TauCeti.Comodule.basePointsRepresentation E g := by
    apply CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.ext_U U hU
    intro χ v hv
    change TauCeti.Comodule.basePointsRepresentation E g
        (TauCeti.Comodule.basePointsRepresentation E s v) =
      TauCeti.Comodule.basePointsRepresentation E s
        (TauCeti.Comodule.basePointsRepresentation E g v)
    rw [hsact χ v hv, map_smul, hsact χ (TauCeti.Comodule.basePointsRepresentation E g v)
      (hpres χ v hv)]
  have heq' : TauCeti.Comodule.basePointsRepresentation E (g * s) =
      TauCeti.Comodule.basePointsRepresentation E (s * g) := by
    rw [map_mul, map_mul]
    exact heq
  exact (eq_of_basePointsRepresentation_eq M E hEtop heq').symm

theorem exists_cocharacter_levi_eq_centralizer [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k M)
    (hI : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)) :
    ∃ l : M →ₐc[k] LaurentPolynomial k,
      (∀ t : kˣ, TauCeti.Cocharacter.pointsHom k l t ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) ∧
      TauCeti.Cocharacter.levi k l = Subgroup.centralizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))) := by
  obtain ⟨l, hl, hC⟩ := exists_cocharacter_pointsHom_mem_levi_le_centralizer M I hI
  exact ⟨l, hl, le_antisymm hC (centralizer_le_levi_of_pointsHom_mem M l _ hl)⟩

theorem exists_cocharacter_levi_le_centralizer [IsAlgClosed k]
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k M)
    (hI : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I)) :
    ∃ l : M →ₐc[k] LaurentPolynomial k,
      TauCeti.Cocharacter.levi k l ≤ Subgroup.centralizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))) := by
  obtain ⟨l, -, hC⟩ := exists_cocharacter_levi_eq_centralizer M I hI
  exact ⟨l, hC.le⟩

end CFSG.LieType.AlgebraicGroups.RegularCocharacter
