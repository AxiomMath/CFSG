module

public import CFSG.LieType.AlgebraicGroups.AdjointLieWeights
public import CFSG.LieType.AlgebraicGroups.RegularCocharacter
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import CFSG.ThirdParty.TauCeti.DynamicRepresentability

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.DynamicAdjointWeights

open TauCeti WithConv

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

theorem point_conjugationAlgHom (l : H →ₐc[k] LaurentPolynomial k) (t : kˣ) (h : H) :
    MultiplicativeGroup.point (R := H) (A := H) (Units.map (Algebra.ofId k H).toMonoidHom t)
        (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h) =
      HopfAlgebra.pointConjugationAlgHom (Cocharacter.pointsHom k l t) h := by
  let ψ : LaurentPolynomial H →ₐ[k] H :=
    (MultiplicativeGroup.point (R := H) (A := H)
      (Units.map (Algebra.ofId k H).toMonoidHom t)).restrictScalars k
  have hunit : Units.map ψ.toMonoidHom (MultiplicativeGroup.genericUnit H) =
      Units.map (Algebra.ofId k H).toMonoidHom t := by
    ext
    rw [Units.coe_map, MultiplicativeGroup.genericUnit_val]
    change MultiplicativeGroup.point (R := H) (A := H)
      (Units.map (Algebra.ofId k H).toMonoidHom t) (LaurentPolynomial.T 1) = _
    rw [MultiplicativeGroup.point_T, zpow_one]
  have hid : ψ.comp (IsScalarTower.toAlgHom k H (LaurentPolynomial H)) = AlgHom.id k H := by
    ext a
    change MultiplicativeGroup.point (R := H) (A := H)
      (Units.map (Algebra.ofId k H).toMonoidHom t) (algebraMap H (LaurentPolynomial H) a) = a
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have key := Cocharacter.mapValue_conjugate (A := H) (l := l) ψ (toConv (AlgHom.id k H))
  rw [hunit, hid, TauCeti.AlgHom.mapValue_id, MonoidHom.id_apply,
    ← Cocharacter.mapValue_pointsHom, ← HopfAlgebra.toConv_pointConjugationAlgHom] at key
  have hconj : (Cocharacter.conjugate H l (toConv (AlgHom.id k H))).ofConv h =
      CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h := by
    ext n
    rw [CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugate]
    rfl
  have h2 := congrArg (fun g : WithConv (H →ₐ[k] H) => g.ofConv h) key
  simp only [TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at h2
  rw [← hconj]
  exact h2

private theorem point_map (Φ : H →ₗ[k] k) (t : kˣ) (q : LaurentPolynomial H) :
    MultiplicativeGroup.point (R := k) (A := k) t (AddMonoidAlgebra.map Φ.toAddMonoidHom q) =
      Φ (MultiplicativeGroup.point (R := H) (A := H)
        (Units.map (Algebra.ofId k H).toMonoidHom t) q) := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [AddMonoidAlgebra.map_add, map_add, map_add, map_add, hp, hq]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.map_single,
      LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.single_eq_C_mul_T, map_mul, map_mul,
      MultiplicativeGroup.point_C, MultiplicativeGroup.point_C, MultiplicativeGroup.point_T,
      MultiplicativeGroup.point_T, Algebra.algebraMap_self, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, ← map_zpow, Units.coe_map]
    change Φ a * ((t ^ n : kˣ) : k) = Φ (a * algebraMap k H ((t ^ n : kˣ) : k))
    rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem unipotentDefiningHopfIdeal_toIdeal_eq_span (l : H →ₐc[k] LaurentPolynomial k) :
    (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).toIdeal =
      Ideal.span ({x | ∃ h : H, ∃ n : ℤ, n < 0 ∧
          (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff n = x} ∪
        {x | ∃ h : H, (CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff 0 -
          algebraMap k H (Coalgebra.counit h) = x}) := by
  rw [CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal_toIdeal,
    CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal_toIdeal, Ideal.span_union]

section Weights

variable [IsAlgClosed k] [Module.Finite k (Bialgebra.CotangentSpace k H)]

theorem cotangentDualLieEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace
    (l : H →ₐc[k] LaurentPolynomial k) {m : ℤ}
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : x ∈ Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
      (Multiplicative.ofAdd m)) (h : H) (n : ℤ) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) x
        ((CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h).coeff n) =
      if n = m then Derivation.cotangentDualLieEquiv (R := k) (H := H) x h else 0 := by
  set d := Derivation.cotangentDualLieEquiv (R := k) (H := H) x
  set e := Bialgebra.CounitAlgebra.algEquivSelf k H k
  set p := CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom l h
  let Φ : H →ₗ[k] k := e.toLinearMap ∘ₗ (d : H →ₗ[k] Bialgebra.CounitAlgebra k H k)
  have hact : ∀ t : kˣ, d (HopfAlgebra.pointConjugationAlgHom (Cocharacter.pointsHom k l t) h) =
      ((t : k) ^ m) • d h := by
    intro t
    let f : _root_.MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k :=
      (MultiplicativeGroup.point (R := k) (A := k) t).comp
        (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm.toAlgEquiv.toAlgHom
    have hpt : Cocharacter.pointsHom k l t =
        toConv (f.comp ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
          l).toAlgHom) := by
      rw [Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply]
      congr 1
      ext a
      simp [f]
    have hf : f (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1) = (t : k) ^ m := by
      have he : (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
          (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1) = LaurentPolynomial.T m := by
        rw [← AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := k) m (1 : k),
          BialgEquiv.symm_apply_apply, LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
      show MultiplicativeGroup.point (R := k) (A := k) t
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
          (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1)) = _
      rw [he, MultiplicativeGroup.point_T, Units.val_zpow_eq_zpow_val]
    have h1 := derivationComp_pointConjugation_of_mem_adjointWeightSpace _ f hx
    rw [← hpt, hf] at h1
    have h2 := congrArg (fun D : Derivation k H (Bialgebra.CounitAlgebra k H k) => D h) h1
    simp only [derivationComp_apply, Derivation.smul_apply] at h2
    rw [← h2, ← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom, BialgEquiv.toBialgHom_eq_coe]
  have hpoly : AddMonoidAlgebra.map Φ.toAddMonoidHom p =
      LaurentPolynomial.C (Φ h) * LaurentPolynomial.T m := by
    rw [← sub_eq_zero]
    apply RegularCocharacter.laurentPolynomial_eq_zero_of_forall_point
    intro t
    rw [map_sub, point_map, point_conjugationAlgHom, map_mul, MultiplicativeGroup.point_C,
      MultiplicativeGroup.point_T, Algebra.algebraMap_self, RingHom.id_apply,
      Units.val_zpow_eq_zpow_val]
    simp only [Φ, LinearMap.comp_apply, Derivation.coeFn_coe, hact t, map_smul, smul_eq_mul,
      AlgEquiv.toLinearMap_apply]
    ring
  have hcoeff := congrArg (fun q : LaurentPolynomial k => q.coeff n) hpoly
  simp only [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single_apply] at hcoeff
  apply e.injective
  rw [apply_ite e, map_zero]
  simp only [Φ, LinearMap.comp_apply, Derivation.coeFn_coe, AlgEquiv.toLinearMap_apply,
    LinearMap.toAddMonoidHom_coe] at hcoeff
  rw [hcoeff]
  by_cases hn : n = m
  · rw [if_pos hn.symm, if_pos hn]
  · rw [if_neg (Ne.symm hn), if_neg hn]

theorem cotangentDualLieEquiv_mem_lieSubalgebra_unipotent_of_pos
    (l : H →ₐc[k] LaurentPolynomial k) {m : ℤ} (hm : 0 < m)
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : x ∈ Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
      (Multiplicative.ofAdd m)) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈
      (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).lieSubalgebra (B := k) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (unipotentDefiningHopfIdeal_toIdeal_eq_span l)]
  rintro _ (⟨h, n, hn, rfl⟩ | ⟨h, rfl⟩)
  · rw [cotangentDualLieEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace l hx,
      if_neg (by omega)]
  · rw [map_sub, cotangentDualLieEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace l hx,
      if_neg (by omega), Derivation.map_algebraMap, sub_zero]

theorem exists_add_mem_lieSubalgebra_unipotent_of_nonpos (l : H →ₐc[k] LaurentPolynomial k)
    (B : HopfIdeal k H)
    (hle : ∀ n : ℤ, n ≤ 0 → ∀ x ∈ Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n),
      Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ B.lieSubalgebra (B := k))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∃ d₁ ∈ (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).lieSubalgebra (B := k),
    ∃ d₂ ∈ B.lieSubalgebra (B := k), d = d₁ + d₂ := by
  let π := (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l
  let E := (Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLinearEquiv
  let N := ((CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l).lieSubalgebra
    (B := k)).toSubmodule ⊔ (B.lieSubalgebra (B := k)).toSubmodule
  have htop : ⨆ α, Derivation.adjointWeightSpace π α = ⊤ := by
    let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
    exact (Derivation.isInternal_adjointWeightSpace π).submodule_iSup_eq_top
  have hle' : ⨆ α, Derivation.adjointWeightSpace π α ≤ N.comap E.toLinearMap := by
    refine iSup_le fun α x hx => ?_
    rw [Submodule.mem_comap]
    rw [← ofAdd_toAdd α] at hx
    by_cases hα : 0 < Multiplicative.toAdd α
    · exact Submodule.mem_sup_left
        (cotangentDualLieEquiv_mem_lieSubalgebra_unipotent_of_pos l hα hx)
    · exact Submodule.mem_sup_right (hle _ (not_lt.mp hα) x hx)
  have hd : E.symm d ∈ N.comap E.toLinearMap := by
    rw [htop] at hle'
    exact hle' Submodule.mem_top
  rw [Submodule.mem_comap, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at hd
  obtain ⟨d₁, hd₁, d₂, hd₂, hsum⟩ := Submodule.mem_sup.mp hd
  exact ⟨d₁, hd₁, d₂, hd₂, hsum.symm⟩

end Weights

end CFSG.LieType.AlgebraicGroups.DynamicAdjointWeights
