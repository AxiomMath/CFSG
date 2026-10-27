module

public import CFSG.LieType.AlgebraicGroups.RegularCocharacter
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.RegularCocharacter

universe u

variable {k : Type u} [Field k]

theorem pointsMulEquiv_cocharacterPoint {n : ℕ} (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (v : kˣ) :
    TauCeti.SplitTorus.pointsMulEquiv
        (toConv (((TauCeti.MultiplicativeGroup.point (R := k) v).comp
          (additiveToLaurentBialg (k := k) : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k]
            LaurentPolynomial k)).comp (characterMapAlg (k := k) ψ₀))) =
      fun j => v ^ ψ₀ (Finsupp.single j 1) := by
  funext j
  apply Units.ext
  rw [TauCeti.SplitTorus.pointsMulEquiv_apply_coe, ofConv_toConv,
    point_cocharacterOfAddHom_single, toAdd_ofAdd, Units.val_zpow_eq_zpow_val]

theorem pointsHom_cocharacterOfAddHom_add {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (ψ₁ ψ₂ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t : kˣ) :
    TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom (ψ₁ + ψ₂) π) t =
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₁ π) t *
        TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₂ π) t := by
  rw [pointsHom_cocharacterOfAddHom, pointsHom_cocharacterOfAddHom,
    pointsHom_cocharacterOfAddHom, ← map_mul]
  congr 1
  apply (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)
    (σ := ULift.{u} (Fin n))).injective
  rw [map_mul, pointsMulEquiv_cocharacterPoint, pointsMulEquiv_cocharacterPoint,
    pointsMulEquiv_cocharacterPoint]
  funext j
  simp only [Pi.mul_apply, AddMonoidHom.add_apply, zpow_add]

theorem mapDomain_injective_of_surjective {M N : Type u} [CommRing M] [HopfAlgebra k M]
    [CommRing N] [HopfAlgebra k N] (π : M →ₐc[k] N) (hπ : Function.Surjective π) :
    Function.Injective (TauCeti.AlgHom.mapDomain (A := k) π) := by
  intro σ₁ σ₂ h
  apply WithConv.ofConv_injective
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  have := congrArg (fun g : WithConv (M →ₐ[k] k) => g.ofConv x) h
  simpa only [TauCeti.AlgHom.mapDomain_apply_apply] using this

theorem eq_of_forall_pointsHom_cocharacterOfAddHom_eq [IsAlgClosed k]
    {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (hπ : Function.Surjective π) {ψ₁ ψ₂ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ}
    (h : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₁ π) t =
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₂ π) t) : ψ₁ = ψ₂ := by
  classical
  have hval : ∀ (t : kˣ) (j : ULift.{u} (Fin n)),
      t ^ ψ₁ (Finsupp.single j 1) = t ^ ψ₂ (Finsupp.single j 1) := by
    intro t j
    have h1 := h t
    rw [pointsHom_cocharacterOfAddHom, pointsHom_cocharacterOfAddHom] at h1
    have h2 := congrArg (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k)
      (σ := ULift.{u} (Fin n))) (mapDomain_injective_of_surjective π hπ h1)
    rw [pointsMulEquiv_cocharacterPoint, pointsMulEquiv_cocharacterPoint] at h2
    exact congrFun h2 j
  refine Finsupp.addHom_ext fun j m => ?_
  rw [show (Finsupp.single j m : ULift.{u} (Fin n) →₀ ℤ) = m • Finsupp.single j 1 by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_zsmul, map_zsmul]
  congr 1
  let E : Finset ℤ := {ψ₁ (Finsupp.single j 1), ψ₂ (Finsupp.single j 1)}
  obtain ⟨t, ht⟩ := exists_unit_pow_separating (k := k) E
  by_contra hne
  apply ht _ (by simp [E]) _ (by simp [E]) hne
  have := congrArg (fun x : kˣ => (x : k)) (hval t j)
  simpa only [Units.val_zpow_eq_zpow_val] using this

theorem exists_eq_cocharacterOfAddHom [IsAlgClosed k] {M : Type u} [CommRing M]
    [HopfAlgebra k M] {n : ℕ}
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (hπ : Function.Surjective π) (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ h : M, π h = 0 → μ h = 0) :
    ∃ ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ, μ = cocharacterOfAddHom ψ₀ π := by
  classical
  let X := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let πa : M →ₐ[k] MonoidAlgebra k X := π
  have hsurj : Function.Surjective πa := hπ
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  have hk : ∀ a ∈ RingHom.ker πa, (μ : M →ₐ[k] LaurentPolynomial k) a = 0 := fun a ha =>
    hμ a (RingHom.mem_ker.mp ha)
  let μa : MonoidAlgebra k X →ₐ[k] LaurentPolynomial k :=
    (Ideal.Quotient.liftₐ (RingHom.ker πa) (μ : M →ₐ[k] LaurentPolynomial k) hk).comp
      e.symm.toAlgHom
  have hμa : ∀ h : M, μa (π h) = μ h := by
    intro h
    change Ideal.Quotient.liftₐ (RingHom.ker πa) (μ : M →ₐ[k] LaurentPolynomial k) hk
      (e.symm (πa h)) = μ h
    have he : e.symm (πa h) = Ideal.Quotient.mk (RingHom.ker πa) h := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    rw [he]
    rfl
  have hcounit : (Bialgebra.counitAlgHom k (LaurentPolynomial k)).comp μa =
      Bialgebra.counitAlgHom k (MonoidAlgebra k X) := by
    apply AlgHom.ext
    intro y
    obtain ⟨h, rfl⟩ := hπ y
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, hμa,
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  have hcomul : (Algebra.TensorProduct.map μa μa).comp (Bialgebra.comulAlgHom k _) =
      (Bialgebra.comulAlgHom k (LaurentPolynomial k)).comp μa := by
    apply AlgHom.ext
    intro y
    obtain ⟨h, rfl⟩ := hπ y
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, hμa, ← CoalgHomClass.map_comp_comul_apply π h,
      ← CoalgHomClass.map_comp_comul_apply μ h]
    induction Coalgebra.comul (R := k) h using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hμa]
    | add x y hx hy => simp only [map_add, hx, hy]
  let μb : MonoidAlgebra k X →ₐc[k] LaurentPolynomial k := BialgHom.ofAlgHom μa hcounit hcomul
  let F : MonoidAlgebra k X →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) :=
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp μb
  let φ : X →* Multiplicative ℤ := TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k F
  refine ⟨AddMonoidHom.toMultiplicative.symm φ, ?_⟩
  ext h
  have hF := TauCeti.MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHomPreimage k F
  have h1 : cocharacterOfAddHom (AddMonoidHom.toMultiplicative.symm φ) π h =
      additiveToLaurentBialg (MonoidAlgebra.mapDomainBialgHom k φ (π h)) := by
    simp only [cocharacterOfAddHom, BialgHom.comp_apply, Equiv.apply_symm_apply]
  rw [h1, hF]
  simp only [additiveToLaurentBialg, F, μb, BialgHom.comp_apply, BialgHom.ofAlgHom_apply, hμa,
    BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom, BialgEquiv.symm_apply_apply]

section Normalizer

variable [IsAlgClosed k] (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
  (I : TauCeti.HopfIdeal k M) {n : ℕ}
  (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))

theorem eq_zero_of_forall_pointsHom_mem (hker : ∀ h : M, π h = 0 ↔ h ∈ I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (h : M) (hh : π h = 0) : μ h = 0 := by
  apply laurentPolynomial_eq_zero_of_forall_point
  intro t
  have h1 := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp (hμ t) h
    ((hker h).mp hh)
  rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.AlgHom.mapDomain_apply_apply,
    ofConv_toConv] at h1
  exact h1

variable {M I π}

theorem exists_conj_cocharacterOfAddHom (hπ : Function.Surjective π)
    (hker : ∀ h : M, π h = 0 ↔ h ∈ I) {g : WithConv (M →ₐ[k] k)}
    (hg : g ∈ Subgroup.normalizer
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
        Set (WithConv (M →ₐ[k] k))))
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) :
    ∃ ψ' : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ, ∀ t : kˣ,
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ' π) t =
        g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t * g⁻¹ := by
  let μ : M →ₐc[k] LaurentPolynomial k := (cocharacterOfAddHom ψ π).comp
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
  have hg' : TauCeti.AlgHom.mapValue (H := M) (Algebra.ofId k k) g = g := by
    apply WithConv.ofConv_injective
    ext x
    simp
  have hμt : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t =
      g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t * g⁻¹ := by
    intro t
    rw [TauCeti.Cocharacter.pointsHom_apply, TauCeti.Cocharacter.pointsHom_apply,
      ← hg', ← TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv]
    rfl
  have hμT : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := by
    intro t
    rw [hμt]
    refine (Subgroup.mem_normalizer_iff.mp hg _).mp ?_
    rw [mem_quotientPointsSubgroup_iff_exists_mapDomain M I π hπ hker,
      pointsHom_cocharacterOfAddHom]
    exact ⟨_, rfl⟩
  obtain ⟨ψ', hψ'⟩ := exists_eq_cocharacterOfAddHom π hπ μ
    (eq_zero_of_forall_pointsHom_mem M I π hker μ hμT)
  exact ⟨ψ', fun t => by rw [← hψ', hμt]⟩

end Normalizer

theorem aeval_apply_of_apply_eq_smul {V : Type*} [AddCommMonoid V] [Module k V]
    (D : Module.End k V) {c : k} {w : V} (hw : D w = c • w) (p : Polynomial k) :
    Polynomial.aeval D p w = p.eval c • w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, mul_smul]
    congr 1
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hw, smul_smul, pow_succ]

theorem finite_setOf_conj_cocharacterOfAddHom [IsAlgClosed k]
    {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {I : TauCeti.HopfIdeal k M} {n : ℕ}
    {π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))}
    (hπ : Function.Surjective π) (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) :
    {ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ | ∃ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t =
        g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹}.Finite := by
  classical
  obtain ⟨E, hEfin, hEtop⟩ :=
    TauCeti.Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top
      (k := k) (C := M)
  let _ : Module.Finite k E := hEfin
  let X := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let _ : DecidableEq X := Classical.decEq X
  let A : X → Submodule k E := fun χ =>
    TauCeti.DiagonalizableGroup.weightSpace E (π : M →ₗc[k] MonoidAlgebra k X) χ
  have hA : DirectSum.IsInternal A :=
    TauCeti.DiagonalizableGroup.isInternal_weightSpace E (π : M →ₗc[k] MonoidAlgebra k X)
  have hSfin : Set.Finite {χ : X | A χ ≠ ⊥} :=
    TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot (V := E)
      (π := (π : M →ₗc[k] MonoidAlgebra k X))
  let S := {χ : X // A χ ≠ ⊥}
  let _ : Fintype S := hSfin.fintype
  let U : S → Submodule k E := fun χ => A χ.1
  let _ : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
  have hU : DirectSum.IsInternal U := (DirectSum.isInternal_ne_bot_iff (R := k) (A := A)).mpr hA
  have hact : ∀ (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t : kˣ) (χ : S) (v : E), v ∈ U χ →
      TauCeti.Comodule.basePointsRepresentation E
          (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t) v =
        ((t : k) ^ ψ (Multiplicative.toAdd χ.1)) • v := by
    intro ψ t χ v hv
    rw [pointsHom_cocharacterOfAddHom, TauCeti.AlgHom.mapDomain_apply]
    rw [basePointsRepresentation_comp_pi_eq_smul π _ (χ := χ.1) hv,
      point_cocharacterOfAddHom_single]
  have hinj : ∀ ψ₁ ψ₂ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ,
      (fun χ : S => ψ₁ (Multiplicative.toAdd χ.1)) =
        (fun χ : S => ψ₂ (Multiplicative.toAdd χ.1)) → ψ₁ = ψ₂ := by
    intro ψ₁ ψ₂ h
    apply eq_of_forall_pointsHom_cocharacterOfAddHom_eq π hπ
    intro t
    apply eq_of_basePointsRepresentation_eq M E hEtop
    apply CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.ext_U U hU
    intro χ v hv
    rw [hact ψ₁ t χ v hv, hact ψ₂ t χ v hv, congrFun h χ]
  let V : Finset ℤ := Finset.univ.image fun χ : S => ψ₀ (Multiplicative.toAdd χ.1)
  have hval : ∀ ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ, (∃ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t =
        g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹) →
      ∀ χ : S, ψ (Multiplicative.toAdd χ.1) ∈ V := by
    rintro ψ ⟨g, -, hψ⟩ χ
    set c := ψ (Multiplicative.toAdd χ.1)
    obtain ⟨t, ht⟩ := exists_unit_pow_separating (k := k) (insert c V)
    obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    let ρ := TauCeti.Comodule.basePointsRepresentation (R := k) (H := M) E
    let D := ρ (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t)
    let w := ρ g⁻¹ v
    have hw0 : w ≠ 0 := by
      intro hw
      apply hv0
      have h1 : ρ g w = v := by
        change ρ g (ρ g⁻¹ v) = v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hw, map_zero]
    have hDw : D w = ((t : k) ^ c) • w := by
      have h1 : ρ (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t) v =
          ((t : k) ^ c) • v := hact ψ t χ v hvU
      rw [hψ t] at h1
      change ρ (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t) (ρ g⁻¹ v) = _
      rw [← Module.End.mul_apply, ← map_mul]
      have h2 : TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹ =
          g⁻¹ * (g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹) := by
        group
      rw [h2, map_mul, Module.End.mul_apply, h1, map_smul]
    let p : Polynomial k := ∏ χ' : S,
      (Polynomial.X - Polynomial.C ((t : k) ^ ψ₀ (Multiplicative.toAdd χ'.1)))
    have hp : Polynomial.aeval D p = 0 := by
      apply CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.ext_U U hU
      intro χ' u hu
      rw [aeval_apply_of_apply_eq_smul D (hact ψ₀ t χ' u hu), LinearMap.zero_apply]
      rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ χ') (by simp), zero_smul]
    have hpw := aeval_apply_of_apply_eq_smul D hDw p
    rw [hp, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hpw
    rcases hpw with hpw | hpw
    · rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hpw
      obtain ⟨χ', -, hχ'⟩ := hpw
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hχ'
      have hmem : ψ₀ (Multiplicative.toAdd χ'.1) ∈ V :=
        Finset.mem_image.mpr ⟨χ', Finset.mem_univ _, rfl⟩
      by_contra hcV
      exact ht c (Finset.mem_insert_self c V) _ (Finset.mem_insert_of_mem hmem)
        (fun h => hcV (h ▸ hmem)) hχ'
    · exact absurd hpw hw0
  apply Set.Finite.of_finite_image (f := fun ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ =>
    fun χ : S => ψ (Multiplicative.toAdd χ.1))
  · refine (Set.Finite.pi (t := fun _ : S => (V : Set ℤ)) fun _ => V.finite_toSet).subset ?_
    rintro _ ⟨ψ, hψ, rfl⟩ χ -
    exact hval ψ hψ χ
  · exact fun ψ₁ _ ψ₂ _ h => hinj ψ₁ ψ₂ h

section OrbitSum
variable [IsAlgClosed k] (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
  (I : TauCeti.HopfIdeal k M) {n : ℕ}
  (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
  (hπ : Function.Surjective π) (hker : ∀ h : M, π h = 0 ↔ h ∈ I)

noncomputable def conjFunctional
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))))
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ :=
  Classical.choose (exists_conj_cocharacterOfAddHom hπ hker g.2 ψ)

theorem conjFunctional_on_points
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))))
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t : kˣ) :
    TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom (conjFunctional M I π hπ hker g ψ) π) t =
      (g : WithConv (M →ₐ[k] k)) * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t *
        (g : WithConv (M →ₐ[k] k))⁻¹ :=
  Classical.choose_spec (exists_conj_cocharacterOfAddHom hπ hker g.2 ψ) t

noncomputable def conjFunctionalAddHom
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k)))) :
    ((ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) →+ ((ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) where
  toFun := conjFunctional M I π hπ hker g
  map_zero' := by
    apply eq_of_forall_pointsHom_cocharacterOfAddHom_eq π hπ
    intro t
    rw [conjFunctional_on_points]
    have hz : TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom 0 π) t = 1 := by
      have hadd := pointsHom_cocharacterOfAddHom_add π 0 0 t
      rw [zero_add] at hadd
      exact mul_eq_left.mp hadd.symm
    rw [hz]
    group
  map_add' ψ χ := by
    apply eq_of_forall_pointsHom_cocharacterOfAddHom_eq π hπ
    intro t
    rw [conjFunctional_on_points,pointsHom_cocharacterOfAddHom_add,
      pointsHom_cocharacterOfAddHom_add,conjFunctional_on_points,conjFunctional_on_points]
    group
noncomputable def conjFunctionalPerm
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k)))) :
    Equiv.Perm ((ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) where
  toFun := conjFunctional M I π hπ hker g
  invFun := conjFunctional M I π hπ hker g⁻¹
  left_inv ψ := by
    apply eq_of_forall_pointsHom_cocharacterOfAddHom_eq π hπ
    intro t
    rw [conjFunctional_on_points,conjFunctional_on_points]
    simp only [Subgroup.coe_inv]
    group
  right_inv ψ := by
    apply eq_of_forall_pointsHom_cocharacterOfAddHom_eq π hπ
    intro t
    rw [conjFunctional_on_points,conjFunctional_on_points]
    simp only [Subgroup.coe_inv]
    group

@[expose] noncomputable def conjOrbit (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) :
    Set ((ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) :=
  {ψ | ∃ g ∈ Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))),
    ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t =
      g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹}

theorem conjOrbit_mem
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))))
    {ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ} (hψ : ψ ∈ conjOrbit M I π ψ₀) :
    conjFunctional M I π hπ hker g ψ ∈ conjOrbit M I π ψ₀ := by
  obtain ⟨a,ha,hact⟩ := hψ
  refine ⟨g*a,(Subgroup.normalizer _).mul_mem g.2 ha,?_⟩
  intro t
  rw [conjFunctional_on_points,hact]
  group

noncomputable def conjOrbitPerm
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k)))) :
    Equiv.Perm (conjOrbit M I π ψ₀) where
  toFun ψ := ⟨conjFunctional M I π hπ hker g ψ,conjOrbit_mem M I π hπ hker ψ₀ g ψ.2⟩
  invFun ψ := ⟨conjFunctional M I π hπ hker g⁻¹ ψ,conjOrbit_mem M I π hπ hker ψ₀ g⁻¹ ψ.2⟩
  left_inv ψ := Subtype.ext ((conjFunctionalPerm M I π hπ hker g).left_inv ψ)
  right_inv ψ := Subtype.ext ((conjFunctionalPerm M I π hπ hker g).right_inv ψ)

theorem conjOrbit_sum_fixed
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    (g : Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k)))) :
    letI : Fintype (conjOrbit M I π ψ₀) :=
      (finite_setOf_conj_cocharacterOfAddHom (I := I) hπ ψ₀).fintype
    conjFunctional M I π hπ hker g (∑ ψ : conjOrbit M I π ψ₀, ψ.1) =
      ∑ ψ : conjOrbit M I π ψ₀, ψ.1 := by
  let : Fintype (conjOrbit M I π ψ₀) :=
    (finite_setOf_conj_cocharacterOfAddHom (I := I) hπ ψ₀).fintype
  change conjFunctionalAddHom M I π hπ hker g _ = _
  rw [map_sum]
  exact Fintype.sum_equiv (conjOrbitPerm M I π hπ hker ψ₀ g) _ _ (fun _ => rfl)

omit [IsAlgClosed k] in
theorem pointsHom_cocharacterOfAddHom_list_sum
    (ps : List ((ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)) (t : kˣ) :
    TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ps.sum π) t =
      (ps.map fun ψ => TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t).prod := by
  induction ps with
  | nil =>
    simp only [List.sum_nil,List.map_nil,List.prod_nil]
    have hadd := pointsHom_cocharacterOfAddHom_add π 0 0 t
    rw [zero_add] at hadd
    exact mul_eq_left.mp hadd.symm
  | cons ψ ps ih =>
    rw [List.sum_cons,pointsHom_cocharacterOfAddHom_add,List.map_cons,List.prod_cons,ih]

include hπ hker in
theorem exists_list_normalizer_conjugate_prod_of_fixed_cocharacter
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    (hF : ∀ ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ,
      (∀ (g : WithConv (M →ₐ[k] k)),
        g ∈ Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
          (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))) →
        ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t * g⁻¹ =
          TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t) →
      ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t ∈
        (TauCeti.AlgHom.mapDomain (A := k)
          (CanonicalReductive.connectedCenterCoordinateMap M)).range) :
    ∃ ns : List (WithConv (M →ₐ[k] k)), ns ≠ [] ∧
      (∀ g ∈ ns, g ∈ Subgroup.normalizer (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
        (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k)))) ∧
      ∀ t : kˣ, (ns.map fun g =>
        g * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * g⁻¹).prod ∈
        (TauCeti.AlgHom.mapDomain (A := k)
          (CanonicalReductive.connectedCenterCoordinateMap M)).range := by
  let O := conjOrbit M I π ψ₀
  let : Fintype O := (finite_setOf_conj_cocharacterOfAddHom (I := I) hπ ψ₀).fintype
  have hself : ψ₀ ∈ O := ⟨1,(Subgroup.normalizer _).one_mem,fun t => by simp⟩
  have : Nonempty O := ⟨⟨ψ₀,hself⟩⟩
  let g : O → WithConv (M →ₐ[k] k) := fun ψ => Classical.choose ψ.2
  have hg (ψ : O) : g ψ ∈ Subgroup.normalizer
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
        (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))) := (Classical.choose_spec ψ.2).1
  have hact (ψ : O) (t : kˣ) :
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ.1 π) t =
        g ψ * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * (g ψ)⁻¹ :=
    (Classical.choose_spec ψ.2).2 t
  let es : List O := List.ofFn (Fintype.equivFin O).symm
  let ns := es.map g
  have hne : ns ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    change (es.map g).length = 0 at hlen
    rw [List.length_map] at hlen
    change (List.ofFn (Fintype.equivFin O).symm).length = 0 at hlen
    rw [List.length_ofFn] at hlen
    exact Fintype.card_ne_zero hlen
  refine ⟨ns,hne,?_,?_⟩
  · intro a ha
    obtain ⟨ψ,_,rfl⟩ := List.mem_map.mp ha
    exact hg ψ
  · intro t
    let Ψ := ∑ ψ : O, ψ.1
    have hfixed : ∀ a ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
          (CommAlgCat.of k k) : Set (WithConv (M →ₐ[k] k))),
        ∀ t : kˣ, a * TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom Ψ π) t * a⁻¹ =
          TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom Ψ π) t := by
      intro a ha t
      have hf := conjOrbit_sum_fixed M I π hπ hker ψ₀ ⟨a,ha⟩
      have hv := conjFunctional_on_points M I π hπ hker ⟨a,ha⟩ Ψ t
      rw [hf] at hv
      exact hv.symm
    have hcenter := hF Ψ hfixed t
    have hsum : (es.map Subtype.val).sum = Ψ := by
      dsimp only [es]
      rw [List.map_ofFn,List.sum_ofFn]
      exact Fintype.sum_equiv (Fintype.equivFin O).symm _ _ (fun _ => rfl)
    have hv := pointsHom_cocharacterOfAddHom_list_sum M π
      (es.map Subtype.val) t
    rw [hsum] at hv
    rw [hv] at hcenter
    change ((es.map g).map fun a => a *
      TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * a⁻¹).prod ∈ _
    simp only [List.map_map,Function.comp_def]
    have heq : (es.map fun ψ => g ψ *
        TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ₀ π) t * (g ψ)⁻¹).prod =
      ((es.map Subtype.val).map fun ψ =>
        TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t).prod := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro ψ _
      exact (hact ψ t).symm
    rw [heq]
    exact hcenter

end OrbitSum

end CFSG.LieType.AlgebraicGroups.RegularCocharacter
