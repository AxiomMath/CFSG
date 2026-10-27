module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBConjugate
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem a6Safe_of_map_eq {P S : Type*} [Group P] [Group S] (π : P →* S) {Q : Subgroup P}
    {R : Subgroup S} (hQ : IsQuasisimple Q) (hQR : Q.map π = R)
    (hker : (π.comp Q.subtype).ker ≤ center Q) (h : A6Safe Q) : A6Safe R := by
  let σ : Q →* R := (π.comp Q.subtype).codRestrict R fun x => by
    rw [← hQR]
    exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hσ : Function.Surjective σ := by
    rintro ⟨y, hy⟩
    rw [← hQR] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hkerσ : σ.ker ≤ center Q := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx)
  exact a6Safe_of_cover hQ σ hσ hkerσ h

theorem a6_inner_psu
    {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (A : primeFormUnitary h (idGram K n)) (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2) :
    A6CentreForm (fixedSubgroup (primeFormConjHom h (idGram K n) A)) := by
  intro L hL
  show A6Safe L
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hA1 : primeFormConjHom h (idGram K n) A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, hcN, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn
    (A := A * A) (by rw [map_mul, hA2])
  have hAA : (A : GL (Fin n) K) * A = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_mul]
    exact hc
  set B := idForm h n with hBdef
  let T : sesqUnitaryGroup B :=
    ⟨Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K),
      (toLin_mem_sesqUnitaryGroup_iff _).mpr A.2⟩
  have hTcoe : ((T : LinearMap.GeneralLinearGroup K (Fin n → K))) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) := rfl
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    refine ⟨(c : K), hcN, ?_⟩
    have e1 : ((T * T : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) := by
      rw [← hAA, map_mul]
      rfl
    rw [e1, OddInner.toLin_scalar]
  have hTne : (QuotientGroup.mk T : sesqProjUnitary h B) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c', -, hc'⟩ := h1
    apply hA1
    have hcomm : ∀ g : GL (Fin n) K, (A : GL (Fin n) K) * g = g * A := by
      intro g
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ← hTcoe, hc', smul_mul_assoc, one_mul, mul_smul_comm,
        mul_one]
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [primeFormConjHom_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
      rw [hcomm, mul_inv_cancel_right]
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2 := by
    refine orderOf_eq_prime ?_ hTne
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hTT
  have hK' : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      center (gramSU h (idGram K n)) := by
    rw [QuotientGroup.ker_mk']
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  have ha : ∀ x, primeFormConjSU h (idGram K n) A (primeFormConjSU h (idGram K n) A x) = x := by
    intro x
    apply Subtype.ext
    change (A : GL (Fin n) K) * ((A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹) *
      (A : GL (Fin n) K)⁻¹ = x
    calc (A : GL (Fin n) K) * ((A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹) *
          (A : GL (Fin n) K)⁻¹ =
        ((A : GL (Fin n) K) * A) * x * ((A : GL (Fin n) K) * A)⁻¹ := by group
      _ = x := by rw [hAA, ← (commute_scalar c _).eq, mul_inv_cancel_right]
  have hα : ∀ s, primeFormConjHom h (idGram K n) A (primeFormConjHom h (idGram K n) A s) = s :=
    fun s => by rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    (QuotientGroup.mk'_surjective _) hK' ha hα
    (fun x => (primeFormConjHom_mk h (idGram K n) A x).symm)
  set R := L.map (fixedSubgroup (primeFormConjHom h (idGram K n) A)).subtype
  have hR : Assembly.IsComponentOf R (fixedSubgroup (primeFormConjHom h (idGram K n) A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (primeFormConjHom h (idGram K n) A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQR, -, hkerQ, hkerZ, -⟩ := hlift R hR
  let φS : gramSU h (idGram K n) →* sesqUnitaryGroup B :=
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
        (gramSU h (idGram K n)).subtype).codRestrict _ fun g =>
      (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp g.2).1
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (congrArg Subtype.val hxy))
  have hcommφ : ∀ g : GL (Fin n) K, (A : GL (Fin n) K) * g = g * A ↔
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) * Matrix.GeneralLinearGroup.toLin g =
        Matrix.GeneralLinearGroup.toLin g * Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) :=
    fun g => by rw [← map_mul, ← map_mul, Matrix.GeneralLinearGroup.toLin.injective.eq_iff]
  have hfixA : ∀ x : gramSU h (idGram K n), x ∈ fixedSubgroup (primeFormConjSU h (idGram K n) A) ↔
      (A : GL (Fin n) K) * x = x * A := by
    intro x
    change primeFormConjSU h (idGram K n) A x = x ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹ = x ↔ _
    rw [mul_inv_eq_iff_eq_mul]
  have hmap : (fixedSubgroup (primeFormConjSU h (idGram K n) A)).map φS =
      Subgroup.centralizer {T} ⊓ CatalogueBUnitaryB.unitarySpecial B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact ((hcommφ x).mp ((hfixA x).mp hx)).symm
      · rw [Subgroup.mem_subgroupOf]
        exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) x).mpr x.2
    · intro hy
      obtain ⟨hyM, hyS⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_subgroupOf] at hyS
      set g := Matrix.GeneralLinearGroup.toLin.symm (y : LinearMap.GeneralLinearGroup K
        (Fin n → K)) with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = (y : LinearMap.GeneralLinearGroup K
          (Fin n → K)) := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K n) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hyS
      refine ⟨⟨g, hg⟩, (hfixA _).mpr ((hcommφ g).mpr ?_), Subtype.ext hgy⟩
      rw [hgy, ← hTcoe]
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyM)).symm
  have h1 := isComponentOf_map_of_injective hQ φS hφS
  rw [hmap] at h1
  have hnormal : ((Subgroup.centralizer {T} ⊓ CatalogueBUnitaryB.unitarySpecial B).subgroupOf
      (Subgroup.centralizer {T})).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBUnitaryB.unitarySpecial_normal B).conj_mem _ hxS (g : sesqUnitaryGroup B)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hO := a6CentreForm_sesqCentralizer h hp2 (by rw [Module.finrank_fin_fun]; omega)
    (idForm_isSymm h n) (idForm_separatingLeft h n) hT _ h3
  have hQo : A6Safe (⁅R.comap (QuotientGroup.mk' _),
      R.comap (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))⁆ :
        Subgroup (gramSU h (idGram K n))) :=
    a6Safe_of_mulEquiv (Subgroup.equivMapOfInjective _ φS hφS)
      (a6Safe_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hO)
  have hQq := LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1)
    ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ).1
  exact a6Safe_of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (primeFormConjHom h (idGram K n) A)).subtype
      (subtype_injective _))
    (a6Safe_of_map_eq _ hQq hQR (hkerQ.le.trans hkerZ) hQo)

section Descent

open OddInner

theorem a6_commutingUnitary
    {p f : ℕ} {E V : Type}
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : UnitaryFieldData p f E) (hp2 : p ≠ 2) (hn : 1 ≤ Module.finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) : A6CentreForm (commutingUnitary B τ₀) := by
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = p ^ f := h.card_fixedField
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp2 h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    exact a6CentreForm_of_mulEquiv
      (Φ.trans (MulEquiv.subgroupCongr
        (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2)))
      (a6CentreForm_orthogonal h.prime hp2 h.one_le hkc _ hQ)
  · obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    have hWpos : 0 < Module.finrank h.fixedField (conjFixed h ((b : E) • τ₀)) := by
      rw [hfinW]
      omega
    exact a6CentreForm_of_mulEquiv Φ
      (a6CentreForm_isometryGroup h.prime hp2 h.one_le hkc B' halt hnd hWpos)

end Descent

end CFSG.ComponentClassification.CatLeafProof
