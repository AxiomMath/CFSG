module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXC
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup Matrix Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

variable {Q : ℕ → Prop}

theorem compOrd_unitary {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    (hW1 : 1 ≤ finrank E W) (hQ2 : Q (Open.ordA 1 (ℓ ^ e)))
    (hQm : 3 ≤ finrank E W → Q (Open.ordTwistedA (finrank E W - 1) (ℓ ^ e))) :
    CompOrd Q (CatalogueBUnitaryIsometry.isometryGroup h) := by
  intro L hL
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsigma hne hE
  have hq3 := CatLeafProof.OddInner.three_le_pow hℓ hℓ2 he
  rcases Nat.lt_or_ge (finrank E W) 2 with h1 | h2
  · have := CatalogueBUnitaryIsometry.isometry_one_solvable h (by omega)
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  rcases Nat.lt_or_ge (finrank E W) 3 with hW3 | hW3
  · have hd : finrank E W = 2 := by omega
    by_cases h3 : ℓ ^ e = 3
    · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hd
        (hfix.trans h3)
      exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
    · have hq5 := CatLeafProof.OddInner.five_le_pow hℓ hℓ2 he h3
      have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
        hne hd (by rw [hfix]; omega) (by rw [hfix]; exact h3)
      obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
        sigma h hsym hnd hsigma hne hd
      obtain rfl :=
        LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
          hquasi (Abelianization.commutator_subset_ker _) hL
      rw [card_centerQuotient_congr eSL, card_psl_eq_ordA (by norm_num), hfix]
      exact hQ2
  · have hadm : StatedLieAdmissible .PSU (finrank E W) ℓ e :=
      ⟨hℓ, he, hW3, fun h' => by have := (Prod.mk.inj h').2; omega⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW3 h hsym hnd hsigma
      hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    have hLie : Blueprint.LieModel (L ⧸ center L) .PSU (finrank E W) ℓ e :=
      Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩
    rw [GH74.card_of_lieModel_PSU (by omega) hℓ2 hLie]
    exact hQm hW3

theorem compOrd_sesqCentralizer {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hn : finrank E V = 5) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    (hQ2 : Q (Open.ordA 1 (p ^ f))) (hQ3 : Q (Open.ordTwistedA 2 (p ^ f)))
    (hQ4 : Q (Open.ordTwistedA 3 (p ^ f))) :
    CompOrd Q (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hA
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  have hP1 := Submodule.one_le_finrank_iff.mpr hP
  have hM1 := Submodule.one_le_finrank_iff.mpr hM
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  have hQm : ∀ m, m ≤ 4 → 3 ≤ m → Q (Open.ordTwistedA (m - 1) (p ^ f)) := by
    intro m hm4 hm3
    interval_cases m
    · exact hQ3
    · exact hQ4
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    refine CompOrd.of_mulEquiv
      (e.trans (MulEquiv.prodCongr (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)
        (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _))) ?_
    exact @CompOrd.prod _ _ _ _ _ (CatalogueBUnitaryIsometry.isometryGroupFinite _)
      (CatalogueBUnitaryIsometry.isometryGroupFinite _)
      (compOrd_unitary h.prime hp h.one_le h.card_eq_sq _ (hsymm _)
        (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlP) hsig2 hsig1 hsig hP1 hQ2
        fun h3 => hQm _ (by omega) h3)
      (compOrd_unitary h.prime hp h.one_le h.card_eq_sq _ (hsymm _)
        (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlM) hsig2 hsig1 hsig hM1 hQ2
        fun h3 => hQm _ (by omega) h3)
  · obtain ⟨-, -, -, hdim2, -⟩ := hpaired hN
    omega

theorem compOrd_inner_psu {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (A : primeFormUnitary h (idGram K 5))
    (hA : orderOf (primeFormConjHom h (idGram K 5) A) = 2) (hQ2 : Q (Open.ordA 1 (p ^ f)))
    (hQ3 : Q (Open.ordTwistedA 2 (p ^ f))) (hQ4 : Q (Open.ordTwistedA 3 (p ^ f))) :
    CompOrd Q (fixedSubgroup (primeFormConjHom h (idGram K 5) A)) := by
  intro L hL
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hA1 : primeFormConjHom h (idGram K 5) A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : primeFormConjHom h (idGram K 5) A * primeFormConjHom h (idGram K 5) A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, hcN, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) (A := A * A) (by rw [map_mul, hA2])
  have hAA : (A : GL (Fin 5) K) * A = GeneralLinearGroup.scalar (Fin 5) c := by
    rw [← Subgroup.coe_mul]
    exact hc
  set B := idForm h 5 with hBdef
  let T : sesqUnitaryGroup B :=
    ⟨Matrix.GeneralLinearGroup.toLin (A : GL (Fin 5) K),
      (toLin_mem_sesqUnitaryGroup_iff _).mpr A.2⟩
  have hTcoe : ((T : LinearMap.GeneralLinearGroup K (Fin 5 → K))) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin 5) K) := rfl
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    refine ⟨(c : K), hcN, ?_⟩
    have e1 : ((T * T : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin 5 → K)) =
        Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin 5) c) := by
      rw [← hAA, map_mul]
      rfl
    rw [e1, CatLeafProof.OddInner.toLin_scalar]
  have hTne : (QuotientGroup.mk T : sesqProjUnitary h B) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c', -, hc'⟩ := h1
    apply hA1
    have hcomm : ∀ g : GL (Fin 5) K, (A : GL (Fin 5) K) * g = g * A := by
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
      change (A : GL (Fin 5) K) * g * (A : GL (Fin 5) K)⁻¹ = g
      rw [hcomm, mul_inv_cancel_right]
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2 := by
    refine orderOf_eq_prime ?_ hTne
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hTT
  have hK' : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 5)) 5)).ker ≤
      center (gramSU h (idGram K 5)) := by
    rw [QuotientGroup.ker_mk']
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  have ha : ∀ x, primeFormConjSU h (idGram K 5) A (primeFormConjSU h (idGram K 5) A x) = x := by
    intro x
    apply Subtype.ext
    change (A : GL (Fin 5) K) * ((A : GL (Fin 5) K) * x * (A : GL (Fin 5) K)⁻¹) *
      (A : GL (Fin 5) K)⁻¹ = x
    calc (A : GL (Fin 5) K) * ((A : GL (Fin 5) K) * x * (A : GL (Fin 5) K)⁻¹) *
          (A : GL (Fin 5) K)⁻¹ =
        ((A : GL (Fin 5) K) * A) * x * ((A : GL (Fin 5) K) * A)⁻¹ := by group
      _ = x := by rw [hAA, ← (commute_scalar c _).eq, mul_inv_cancel_right]
  have hα : ∀ s, primeFormConjHom h (idGram K 5) A (primeFormConjHom h (idGram K 5) A s) = s :=
    fun s => by rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    (QuotientGroup.mk'_surjective _) hK' ha hα
    (fun x => (primeFormConjHom_mk h (idGram K 5) A x).symm)
  set R := L.map (fixedSubgroup (primeFormConjHom h (idGram K 5) A)).subtype
  have hR : Assembly.IsComponentOf R (fixedSubgroup (primeFormConjHom h (idGram K 5) A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (primeFormConjHom h (idGram K 5) A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  let φS : gramSU h (idGram K 5) →* sesqUnitaryGroup B :=
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin 5) K ≃*
      LinearMap.GeneralLinearGroup K (Fin 5 → K)).toMonoidHom.comp
        (gramSU h (idGram K 5)).subtype).codRestrict _ fun g =>
      (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp g.2).1
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (congrArg Subtype.val hxy))
  have hcommφ : ∀ g : GL (Fin 5) K, (A : GL (Fin 5) K) * g = g * A ↔
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin 5) K) * Matrix.GeneralLinearGroup.toLin g =
        Matrix.GeneralLinearGroup.toLin g * Matrix.GeneralLinearGroup.toLin (A : GL (Fin 5) K) :=
    fun g => by rw [← map_mul, ← map_mul, Matrix.GeneralLinearGroup.toLin.injective.eq_iff]
  have hfixA : ∀ x : gramSU h (idGram K 5), x ∈ fixedSubgroup (primeFormConjSU h (idGram K 5) A) ↔
      (A : GL (Fin 5) K) * x = x * A := by
    intro x
    change primeFormConjSU h (idGram K 5) A x = x ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin 5) K) * x * (A : GL (Fin 5) K)⁻¹ = x ↔ _
    rw [mul_inv_eq_iff_eq_mul]
  have hmap : (fixedSubgroup (primeFormConjSU h (idGram K 5) A)).map φS =
      Subgroup.centralizer {T} ⊓ CatalogueBUnitaryB.unitarySpecial B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact ((hcommφ x).mp ((hfixA x).mp hx)).symm
      · rw [Subgroup.mem_subgroupOf]
        exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K 5) x).mpr x.2
    · intro hy
      obtain ⟨hyM, hyS⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_subgroupOf] at hyS
      set g := Matrix.GeneralLinearGroup.toLin.symm (y : LinearMap.GeneralLinearGroup K
        (Fin 5 → K)) with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = (y : LinearMap.GeneralLinearGroup K
          (Fin 5 → K)) := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K 5) := by
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
  have hO := compOrd_sesqCentralizer h hp2 (by rw [Module.finrank_fin_fun])
    (idForm_isSymm h 5) (idForm_separatingLeft h 5) hT hQ2 hQ3 hQ4 _ h3
  rw [card_centerQuotient_congr (L.equivMapOfInjective
      (fixedSubgroup (primeFormConjHom h (idGram K 5) A)).subtype (subtype_injective _)),
    Nat.card_congr eQR.symm.toEquiv,
    card_centerQuotient_congr (Subgroup.equivMapOfInjective _ φS hφS),
    ← card_centerQuotient_congr (Subgroup.subgroupOfEquivOfLe h2.1)]
  exact hO

end P211X

end CFSG.ComponentClassification.GSThmB
