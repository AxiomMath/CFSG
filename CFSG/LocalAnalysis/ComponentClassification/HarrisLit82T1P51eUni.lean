module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eLin
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup Matrix Module CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem notBC3_SL {k : Type} [Field k] [Finite k] {p j n : ℕ}
    (hadm : StatedLieAdmissible .PSL n p j) (hk : Nat.card k = p ^ j) :
    NotBC3 p (Matrix.SpecialLinearGroup (Fin n) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact ⟨.PSL, m + 1, j, by simp, hadm, Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩⟩

theorem notBC3_of_commutator_le {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsQuasisimple S) (hSX : _root_.commutator X ≤ S) {p : ℕ} (h : NotBC3 p S)
    {L : Subgroup X} (hL : IsComponent L) : NotBC3 p L := by
  obtain rfl := CentralQuotientLift.eq_of_isComponent_of_quasisimple hS hSX hL
  exact h

theorem notBC3_unitary {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 2 ≤ Module.finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    NotBC3 ℓ L := by
  have hq3 := CatLeafProof.OddInner.three_le_pow hℓ hℓ2 he
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsigma hne hE
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hW3 | hW3
  · have hd : Module.finrank E W = 2 := by omega
    by_cases h3 : ℓ ^ e = 3
    · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hd
        (hfix.trans h3)
      exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
    · have hq5 := CatLeafProof.OddInner.five_le_pow hℓ hℓ2 he h3
      have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
        hne hd (by rw [hfix]; omega) (by rw [hfix]; exact h3)
      obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
        sigma h hsym hnd hsigma hne hd
      have hadm : StatedLieAdmissible .PSL 2 ℓ e :=
        CatLeafProof.OddInner.admissible_PSL hℓ he le_rfl (Or.inr (by omega)) (Or.inr h3)
      exact notBC3_of_commutator_le hquasi (Abelianization.commutator_subset_ker _)
        (NotBC3.of_mulEquiv eSL (notBC3_SL hadm hfix)) hL
  · have hadm : StatedLieAdmissible .PSU (Module.finrank E W) ℓ e :=
      ⟨hℓ, he, hW3, fun h' => by have := (Prod.mk.inj h').2; omega⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW3 h hsym hnd hsigma
      hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    exact ⟨.PSU, Module.finrank E W, e, by simp, hadm, Or.inl ⟨by decide, hadm, E,
      inferInstance, inferInstance, hE, ⟨eX⟩⟩⟩

theorem notBC3_unitary_pos {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 1 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    NotBC3 ℓ L := by
  rcases Nat.lt_or_ge (finrank E W) 2 with h1 | h2
  · have := CatalogueBUnitaryIsometry.isometry_one_solvable h (by omega)
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  · exact notBC3_unitary hℓ hℓ2 he hE h2 h hsym hnd hsigma hne hsig hL

theorem notBC3_sesqCentralizer {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {L : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)))}
    (hL : IsComponent L) : NotBC3 p L := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    exact notBC3_of_component_equiv
      (e.trans (MulEquiv.prodCongr (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)
        (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)))
      (fun M hMc => notBC3_prod
        (fun M₁ hM₁ => notBC3_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hP) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlP) hsig2 hsig1 hsig hM₁)
        (fun M₂ hM₂ => notBC3_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hM) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlM) hsig2 hsig1 hsig hM₂)
        hMc) hL
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    exact notBC3_of_component_equiv
      (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv))
      (fun M hMc => notBC3_GL h.prime hp (j := 2 * f) (by have := h.one_le; omega) h.card
        (by omega) hMc) hL

theorem notBC3_inner_psu {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (A : primeFormUnitary h (idGram K n)) (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {L : Subgroup (fixedSubgroup (primeFormConjHom h (idGram K n) A))} (hL : IsComponent L) :
    NotBC3 p L := by
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
    rw [e1, CatLeafProof.OddInner.toLin_scalar]
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
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
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
  have hfixA : ∀ x : gramSU h (idGram K n),
      x ∈ FixedCommutingProduct.fixedSubgroup (primeFormConjSU h (idGram K n) A) ↔
      (A : GL (Fin n) K) * x = x * A := by
    intro x
    change primeFormConjSU h (idGram K n) A x = x ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹ = x ↔ _
    rw [mul_inv_eq_iff_eq_mul]
  have hmap : (FixedCommutingProduct.fixedSubgroup (primeFormConjSU h (idGram K n) A)).map φS =
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
  have hU := notBC3_sesqCentralizer h hp2 (by rw [Module.finrank_fin_fun]; omega)
    (idForm_isSymm h n) (idForm_separatingLeft h n) hT h3
  have hQo : NotBC3 p (⁅R.comap (QuotientGroup.mk' _),
      R.comap (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))⁆ :
        Subgroup (gramSU h (idGram K n))) :=
    NotBC3.of_mulEquiv (Subgroup.equivMapOfInjective _ φS hφS)
      (NotBC3.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hU)
  exact NotBC3.of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (primeFormConjHom h (idGram K n) A)).subtype
      (subtype_injective _))
    (NotBC3.of_centerQuotient_equiv eQR.symm hQo)

theorem famNoSpin7_psu (hO : LieOrderFormulasInput) : FamNoSpin7 .PSU := by
  intro X _ n p f hp hp2 hadm hX g hg L hL
  obtain ⟨K, _, h, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hX
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e g)
  let A : primeFormUnitary h (idGram K n) :=
    ⟨(s : GL (Fin n) K), ((mem_gramSU_iff_unitary h).mp s.2).1⟩
  have hconj : primeFormConjHom h (idGram K n) A = MulAut.conj (e g) := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H y =>
      have h1 : (⟨(A : GL (Fin n) K) * y * (A : GL (Fin n) K)⁻¹,
          conj_mem_gramSU h (idGram K n) A.2 y.2⟩ : gramSU h (idGram K n)) = s * y * s⁻¹ :=
        Subtype.ext rfl
      rw [primeFormConjHom_mk, h1, MulAut.conj_apply, ← hs, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hord : orderOf (primeFormConjHom h (idGram K n) A) = 2 := by
    rw [hconj, orderOf_conj_mulEquiv]
    exact hg
  refine NotBC3.noSpin7 hO hp2 (notBC3_of_conj_mulEquiv e g (fun M hM => ?_) hL)
  let Ψ := MulEquiv.subgroupCongr (congrArg fixedSubgroup hconj.symm)
  exact NotBC3.of_mulEquiv (M.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (notBC3_inner_psu h hp2 hadm A hord (LocalCores.isComponent_map_mulEquiv Ψ hM))

end CFSG.ComponentClassification.HarrisLit.T1.P51e
