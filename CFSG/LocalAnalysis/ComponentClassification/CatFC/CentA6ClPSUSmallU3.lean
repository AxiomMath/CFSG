module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUInner

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

section Kernel

variable {K : Type} [Field K] (h : UnitaryFieldData 3 2 K)

theorem psu_ker_three_two (x : ↥(gramSU h (idGram K 3)))
    (hx : (QuotientGroup.mk x : primeFormP h (idGram K 3)) = 1) : x = 1 := by
  rw [QuotientGroup.eq_one_iff] at hx
  obtain ⟨c, hN, hc3, hxc⟩ := hx
  have h10 : c ^ 10 = 1 := by
    apply Units.ext
    have := hN
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at this
    have e : (c : K) * (c : K) ^ 3 ^ 2 = (c : K) ^ 10 := by ring
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← e]
    exact this
  have hc1 : c = 1 := by
    have e : c ^ 10 = c * (c ^ 3) ^ 3 := by rw [← pow_mul, ← pow_succ']
    rw [e, hc3, one_pow, mul_one] at h10
    exact h10
  apply Subtype.ext
  rw [hxc, hc1, map_one]
  rfl

end Kernel

section Transfer

variable {n : ℕ} {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 3 f K)

theorem psu_transfer_injective {σ : MulAut (primeFormP h (idGram K n))} {Q : Type} [Group Q]
    {ι : Q →* LinearMap.GeneralLinearGroup K (Fin n → K)} {ρ : Q →* ↥(fixedSubgroup σ)}
    (hT : PSUIsTransfer h σ ι ρ) (hι : Function.Injective ι)
    (hker : ∀ x : ↥(gramSU h (idGram K n)),
      (QuotientGroup.mk x : primeFormP h (idGram K n)) = 1 → x = 1) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, hg, hρ⟩ := hT x
  have h1 : (QuotientGroup.mk g : primeFormP h (idGram K n)) = 1 := by
    rw [← hρ, hx]
    rfl
  have h2 := hker g h1
  apply hι
  rw [← hg, h2, map_one]
  simp

end Transfer

section Orders

variable {E : Type} [Field E] {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem psu_exists_perfect_unitary_two_card (h : UnitaryFieldData 3 2 E)
    {B' : W →ₛₗ[h.bar] W →ₗ[E] E} (hsym : B'.IsSymm) (hl : B'.SeparatingLeft)
    (hW : finrank E W = 2) :
    ∃ (Q : Type) (_ : Group Q) (j : Q →* sesqUnitaryGroup B'), Function.Injective j ∧
      commutator Q = ⊤ ∧ Nat.card Q = 720 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := h.finite
  obtain ⟨hsig2, hsig1, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data 3 2 h.card_eq_sq
  have hfix := OddInner.card_fixedSubfield hsig2 hsig1 h.card_eq_sq
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hsym hl
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 2 h.card_eq_sq)) ≠ 2 := by
    rw [hfix]; norm_num
  have hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 2 h.card_eq_sq)) ≠ 3 := by
    rw [hfix]; norm_num
  have hq := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple B' hsym hnd hsig2 hsig1 hW
    hq2 hq3
  obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
    (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 2 h.card_eq_sq) B' hsym hnd hsig2 hsig1 hW
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 2 h.card_eq_sq))) = 720 := by
    rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_two, hfix]
    norm_num
  refine ⟨↥(CatalogueBUnitaryIsometry.specialIsometry
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation 3 2 h.card_eq_sq) B'),
    inferInstance,
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.toMonoidHom.comp (Subgroup.subtype _),
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.injective.comp
      (Subgroup.subtype_injective _),
    Group.isPerfect_def.mp hq.1, ?_⟩
  rw [Nat.card_congr eSL.toEquiv, hcard]

end Orders

theorem psu_inner_three_two_false (hO : LieOrderFormulasInput) {K : Type} [Field K]
    (h : UnitaryFieldData 3 2 K) (A : primeFormUnitary h (idGram K 3))
    (hA : orderOf (primeFormConjHom h (idGram K 3) A) = 2)
    {D : Subgroup ↥(fixedSubgroup (primeFormConjHom h (idGram K 3) A))}
    (hD : A6Hyp (primeFormConjHom h (idGram K 3) A) D) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  obtain ⟨T, hT, hT2⟩ := psu_exists_involution_lift h (by norm_num : 3 ≤ 3) A hA
  have hdimV : finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hnV : 2 ≤ finrank K (Fin 3 → K) := by omega
  obtain ⟨l, -, -, hN, hP, hM, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h (by norm_num : (3 : ℕ) ≠ 2) hnV
      (idForm_isSymm h 3) (idForm_separatingLeft h 3) hT2
  have hker := psu_ker_three_two h
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have hr := Submodule.finrank_add_eq_of_isCompl hcompl
    have hP1 := Submodule.one_le_finrank_iff.mpr hP
    have hM1 := Submodule.one_le_finrank_iff.mpr hM
    have hsymm : ∀ Pm : Submodule K (Fin 3 → K), ((idForm h 3).domRestrict₁₂ Pm Pm).IsSymm :=
      fun Pm => ⟨fun x y => (idForm_isSymm h 3).eq (x : Fin 3 → K) (y : Fin 3 → K)⟩
    have key : ∀ (Pm : Submodule K (Fin 3 → K)),
        ((idForm h 3).domRestrict₁₂ Pm Pm).SeparatingLeft → finrank K Pm = 2 →
        (∀ {Q : Type} [Group Q] (j : Q →* sesqUnitaryGroup ((idForm h 3).domRestrict₁₂ Pm Pm)),
          Function.Injective j → ∃ ι : Q →* sesqUnitaryGroup (idForm h 3), Function.Injective ι ∧
            ∀ x, ι x ∈ Subgroup.centralizer ({T} : Set (sesqUnitaryGroup (idForm h 3)))) →
        False := by
      intro Pm hl hd emb
      obtain ⟨Q, _, j, hj, hperf, hcard⟩ := psu_exists_perfect_unitary_two_card h (hsymm Pm) hl hd
      obtain ⟨ι, hι, hc⟩ := emb j hj
      obtain ⟨ρ, hρT, hρk⟩ := psu_inner_perfect_hom h A T hT ι hι hc hperf
      have hinj : Function.Injective ρ :=
        psu_transfer_injective h hρT ((Subgroup.subtype_injective _).comp hι) hker
      have h1 := hD.psu_card_range_dvd ρ hperf
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard] at h1
      omega
    by_cases hP2 : finrank K (eigenPlus l (unitaryOp T)) = 2
    · exact key _ hlP hP2 (fun j hj => psu_emb_left _ e j hj)
    · exact key _ hlM (by omega) (fun j hj => psu_emb_right _ e j hj)
  · obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    omega

section Outer

variable {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K)

theorem psu_graph_not_inner (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 3 ^ f = 2))
    (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) :
    primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ ∉
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (MulAut.conj (QuotientGroup.mk g : primeFormP h (idGram K n)) :
      MulAut (primeFormP h (idGram K n))) =
      primeFormConjHom h (idGram K n) (gramSUToUnitary h (idGram K n) g) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H g' =>
      rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
  have h2 : primeFormPsi h hC ⟨A, φ⟩ =
      primeFormPsi h hC ⟨gramSUToUnitary h (idGram K n) g, 1⟩ := by
    rw [← primeFormConjHom_eq_psi h hC, ← h1]
    exact hx.symm
  have h3 := congrArg (primeFormFieldFactor h hC hn hq) h2
  rw [primeFormFieldFactor_psi h hC hn hq, primeFormFieldFactor_psi h hC hn hq] at h3
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  rw [← hφ c]
  have h4 : φ = 1 := h3
  rw [h4]
  rfl

end Outer

end CFSG.ComponentClassification.CatFC
