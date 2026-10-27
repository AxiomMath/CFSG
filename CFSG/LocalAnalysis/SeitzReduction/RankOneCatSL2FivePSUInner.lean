module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FivePSUBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSL
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

section Inner


theorem oddFivePSUInnerInput_holds : OddFivePSUInnerInput := by
  intro n K _ f h hadm A hA hF
  have hn : 3 ≤ n := hadm.2.2.1
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨h.prime⟩
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
  set Z := normOneScalars h (gramSU h (idGram K n)) n with hZdef
  set ψ := primeFormConjSU h (idGram K n) A with hψdef
  have hinv : Z.map ψ.toMonoidHom = Z := map_normOneScalars_conj h (idGram K n) A
  have heq : primeFormConjHom h (idGram K n) A =
      CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := rfl
  have hZc : Z ≤ center (gramSU h (idGram K n)) := normOneScalars_le_center h _ n
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
  have hfixA : ∀ x : gramSU h (idGram K n), x ∈ fixedSubgroup ψ ↔
      (A : GL (Fin n) K) * x = x * A := by
    intro x
    change primeFormConjSU h (idGram K n) A x = x ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹ = x ↔ _
    rw [mul_inv_eq_iff_eq_mul]
  have hmap : (fixedSubgroup ψ).map φS =
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
  have hnormal : ((Subgroup.centralizer {T} ⊓ CatalogueBUnitaryB.unitarySpecial B).subgroupOf
      (Subgroup.centralizer {T})).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBUnitaryB.unitarySpecial_normal B).conj_mem _ hxS (g : sesqUnitaryGroup B)
  obtain ⟨L, hL, hLm⟩ := hF.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := FiveList.exists_component_of_map_inf Z hZc ψ hinv φS hφS _ _ hmap
    hnormal hL
  have hNm : LieModel (N ⧸ center N) .PSL 2 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  have hdimV : 2 ≤ finrank K (Fin n → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨l, -, -, hN1, hP0, hM0, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2 hdimV (idForm_isSymm h n)
      (idForm_separatingLeft h n) hT
  have hsymm : ∀ P : Submodule K (Fin n → K), (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => (idForm_isSymm h n).eq (x : Fin n → K) (y : Fin n → K)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data 5 f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply 5 f h.card_eq_sq
  have key : ∀ P : Submodule K (Fin n → K), P ≠ ⊥ → (B.domRestrict₁₂ P P).SeparatingLeft →
      ∀ M : Subgroup (sesqUnitaryGroup (B.domRestrict₁₂ P P)), IsComponent M →
        LieModel (M ⧸ center M) .PSL 2 2 2 → finrank K P = 2 ∧ f = 1 := by
    intro P hP0 hlP M hM hMm
    let eI := CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h (B.domRestrict₁₂ P P)
    have hM' := LocalCores.isComponent_map_mulEquiv eI hM
    have hM'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (M.equivMapOfInjective eI.toMonoidHom eI.injective) hMm
    rcases FiveList.lieModel_of_isComponent_unitary h.prime hp2 h.one_le h.card_eq_sq
        (Submodule.one_le_finrank_iff.mpr hP0) _ (hsymm P)
        (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm P) hlP) hsig2 hsig1 hsig hM' with
      ⟨hd, hadm2, hmod⟩ | ⟨hadmU, hmodU⟩
    · obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hM'm hp2 hadm2 hmod
      exact ⟨hd, eq_one_of_five_pow_eq_five h5⟩
    · obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hM'm hp2 hadmU hmodU
      exact absurd h1 (by decide)
  rcases hN1 with hN1 | hN1
  ·
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN1
    have hN' := LocalCores.isComponent_map_mulEquiv e hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective e.toMonoidHom e.injective) hNm
    have hdimsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun] at hdimsum
    have h2part : f = 1 → 2 ≤ finrank K (eigenPlus l (unitaryOp T)) →
        2 ≤ finrank K (eigenMinus l (unitaryOp T)) → False := by
      intro hf1 hdp hdm
      have hq : 5 ^ f = 5 := by rw [hf1, pow_one]
      apply hF.not_dvd
      have h16p := FiveList.sixteen_dvd_card_sesqUnitaryGroup h hq (hsymm _) hlP hdp
      have h16m := FiveList.sixteen_dvd_card_sesqUnitaryGroup h hq (hsymm _) hlM hdm
      have h7 : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer {T}) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_prod]
        exact (by norm_num : 2 ^ 7 ∣ 16 * 16).trans (Nat.mul_dvd_mul h16p h16m)
      have hCS : Nat.card (Subgroup.centralizer {T}) = Nat.card (fixedSubgroup ψ) *
          (CatalogueBUnitaryB.unitarySpecial B).relIndex (Subgroup.centralizer {T}) := by
        have h1 := Subgroup.card_mul_index
          ((CatalogueBUnitaryB.unitarySpecial B).subgroupOf (Subgroup.centralizer {T}))
        have h2 : Nat.card ((CatalogueBUnitaryB.unitarySpecial B).subgroupOf
            (Subgroup.centralizer {T})) = Nat.card (fixedSubgroup ψ) := by
          rw [← Subgroup.inf_subgroupOf_right (CatalogueBUnitaryB.unitarySpecial B)
              (Subgroup.centralizer {T}),
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, ← hmap,
            Subgroup.card_map_of_injective hφS]
        rw [← h1, h2]
        rfl
      have hidx := FiveList.relIndex_unitarySpecial_dvd h (idForm_isSymm h n)
        (idForm_separatingLeft h n) (by rw [Module.finrank_fin_fun]; omega)
        (Subgroup.centralizer {T})
      rw [hq] at hidx
      exact FiveList.thirty_two_dvd_of_two_pow_seven_dvd (hCS ▸ h7) hidx
        (FiveList.card_fixed_dvd_card_mul Z ψ hinv)
        (FiveList.card_normOneScalars_dvd_six h hq (by omega))
    rcases FiveList.exists_component_factor hN' with ⟨M, hM, ⟨eM⟩⟩ | ⟨M, hM, ⟨eM⟩⟩
    · obtain ⟨hd2, hf1⟩ := key _ hP0 hlP M hM (FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm)
      refine ⟨?_, hf1⟩
      by_contra hn3
      exact h2part hf1 (by omega) (by omega)
    · obtain ⟨hd2, hf1⟩ := key _ hM0 hlM M hM (FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm)
      refine ⟨?_, hf1⟩
      by_contra hn3
      exact h2part hf1 (by omega) (by omega)
  ·
    obtain ⟨-, -, -, -, -, -, e, -⟩ := hpaired hN1
    let eG := e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasis K (eigenPlus l (unitaryOp T)))).toMulEquiv)
    have hN' := LocalCores.isComponent_map_mulEquiv eG hN
    obtain ⟨hadmE, hmodE⟩ := FiveList.lieModel_of_isComponent_GL h.prime (j := 2 * f)
      (by have := h.one_le; omega) h.card (Submodule.one_le_finrank_iff.mpr hP0) hN'
    obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two
      (FiveList.lieModel_centerQuotient_of_mulEquiv (N.equivMapOfInjective _ eG.injective) hNm)
      hp2 hadmE hmodE
    have := eq_one_of_five_pow_eq_five h5
    have := h.one_le
    omega

end Inner

end CFSG.SeitzReduction.RankOne
