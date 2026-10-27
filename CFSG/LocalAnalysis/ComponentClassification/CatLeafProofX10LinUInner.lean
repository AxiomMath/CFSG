module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinUCent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem inner_psu_component_cases {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (A : primeFormUnitary h (idGram K n)) (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {L : Subgroup (fixedSubgroup (primeFormConjHom h (idGram K n) A))} (hL : IsComponent L) :
    (∃ z ∈ L, (∀ y ∈ L, z * y = y * z) ∧ z * z = 1 ∧ z ≠ 1) ∨
      ModelIn p (linUInnerTuples n f) L := by
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
  refine component_cases_of_centralLift (QuotientGroup.mk'_surjective _) hK' ha hα
    (fun x => (primeFormConjHom_mk h (idGram K n) A x).symm) (fun Q hQ => ?_) hL
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
      x ∈ fixedSubgroup (primeFormConjSU h (idGram K n) A) ↔ (A : GL (Fin n) K) * x = x * A := by
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
  have hMF : Assembly.IsComponentOf
      (Q.map (fixedSubgroup (primeFormConjSU h (idGram K n) A)).subtype)
      (fixedSubgroup (primeFormConjSU h (idGram K n) A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le Q)).2 ?_
    have hQQ : (Q.map (fixedSubgroup (primeFormConjSU h (idGram K n) A)).subtype).subgroupOf
        (fixedSubgroup (primeFormConjSU h (idGram K n) A)) = Q :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) Q
    rw [hQQ]
    exact hQ
  have h1 := isComponentOf_map_of_injective hMF φS hφS
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
  set M := (Q.map (fixedSubgroup (primeFormConjSU h (idGram K n) A)).subtype).map φS with hMdef
  let eQM : Q ≃* M.subgroupOf (Subgroup.centralizer {T}) :=
    ((Q.equivMapOfInjective (fixedSubgroup (primeFormConjSU h (idGram K n) A)).subtype
      (subtype_injective _)).trans
      ((Q.map (fixedSubgroup (primeFormConjSU h (idGram K n) A)).subtype).equivMapOfInjective
        φS hφS)).trans
        (Subgroup.subgroupOfEquivOfLe h2.1).symm
  have hdim : 2 ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    omega
  rcases sesqCentralizer_component_cases h hp2 hdim (idForm_isSymm h n)
      (idForm_separatingLeft h n) hT h3 with ⟨z, hzM, hzc, hzz, hzns⟩ | hm
  ·
    left
    obtain ⟨w, hw⟩ := eQM.surjective ⟨z, hzM⟩
    refine ⟨(w : fixedSubgroup (primeFormConjSU h (idGram K n) A)), w.2, fun y hy => ?_, ?_, ?_⟩
    · have h4 := hzc _ (eQM ⟨y, hy⟩).2
      have h5 : eQM (w * ⟨y, hy⟩) = eQM (⟨y, hy⟩ * w) := by
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hw]
        exact h4
      exact congrArg Subtype.val (eQM.injective h5)
    · have h5 : eQM (w * w) = 1 := by
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul, hw]
        exact hzz
      exact congrArg Subtype.val (eQM.injective (h5.trans (map_one eQM).symm))
    ·
      intro h1'
      have hmem : ((w : fixedSubgroup (primeFormConjSU h (idGram K n) A)) :
          gramSU h (idGram K n)) ∈ normOneScalars h (gramSU h (idGram K n)) n := by
        rw [← QuotientGroup.ker_mk' (normOneScalars h (gramSU h (idGram K n)) n)]
        exact h1'
      obtain ⟨c', -, -, hc'⟩ := hmem
      have hz' : ((eQM w : M.subgroupOf (Subgroup.centralizer {T})) :
          Subgroup.centralizer {T}) = z := congrArg Subtype.val hw
      apply hzns (c' : K)
      rw [← hz']
      change ((Matrix.GeneralLinearGroup.toLin
        (((w : fixedSubgroup (primeFormConjSU h (idGram K n) A)) : gramSU h (idGram K n)) :
          GL (Fin n) K) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) = (c' : K) • 1
      rw [hc', OddInner.toLin_scalar]
  · right
    rw [Module.finrank_fin_fun] at hm
    exact hm.of_mulEquiv eQM

end CFSG.ComponentClassification.CatLeafProof.X10Lin
