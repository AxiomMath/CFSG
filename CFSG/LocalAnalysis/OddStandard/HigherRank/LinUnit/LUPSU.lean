module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUUnit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LULift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

@[expose] def luIsom {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h (idGram K n)) : sesqUnitaryGroup (idForm h n) :=
  ⟨Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K), (toLin_mem_sesqUnitaryGroup_iff _).mpr A.2⟩

@[expose] def luSUHom {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K) :
    gramSU h (idGram K n) →* sesqUnitaryGroup (idForm h n) :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
    LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
      (gramSU h (idGram K n)).subtype).codRestrict _ fun g =>
    (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp g.2).1

theorem luSUHom_injective {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K) :
    Function.Injective (luSUHom (n := n) h) := fun x y hxy =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (congrArg Subtype.val hxy))

theorem exists_sesqComponent_of_SU {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (A : primeFormUnitary h (idGram K n))
    {Q : Subgroup (fixedSubgroup (primeFormConjSU h (idGram K n) A))} (hQ : IsComponent Q) :
    ∃ (M : Subgroup (Subgroup.centralizer ({luIsom h A} : Set (sesqUnitaryGroup (idForm h n)))))
      (e : Q ≃* M), IsComponent M ∧ ∀ q : Q,
        ((e q : Subgroup.centralizer ({luIsom h A} : Set (sesqUnitaryGroup (idForm h n)))) :
          sesqUnitaryGroup (idForm h n)) =
            luSUHom h (((q : fixedSubgroup (primeFormConjSU h (idGram K n) A)) :
              gramSU h (idGram K n))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  set B := idForm h n with hBdef
  let T : sesqUnitaryGroup B := luIsom h A
  have hTcoe : ((T : LinearMap.GeneralLinearGroup K (Fin n → K))) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) := rfl
  let φS : gramSU h (idGram K n) →* sesqUnitaryGroup B := luSUHom h
  have hφS : Function.Injective φS := luSUHom_injective h
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
  exact ⟨M.subgroupOf (Subgroup.centralizer {T}), eQM, h3, fun q => rfl⟩

theorem inner_psu_modelIn {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (A : primeFormUnitary h (idGram K n)) (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {L : Subgroup (fixedSubgroup (primeFormConjHom h (idGram K n) A))} (hL : IsComponent L) :
    ModelIn p (luUniTuples n f) L := by
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
  let T : sesqUnitaryGroup B := luIsom h A
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
  refine modelIn_of_centralLift (QuotientGroup.mk'_surjective _) hK' ha hα
    (fun x => (primeFormConjHom_mk h (idGram K n) A x).symm) (fun Q hQ => ?_) hL
  obtain ⟨M, eQM, hM, -⟩ := exists_sesqComponent_of_SU h A hQ
  have hdim : 2 ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hm := sesqCentralizer_modelIn h hp2 hdim (idForm_isSymm h n)
    (idForm_separatingLeft h n) hT hM
  rw [Module.finrank_fin_fun] at hm
  exact hm.of_mulEquiv eQM

end CFSG.OddStandard.HigherRank.LinUnit
