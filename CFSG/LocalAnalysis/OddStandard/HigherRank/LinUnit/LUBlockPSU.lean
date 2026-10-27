module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUPSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockSesq
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockLift
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUOrder

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)

theorem exists_sq_eq_neg_one_of_card_nine {K : Type} [Field K] (hK : Nat.card K = 9) :
    ∃ ζ : K, ζ ^ 2 = -1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hsq : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
    norm_num
  obtain ⟨r, hr⟩ := hsq
  exact ⟨r, by rw [pow_two]; exact hr.symm⟩

theorem inner_psu_setup {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2) :
    orderOf (QuotientGroup.mk (luIsom h A) : sesqProjUnitary h (idForm h n)) = 2 ∧
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
        center (gramSU h (idGram K n)) ∧
      (∀ x, primeFormConjSU h (idGram K n) A (primeFormConjSU h (idGram K n) A x) = x) ∧
      (∀ s, primeFormConjHom h (idGram K n) A (primeFormConjHom h (idGram K n) A s) = s) := by
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
  exact ⟨hT, hK', ha, hα⟩

theorem luSUHom_mem_sesqNormOneScalars {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) {x : gramSU h (idGram K n)}
    (hx : x ∈ normOneScalars h (gramSU h (idGram K n)) n) :
    luSUHom h x ∈ sesqNormOneScalars h (idForm h n) := by
  obtain ⟨c, hc, -, hxc⟩ := hx
  refine ⟨(c : K), hc, ?_⟩
  have e1 : ((luSUHom h x : sesqUnitaryGroup (idForm h n)) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) := by
    rw [← hxc]
    rfl
  rw [e1, OddInner.toLin_scalar]

theorem su_component_hasFourElt {n : ℕ} {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 3 f K)
    (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (hT : orderOf (QuotientGroup.mk (luIsom h A) : sesqProjUnitary h (idForm h n)) = 2)
    {Q : Subgroup (fixedSubgroup (primeFormConjSU h (idGram K n) A))} (hQ : IsComponent Q)
    (hmodel : Blueprint.LieModel (Q ⧸ center Q) .PSU 4 3 1) :
    ∃ q : Q, q ∈ center Q ∧
      orderOf (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
        ((q : fixedSubgroup (primeFormConjSU h (idGram K n) A)) : gramSU h (idGram K n))) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite K := h.finite
  have : CharP K 3 := h.charP
  have hdim : 2 ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨M, eQM, hM, hcoe⟩ := exists_sesqComponent_of_SU h A hQ
  have hmodelM : Blueprint.LieModel (M ⧸ center M) .PSU 4 3 1 :=
    Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (center Q) (center M) eQM (Subgroup.map_center_eq eQM)) hmodel
  rcases sesqCentralizer_block h (by norm_num) hdim (idForm_isSymm h n)
      (idForm_separatingLeft h n) hT hM with ⟨k, f', hk⟩ | ⟨d, -, hd, hblock⟩
  · exact (lieModel_psl_ne_psu43 hk.1 hk.2 hmodelM).elim
  obtain ⟨rfl, rfl⟩ := lieModel_psu_eq_psu43 hd.1 hd.2 hmodelM
  obtain ⟨ζ, hζ⟩ := exists_sq_eq_neg_one_of_card_nine (by rw [h.card]; norm_num)
  have hζ4 : ζ ^ 4 = 1 := by
    calc ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hζ]; norm_num
  have hζn : h.norm ζ = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
    calc ζ * ζ ^ 3 ^ 1 = ζ ^ 4 := by ring
      _ = 1 := hζ4
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h1
    have h2 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination (-1 : K) * (hζ.symm.trans h1)
    have := (CharP.cast_eq_zero_iff K 3 2).mp h2
    omega
  obtain ⟨w, hwc, P, W, hb⟩ := hblock ζ hζn hζ4
  obtain ⟨q, hqw⟩ : ∃ q : Q, eQM q = w := ⟨eQM.symm w, eQM.apply_symm_apply w⟩
  have hyg : luSUHom h (((q : fixedSubgroup (primeFormConjSU h (idGram K n) A)) :
      gramSU h (idGram K n))) = ((w : Subgroup.centralizer ({luIsom h A} :
        Set (sesqUnitaryGroup (idForm h n)))) : sesqUnitaryGroup (idForm h n)) := by
    rw [← hcoe q, hqw]
  refine ⟨q, Subgroup.mem_center_iff.mpr fun y => eQM.injective ?_, ?_⟩
  · simp only [map_mul, hqw]
    exact (Subgroup.mem_center_iff.mp hwc) (eQM y)
  · set y : gramSU h (idGram K n) :=
      ((q : fixedSubgroup (primeFormConjSU h (idGram K n) A)) : gramSU h (idGram K n)) with hy
    have hg4 : luSUHom h (y ^ 4) = 1 := by
      rw [map_pow, hyg]
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact (ActsAsBlock.pow_eq_one_iff hb 4).mpr hζ4
    have hy4 : y ^ 4 = 1 := luSUHom_injective h (hg4.trans (map_one _).symm)
    have hfin : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) y) ^ 2 ^ (1 + 1) =
        1 := by
      rw [← map_pow]
      norm_num [hy4]
    have hnot : ¬ (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) y) ^ 2 ^ 1 =
        1 := by
      intro hcon
      rw [pow_one, ← map_pow] at hcon
      have hy2 := luSUHom_mem_sesqNormOneScalars h ((QuotientGroup.eq_one_iff _).mp hcon)
      rw [map_pow, hyg] at hy2
      exact hζ2 (ActsAsBlock.pow_eq_one_of_mem_normOneScalars hb 2 hy2)
    have := orderOf_eq_prime_pow (p := 2) hnot hfin
    simpa using this

theorem inner_psu_hasFourElt {n : ℕ} {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 3 f K)
    (hadm : StatedLieAdmissible .PSU n 3 f) (A : primeFormUnitary h (idGram K n))
    (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {L : Subgroup (fixedSubgroup (primeFormConjHom h (idGram K n) A))} (hL : IsComponent L) :
    HasFourElt L := by
  have : Finite K := h.finite
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨hT, hK', ha, hα⟩ := inner_psu_setup h hn A hA
  exact hasFourElt_of_centralLift (QuotientGroup.mk'_surjective _) hK' ha hα
    (fun x => (primeFormConjHom_mk h (idGram K n) A x).symm)
    (fun Q hQ hmodel => su_component_hasFourElt h hn A hT hQ hmodel) hL

end CFSG.OddStandard.HigherRank.LinUnit
