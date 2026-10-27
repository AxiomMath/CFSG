module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutLin
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutUni
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.RankDiag
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredThree

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.ComponentClassification.RankTwoClassical
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2

namespace Up34Chev2

theorem three_ne_zero_of_card_two_pow {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : (3 : K) ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  intro h3
  have h1 : (1 : K) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem two_lt_two_pow_of_ne {f : ℕ} (hf : 1 ≤ f) (hne : 2 ^ f ≠ 2) : 2 < 2 ^ f := by
  have h2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem up34_projectiveSL3_diag_no_pumpup {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {ψ : MulAut (projectiveSL 3 K)} (hψ : ψ ∈ linearAutGroup 3 K) :
    ¬ Up34Pumpup (projectiveSL 3 K) ψ := by
  intro hp
  haveI : IsSimpleGroup (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := K) le_rfl
  have hnab : ∃ a b : projectiveSL 3 K, a * b ≠ b * a := by
    have h1 := CFSG.RankThree.PartOne.KCLinearSubfield.not_commutative_projectiveSL (n := 3)
      (K := K) le_rfl
    push Not at h1
    exact h1
  obtain ⟨B, hB, hBcard, hBle⟩ :=
    hp.exists_elemAbelian_aut_gt_nine (up34_center_eq_bot_of_simple hnab)
  have hBD : B ≤ linearAutGroup 3 K :=
    hBle.trans (sup_le (Subgroup.zpowers_le.2 hψ) (innAut_le_linearAutGroup 3 K))
  have h9 := CFSG.RankThree.PartTwo.Sec4.card_inf_linearAutGroup_three_le h3 hB
  rw [inf_eq_left.2 hBD] at h9
  omega

theorem up34_psuConj_no_pumpup {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {ψ : MulAut (unitaryPSU h 3)} (hψ : ψ ∈ (psuConj h).range) :
    ¬ Up34Pumpup (unitaryPSU h 3) ψ := by
  intro hp
  obtain ⟨B, hB, hBcard, hBle⟩ := hp.exists_elemAbelian_aut_gt_nine
    (center_unitaryPSU_three_eq_bot h hq)
  have hBD : B ≤ (psuConj h).range :=
    hBle.trans (sup_le (Subgroup.zpowers_le.2 hψ) (stdPinnedPSU3 h).inn_le)
  have h9 := CFSG.RankThree.PartTwo.Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 B
    hB hBD
  omega

theorem congr_symm_primeFormConjHom {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hA : (A : GL (Fin 3) K) ∈ unitaryIsom3 h) :
    MulAut.congr (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3).symm
        (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A) =
      psuConj h ⟨A, hA⟩ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
  apply (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3).injective
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have e1 : psuConj h ⟨A, hA⟩ (unitaryProj h 3 s) = unitaryProj h 3 (suConj h ⟨A, hA⟩ s) := rfl
  rw [e1, CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psi_unitaryProj,
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psi_unitaryProj, primeFormConjHom_mk]
  rfl

theorem mem_unitaryIsom3_of_mem_primeFormUnitary {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    (A : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  have h1 := A.2
  rw [mem_unitaryIsom3]
  change (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : GL (Fin 3) K) =
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) at h1
  simp only [Units.val_one, Matrix.mul_one] at h1
  exact h1

theorem up34_primeFormD_three_no_pumpup {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 2 < 2 ^ f)
    {ψ : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}
    (hψ : ψ ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    ¬ Up34Pumpup (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ψ := by
  haveI := h.finite
  obtain ⟨A, rfl⟩ := hψ
  have hA := mem_unitaryIsom3_of_mem_primeFormUnitary h A
  intro hp
  haveI : Finite (unitaryPSU h 3) := inferInstance
  haveI : Finite (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Finite.of_equiv _ (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3).toEquiv
  have hp' := hp.of_congr (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3).symm
  rw [congr_symm_primeFormConjHom h A hA] at hp'
  have h3 : (3 : K) ≠ 0 :=
    three_ne_zero_of_card_two_pow (f := 2 * f) (by have := h.one_le; omega) h.card
  exact up34_psuConj_no_pumpup h3 hq ⟨⟨A, hA⟩, rfl⟩ hp'

end Up34Chev2

section Family


theorem up34C2OutDiag_a2 : Up34C2OutDiag_A2 := by
  intro f K _ _ hf hK A _ hp
  exact up34_projectiveSL3_diag_no_pumpup (three_ne_zero_of_card_two_pow hf hK)
    (conjAut_mem_linearAutGroup A) hp

theorem up34C2Inn_a2 : Up34Chev2Inn FamA2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | A r q =>
    have hq2 : q.p = 2 := hc
    have hr2 : r = 2 := hF
    subst hr2
    have hm := blueprintLieModel_A 2 q hv e
    rw [hq2] at hm
    have hC : StatedClassicalModel S .PSL 3 2 q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
    let e' : S ≃* projectiveSL 3 K := e0.trans (statedProjEquiv 3 K)
    haveI : Finite (projectiveSL 3 K) := Finite.of_equiv S e'.toEquiv
    have hxD : MulAut.congr e' (MulAut.conj x) ∈ linearAutGroup 3 K := by
      have : MulAut.congr e' (MulAut.conj x) = MulAut.conj (e' x) := by
        refine MulEquiv.ext fun y => ?_
        simp [MulAut.congr_apply, MulAut.conj_apply]
      rw [this]
      exact innAut_le_linearAutGroup 3 K ⟨e' x, rfl⟩
    exact up34_projectiveSL3_diag_no_pumpup (three_ne_zero_of_card_two_pow q.exponent_pos hK)
      hxD (hx.of_congr e')
  | _ => exact hF.elim

theorem up34C2OutDiag_twA2 : Up34C2OutDiag_TwA2 := by
  intro f K _ h _ hne ψ hψ _ hp
  exact up34_primeFormD_three_no_pumpup h
    (two_lt_two_pow_of_ne h.one_le fun h2 => hne ⟨rfl, h2⟩) hψ hp

theorem up34C2Inn_twA2 : Up34Chev2Inn FamTwA2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | twistedA r q =>
    have hq2 : q.p = 2 := hc
    have hr2 : r = 2 := hF
    subst hr2
    have hm := blueprintLieModel_twistedA 2 q hv e
    have hadm := statedLieAdmissible_twistedA hv
    rw [hq2] at hm hadm
    obtain ⟨K, _, h, ⟨e1⟩⟩ := exists_psu_model hadm hm
    haveI := h.finite
    haveI : Finite (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      Finite.of_equiv S e1.toEquiv
    have hq : 2 < 2 ^ q.exponent :=
      two_lt_two_pow_of_ne q.exponent_pos fun h2 => hadm.2.2.2 (by rw [h2])
    have hxD : MulAut.congr e1 (MulAut.conj x) ∈
        primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have : MulAut.congr e1 (MulAut.conj x) = MulAut.conj (e1 x) := by
        refine MulEquiv.ext fun y => ?_
        simp [MulAut.congr_apply, MulAut.conj_apply]
      rw [this]
      exact innerAut_le_primeFormD' h ⟨e1 x, rfl⟩
    exact up34_primeFormD_three_no_pumpup h hq hxD (hx.of_congr e1)
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
