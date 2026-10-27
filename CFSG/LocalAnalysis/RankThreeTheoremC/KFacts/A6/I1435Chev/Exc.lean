module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Families
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.OuterArith

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.OuterArith
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27 noE27_g2Low noE27_triD4Low noE27_reeF4)

namespace Arith

theorem not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h =>
  absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)

theorem three_dvd_of_order {n d N : ℕ} (h : n * d = N) (hd : ¬ 3 ∣ d) (hN : 3 ∣ N) :
    3 ∣ n := by
  rw [← h] at hN
  exact ((Nat.Prime.dvd_mul Nat.prime_three).1 hN).resolve_right hd

theorem pow_five_dvd_of_dvd_three {n d N : ℕ} (h : n * d = N) (hd : d ∣ 3)
    (hN : 3 ^ 6 ∣ N) : 3 ^ 5 ∣ n := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with rfl | rfl
  · rw [mul_one] at h
    subst h
    exact (pow_dvd_pow 3 (by norm_num)).trans hN
  · rw [← h, show (3 : ℕ) ^ 6 = 3 ^ 5 * 3 by norm_num] at hN
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hN

theorem pow_five_dvd_of_dvd_four {n d N : ℕ} (h : n * d = N) (hd : d ∣ 4)
    (hN : 3 ^ 5 ∣ N) : 3 ^ 5 ∣ n := by
  have hcop : Nat.Coprime (3 ^ 5) d := Nat.Coprime.coprime_dvd_right hd (by norm_num)
  rw [← h] at hN
  exact hcop.dvd_of_dvd_mul_right hN

variable {q : ℕ}

theorem three_dvd_even (hq : ¬ 3 ∣ q) (i : ℕ) : 3 ∣ q ^ (2 * i) - 1 :=
  dvd_even_pow_sub_one hq

theorem nine_dvd_six (hq2 : 2 ≤ q) (hq : ¬ 3 ∣ q) {k : ℕ} (hk : k ≠ 0) :
    9 ∣ q ^ (6 * k) - 1 := by
  have h := pow_dvd_pow_sub_one (x := q ^ 2) (m := 3 * k) (by nlinarith) (by omega)
    (dvd_sq_sub_one_of_not_dvd hq)
  have hv : 1 ≤ (3 * k).factorization 3 := by
    rw [Nat.factorization_mul (by norm_num) hk, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three]
    omega
  rw [← pow_mul, show 2 * (3 * k) = 6 * k by ring] at h
  have h9 : 3 ^ 2 ∣ q ^ (6 * k) - 1 := (pow_dvd_pow 3 (by omega)).trans h
  simpa using h9

theorem pow_six_dvd_four (hq2 : 2 ≤ q) (hq : ¬ 3 ∣ q) :
    3 ^ 6 ∣ (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have h12 : 9 ∣ q ^ 12 - 1 := by simpa using nine_dvd_six hq2 hq (k := 2) two_ne_zero
  have h8 : 3 ∣ q ^ 8 - 1 := by simpa using three_dvd_even hq 4
  have h6 : 9 ∣ q ^ 6 - 1 := by simpa using nine_dvd_six hq2 hq (k := 1) one_ne_zero
  have h2 : 3 ∣ q ^ 2 - 1 := by simpa using three_dvd_even hq 1
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h12 h8) h6) h2
  rwa [show (3 : ℕ) ^ 6 = 9 * 3 * 9 * 3 by norm_num]

theorem pow_five_dvd_prod_Icc (hq2 : 2 ≤ q) (hq : ¬ 3 ∣ q) {m : ℕ} (hm : 4 ≤ m) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
  have hsub : ({1, 2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 1 m := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_singleton]
  have h3 : 9 ∣ q ^ (2 * 3) - 1 := by simpa using nine_dvd_six hq2 hq (k := 1) one_ne_zero
  have := mul_dvd_mul (three_dvd_even hq 1) (mul_dvd_mul (three_dvd_even hq 2)
    (mul_dvd_mul h3 (three_dvd_even hq 4)))
  rwa [show (3 : ℕ) ^ 5 = 3 * (3 * (9 * 3)) by norm_num]

theorem pow_five_dvd_D4 (hq2 : 2 ≤ q) (hq : ¬ 3 ∣ q) :
    3 ^ 5 ∣ (q ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1) := by
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by simp),
    Finset.prod_insert (by simp), Finset.prod_singleton]
  have h3 : 9 ∣ q ^ (2 * 3) - 1 := by simpa using nine_dvd_six hq2 hq (k := 1) one_ne_zero
  have h4 : 3 ∣ q ^ 4 - 1 := by simpa using three_dvd_even hq 2
  have := mul_dvd_mul h4 (mul_dvd_mul (three_dvd_even hq 1) (mul_dvd_mul (three_dvd_even hq 2)
    h3))
  rwa [show (3 : ℕ) ^ 5 = 3 * (3 * (3 * 9)) by norm_num]

theorem two_pow_facts {q : PrimePower} (hq : q.p = 2) :
    2 ≤ q.p ^ q.exponent ∧ ¬ 3 ∣ q.p ^ q.exponent := by
  rw [hq]
  exact ⟨Nat.le_self_pow q.exponent_pos.ne' 2, not_three_dvd_two_pow _⟩

end Arith

open Arith

theorem Shape.not_pow_five {K : Type} [Group K] [Finite K] (h : Shape K)
    (h5 : 3 ^ 5 ∣ Nat.card K) : False :=
  h.not_dvd243 h5

theorem Shape.not_noE27 {K : Type} [Group K] [Finite K] (h : Shape K) (hn : NoE27 K) : False :=
  hn h.exists_E

theorem FamilyAt.of_pow_five {d : LieTypeIndex}
    (h : ∀ (hv : d.Valid) (K : Type) [Group K] [Finite K], IsSimpleGroup K →
      Nonempty (K ≃* ValidLieTypeIndex.Group ⟨d, hv⟩) → 3 ^ 5 ∣ Nat.card K) : FamilyAt d :=
  FamilyAt.of_not_shape fun hv K _ _ hs he =>
    ⟨(dvd_pow_self 3 (by norm_num)).trans (h hv K hs he), fun hS => hS.not_pow_five
      (h hv K hs he)⟩

section Families


theorem card_mul_divisor {K : Type} [Group K] {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hm : LieModel K t n p f) :
    Nat.card K * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K t n p f hadm hm).2.1

theorem familyAt_suzuki (m : ℕ) : FamilyAt (.suzuki m) := by
  intro hv K _ _ _ ⟨e⟩ hAut _
  exfalso
  have hm := CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv e
  obtain ⟨A, hA3, hA27⟩ := hAut
  have h := CFSG.RankThree.PartTwo.KFacts.KP7.card_dvd_three_of_pow_three hm hA3
  rw [hA27] at h
  norm_num at h

theorem familyAt_G2 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.G2 q) := by
  refine FamilyAt.of_not_shape fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hcem : ChevalleyExceptionalModel K .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e⟩
  have hm : LieModel K .G2 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  have hN := card_mul_divisor hcem.1 hm
  refine ⟨three_dvd_of_order hN (by simp [lieOrderDivisor]) ?_, fun hS => hS.not_noE27
    (noE27_g2Low K .G2 0 q.p q.exponent hcem.1 (by decide) ⟨rfl, by rw [hq]; decide⟩ hm)⟩
  simp only [lieOrderNumerator]
  exact Dvd.dvd.mul_left (by simpa using three_dvd_even hq3 1) _

theorem familyAt_trialityD4 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.trialityD4 q) := by
  refine FamilyAt.of_not_shape fun hv K _ _ _ ⟨e⟩ => ?_
  have hq2 : 2 ≤ 2 ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' 2
  have hq3 := not_three_dvd_two_pow q.exponent
  have hcem :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.chevalleyExceptionalModel_trialityD4_of_lie
      hv hq e
  have hm : LieModel K .trialityD4 0 2 q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  have hN := card_mul_divisor hcem.1 hm
  refine ⟨three_dvd_of_order hN (by simp [lieOrderDivisor]) ?_, fun hS => hS.not_noE27
    (noE27_triD4Low K .trialityD4 0 2 q.exponent hcem.1 (by decide) ⟨rfl, by decide⟩ hm)⟩
  simp only [lieOrderNumerator]
  exact Dvd.dvd.mul_left (by simpa using three_dvd_even hq3 1) _

theorem familyAt_reeF4 (m : ℕ) : FamilyAt (.reeF4 m) := by
  refine FamilyAt.of_not_shape fun hv K _ _ _ ⟨e⟩ => ?_
  have hq2 : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_self_pow (by omega) 2
  have hq3 := not_three_dvd_two_pow (2 * m + 1)
  have hR := CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_reeF4_of_lie hv e
  have hm : LieModel K .twistedF4 0 2 (2 * m + 1) := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  have hN := card_mul_divisor hR.1 hm
  refine ⟨three_dvd_of_order hN (by simp [lieOrderDivisor]) ?_, fun hS => hS.not_noE27
    (noE27_reeF4 K .twistedF4 0 2 (2 * m + 1) hR.1 (by decide) rfl hm)⟩
  simp only [lieOrderNumerator]
  have h4 : 3 ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by simpa using three_dvd_even hq3 2
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h4 _) _) _

theorem familyAt_tits : FamilyAt .tits := by
  refine FamilyAt.of_not_shape fun hv K _ _ _ ⟨e⟩ => ?_
  have hR := CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e
  have hm : LieModel K .Tits 0 2 1 := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  have hN := card_mul_divisor hR.1 hm
  refine ⟨three_dvd_of_order hN (by simp [lieOrderDivisor]) (by simp [lieOrderNumerator]),
    fun hS => hS.not_noE27 ?_⟩
  rintro ⟨E, hE, hc⟩
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv
    (E := E.map e.toMonoidHom) (hE.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

theorem familyAt_F4 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.F4 q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hcem : ChevalleyExceptionalModel K .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e⟩
  have hm : LieModel K .F4 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  refine pow_five_dvd_of_dvd_three (card_mul_divisor hcem.1 hm) (by simp [lieOrderDivisor]) ?_
  simp only [lieOrderNumerator]
  have := Dvd.dvd.mul_left (pow_six_dvd_four hq2 hq3) ((q.p ^ q.exponent) ^ 24)
  simpa only [mul_assoc] using this

theorem familyAt_E6 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.E6 q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hcem : ChevalleyExceptionalModel K .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e⟩
  have hm : LieModel K .E6 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  refine pow_five_dvd_of_dvd_three (card_mul_divisor hcem.1 hm)
    (by simp only [lieOrderDivisor]; exact Nat.gcd_dvd_left _ _) ?_
  simp only [lieOrderNumerator]
  set Q := q.p ^ q.exponent
  have h := mul_dvd_mul (mul_dvd_mul (one_dvd (Q ^ 36 * (Q ^ 9 - 1) * (Q ^ 5 - 1)))
    (pow_six_dvd_four hq2 hq3)) (one_dvd 1)
  rw [mul_one, one_mul, mul_one] at h
  refine h.trans (dvd_of_eq ?_)
  ring

theorem familyAt_E7 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.E7 q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hcem : ChevalleyExceptionalModel K .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e⟩
  have hm : LieModel K .E7 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  have hd : lieOrderDivisor .E7 0 (q.p ^ q.exponent) = 1 := by
    simp only [lieOrderDivisor]
    rw [hq]
    exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 (Nat.Even.sub_odd
      (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, q.exponent_pos.ne'⟩) odd_one))
  refine pow_five_dvd_of_dvd_three (card_mul_divisor hcem.1 hm) (by rw [hd]; norm_num) ?_
  simp only [lieOrderNumerator]
  set Q := q.p ^ q.exponent
  have h := mul_dvd_mul (one_dvd (Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 10 - 1)))
    (pow_six_dvd_four hq2 hq3)
  rw [one_mul] at h
  refine h.trans (dvd_of_eq ?_)
  ring

theorem familyAt_E8 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.E8 q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hcem : ChevalleyExceptionalModel K .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e⟩
  have hm : LieModel K .E8 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  refine pow_five_dvd_of_dvd_three (card_mul_divisor hcem.1 hm) (by simp [lieOrderDivisor]) ?_
  simp only [lieOrderNumerator]
  set Q := q.p ^ q.exponent
  have h30 : 9 ∣ Q ^ 30 - 1 := by simpa using nine_dvd_six hq2 hq3 (k := 5) (by norm_num)
  have h24 : 9 ∣ Q ^ 24 - 1 := by simpa using nine_dvd_six hq2 hq3 (k := 4) (by norm_num)
  have h12 : 9 ∣ Q ^ 12 - 1 := by simpa using nine_dvd_six hq2 hq3 (k := 2) (by norm_num)
  rw [show (3 : ℕ) ^ 6 = 9 * 9 * 9 by norm_num]
  refine (mul_dvd_mul (mul_dvd_mul h30 h24) h12).trans ⟨Q ^ 120 * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
    (Q ^ 14 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1), by ring⟩

theorem familyAt_twistedE6 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.twistedE6 q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hcem : ChevalleyExceptionalModel K .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e⟩
  have hm : LieModel K .twistedE6 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hcem⟩)
  refine pow_five_dvd_of_dvd_three (card_mul_divisor hcem.1 hm)
    (by simp only [lieOrderDivisor]; exact Nat.gcd_dvd_left _ _) ?_
  simp only [lieOrderNumerator]
  set Q := q.p ^ q.exponent
  have h := mul_dvd_mul (one_dvd (Q ^ 36 * (Q ^ 9 + 1) * (Q ^ 5 + 1)))
    (pow_six_dvd_four hq2 hq3)
  rw [one_mul] at h
  refine h.trans (dvd_of_eq ?_)
  ring

theorem familyAt_D (r : ℕ) (q : PrimePower) (hq : q.p = 2) : FamilyAt (.D r q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  have hm : LieModel K .POmegaPlus r q.p q.exponent := Or.inl ⟨by decide, hC⟩
  have hr : 4 ≤ r := hC.1.2.2
  refine pow_five_dvd_of_dvd_four (card_mul_divisor hC.1 hm)
    (by simp only [lieOrderDivisor]; exact Nat.gcd_dvd_left _ _) ?_
  simp only [lieOrderNumerator]
  set Q := q.p ^ q.exponent
  rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
  · have h := Dvd.dvd.mul_left (pow_five_dvd_D4 hq2 hq3) (Q ^ (4 * (4 - 1)))
    simpa only [mul_assoc] using h
  · exact Dvd.dvd.mul_left (pow_five_dvd_prod_Icc hq2 hq3 (by omega)) _

theorem familyAt_twistedD (r : ℕ) (q : PrimePower) (hq : q.p = 2) (hr : 5 ≤ r) :
    FamilyAt (.twistedD r q) := by
  refine FamilyAt.of_pow_five fun hv K _ _ _ ⟨e⟩ => ?_
  obtain ⟨hq2, hq3⟩ := two_pow_facts hq
  have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  have hm : LieModel K .POmegaMinus r q.p q.exponent := Or.inl ⟨by decide, hC⟩
  refine pow_five_dvd_of_dvd_four (card_mul_divisor hC.1 hm)
    (by simp only [lieOrderDivisor]; exact Nat.gcd_dvd_left _ _) ?_
  simp only [lieOrderNumerator]
  exact Dvd.dvd.mul_left (pow_five_dvd_prod_Icc hq2 hq3 (by omega)) _

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
