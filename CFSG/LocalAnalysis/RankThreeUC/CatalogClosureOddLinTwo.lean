module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearTwo
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartTwo.Census.LinearRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalInvolution
  CFSG.RankThree.PartTwo.Census Matrix
open scoped MatrixGroups

section Prime

variable {K : Type} [Field K]

theorem pRank_PSL_two_le [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : (r : K) ≠ 0)
    (hodd : Odd (Nat.card K)) : Assembly.pRank r (⊤ : Subgroup PSL(2, K)) ≤ 2 := by
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have hc : ¬ r ∣ Nat.card (Subgroup.center SL(2, K)) := by
    rw [sl2_natCard_center hodd]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  have h1 : CFSG.Open.pRank r (⊤ : Subgroup PSL(2, K)) =
      CFSG.Open.pRank r (⊤ : Subgroup SL(2, K)) :=
    CFSG.SectionRank.pRank_quotient_eq _ hc
  have h2 := pRank_le_of_injective_GL (X := SL(2, K)) hr hrK
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
  rw [Fintype.card_fin] at h2
  change CFSG.Open.pRank r (⊤ : Subgroup PSL(2, K)) ≤ 2
  rw [h1]
  exact h2

end Prime

section Char

variable {K : Type} [Field K] {r : ℕ} [Fact r.Prime] [CharP K r]

local notation "M₂" => Matrix (Fin 2) (Fin 2) K

theorem trace_eq_zero_of_pow_eq_zero {N : Matrix (Fin 2) (Fin 2) K} {n : ℕ} (hn : 0 < n)
    (h : N ^ n = 0) : N.trace = 0 ∧ N * N = 0 := by
  have hdet : N.det = 0 := by
    have : N.det ^ n = 0 := by rw [← Matrix.det_pow, h, Matrix.det_zero]
    exact (pow_eq_zero_iff (by omega)).mp this
  have hsq : N * N = N.trace • N := by
    rw [mul_self_eq_trace_smul_sub_det, hdet, zero_smul, sub_zero]
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, pow_succ]
  by_cases hN : N = 0
  · rw [hN]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hpow m] at h
    have hm : N.trace ^ m = 0 := by
      rcases smul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 hN
    have htr : N.trace = 0 := (pow_eq_zero_iff'.mp hm).1
    exact ⟨htr, by rw [hsq, htr, zero_smul]⟩

theorem false_of_char_odd (hr2 : r ≠ 2) {A B : SL(2, K)}
    (hAr : A ^ r ∈ Subgroup.center SL(2, K)) (hA : A ∉ Subgroup.center SL(2, K))
    (hB2 : B ^ 2 ∈ Subgroup.center SL(2, K)) (hB : B ∉ Subgroup.center SL(2, K))
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center SL(2, K)) : False := by
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K r 2).mp (by exact_mod_cast h0)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hrodd : Odd r := (Fact.out : r.Prime).odd_of_ne_two hr2
  have hneg : (-1 : SL(2, K)) ∈ Subgroup.center SL(2, K) := (mem_center_sl2_iff _).mpr (Or.inr rfl)
  have hBB : (B : Matrix (Fin 2) (Fin 2) K) * B = -1 := by
    rcases (mem_center_sl2_iff _).mp hB2 with h | h
    · exfalso
      apply hB
      have hinv : B⁻¹ = B := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, h]
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self K h2 B hinv with
        h' | h'
      · rw [h']
        exact Subgroup.one_mem _
      · rw [h']
        exact hneg
    · have := congrArg Subtype.val (show B * B = -1 by rw [← pow_two]; exact h)
      change (B : M₂) * B = ((-1 : SL(2, K)) : M₂) at this
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
  have hBdet : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
  have htrB : (B : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
    have hch := mul_self_eq_trace_smul_sub_det (B : Matrix (Fin 2) (Fin 2) K)
    rw [hBB, hBdet, one_smul, eq_sub_iff_add_eq, neg_add_cancel] at hch
    rcases smul_eq_zero.mp hch.symm with h | h
    · exact h
    · exfalso
      rw [h, Matrix.det_zero] at hBdet
      exact zero_ne_one hBdet
  obtain ⟨A', hA'r, hA', hA'B⟩ : ∃ A' : SL(2, K), A' ^ r = 1 ∧ A' ∉ Subgroup.center SL(2, K) ∧
      (A' * B * A'⁻¹ * B⁻¹ ∈ Subgroup.center SL(2, K)) := by
    rcases (mem_center_sl2_iff _).mp hAr with h | h
    · exact ⟨A, h, hA, hAB⟩
    · refine ⟨-A, ?_, fun hc => hA ?_, ?_⟩
      · rw [Odd.neg_pow hrodd, h, neg_neg]
      · have : -1 * (-A) ∈ Subgroup.center SL(2, K) := Subgroup.mul_mem _ hneg hc
        rwa [neg_one_mul, neg_neg] at this
      · have hinv : (-A)⁻¹ = -A⁻¹ :=
          inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
        rwa [hinv, neg_mul, neg_mul_neg]
  set N : M₂ := (A' : M₂) - 1 with hN
  have hApow : (A' : M₂) ^ r = 1 := by
    have := congrArg Subtype.val hA'r
    simpa using this
  have hNpow : N ^ r = 0 := by
    rw [hN, sub_pow_char_of_commute r (Commute.one_right (A' : M₂)), hApow, one_pow, sub_self]
  obtain ⟨hNtr, hNN⟩ := trace_eq_zero_of_pow_eq_zero (Fact.out : r.Prime).pos hNpow
  have hN0 : N ≠ 0 := by
    intro h0
    apply hA'
    refine mem_center_of_coe_eq_smul (c := 1) ?_
    rw [one_smul, ← sub_eq_zero]
    exact h0
  have hpol := mul_add_mul_eq_trace_smul hNtr htrB
  rcases (mem_center_sl2_iff _).mp hA'B with h | h
  ·
    have h' : A' * B = B * A' := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
    have hcomm : (A' : M₂) * B = B * A' := congrArg Subtype.val h'
    have hNB : N * B = B * N := by
      rw [hN, sub_mul, mul_sub, hcomm, Matrix.one_mul, Matrix.mul_one]
    rw [← hNB] at hpol
    have hs : N * B = ((2 : K)⁻¹ * (N * B).trace) • (1 : M₂) := by
      rw [mul_smul, ← hpol, ← two_smul K (N * B), smul_smul, inv_mul_cancel₀ h2, one_smul]
    have hsq : (N * B) * (N * B) = 0 := by
      have e : (N * B) * (N * B) = (N * N) * (B * B) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B : M₂) N, ← hNB, Matrix.mul_assoc,
          Matrix.mul_assoc]
      rw [e, hNN, Matrix.zero_mul]
    rw [hs, smul_mul_smul_comm, Matrix.one_mul, smul_eq_zero] at hsq
    rcases hsq with hs0 | hs0
    · rw [mul_self_eq_zero] at hs0
      rw [hs0, zero_smul] at hs
      apply hN0
      calc N = -(N * ((B : M₂) * B)) := by rw [hBB, mul_neg, Matrix.mul_one, neg_neg]
        _ = -(N * B * B) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hs, Matrix.zero_mul, neg_zero]
    · exact one_ne_zero hs0
  ·
    have h' : A' * B = -1 * B * A' :=
      mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_iff_eq_mul.mp h)
    have hanti : (A' : M₂) * B = -((B : M₂) * A') := by
      have := congrArg Subtype.val h'
      change (A' : M₂) * B = ((-1 : SL(2, K)) : M₂) * B * A' at this
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_one_mul,
        neg_mul] at this
      exact this
    have hNB : N * B + B * N = (-2 : K) • (B : M₂) := by
      rw [hN, sub_mul, mul_sub, hanti, Matrix.one_mul, Matrix.mul_one,
        show (-2 : K) • (B : M₂) = -(B : M₂) - B by
          rw [show (-2 : K) = -1 - 1 by norm_num, sub_smul, neg_one_smul, one_smul]]
      abel
    rw [hNB] at hpol
    apply hB
    refine mem_center_of_coe_eq_smul (c := (-2 : K)⁻¹ * (N * B).trace) ?_
    rw [mul_smul, ← hpol, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]

theorem not_commute_PSL_two_char_odd (hr2 : r ≠ 2) (a t : PSL(2, K)) (ha : orderOf a = r)
    (ht : orderOf t = 2) : a * t ≠ t * a := by
  intro hat
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective t
  have hmem : ∀ X : SL(2, K), (QuotientGroup.mk X : PSL(2, K)) = 1 →
      X ∈ Subgroup.center SL(2, K) := fun X hX => (QuotientGroup.eq_one_iff X).mp hX
  have hnmem : ∀ X : SL(2, K), (QuotientGroup.mk X : PSL(2, K)) ≠ 1 →
      X ∉ Subgroup.center SL(2, K) := fun X hX hc => hX ((QuotientGroup.eq_one_iff X).mpr hc)
  refine false_of_char_odd (r := r) (K := K) hr2 (A := A) (B := B) (hmem _ ?_) (hnmem _ ?_)
    (hmem _ ?_) (hnmem _ ?_) (hmem _ ?_)
  · have := pow_orderOf_eq_one (QuotientGroup.mk A : PSL(2, K))
    rw [ha] at this
    rw [QuotientGroup.mk_pow]
    exact this
  · intro h1
    rw [h1, orderOf_one] at ha
    exact (Fact.out : r.Prime).ne_one ha.symm
  · have := pow_orderOf_eq_one (QuotientGroup.mk B : PSL(2, K))
    rw [ht] at this
    rw [QuotientGroup.mk_pow]
    exact this
  · intro h1
    rw [h1, orderOf_one] at ht
    omega
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hat]
    group

end Char

theorem localRank_le_one_of_forall_ne {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2)
    (h : ∀ a t : H, orderOf a = r → orderOf t = 2 → a * t ≠ t * a) : localRank r H ≤ 1 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained r
    hr H (by change 0 < localRank r H; omega)
  change Assembly.pRank r L = localRank r H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ : ∃ E : Subgroup H, E ≤ L ∧ IsElemAbelian r E ∧
      Nat.card E = r ^ Assembly.pRank r L :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained r hr L
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨A', hA'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) r (n := 2)
    (by rw [hEc]; exact pow_dvd_pow r (by omega))
  set A : Subgroup H := A'.map E.subtype
  have hAE : A ≤ E := Subgroup.map_subtype_le A'
  have hAc : Nat.card A = r ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hA']
  have hpower : ∀ a : A, a ^ r = 1 := fun a => Subtype.ext (hE.2 a (hAE a.2))
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  have hcomp : ¬ r ∣ Nat.card P := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    intro h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    r hr A P hpower hAc hcomp (hAE.trans hEL)
  obtain ⟨a, ha1, ha⟩ : ∃ a : A, a ≠ 1 ∧
      P ⊓ Subgroup.centralizer ({(a : H)} : Set H) ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hP
    rw [hgen]
    exact iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun ha => hno a ha
  set X := P ⊓ Subgroup.centralizer ({(a : H)} : Set H)
  have hX2 : IsPGroup 2 X := hP2.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX2
    rcases k with _ | k
    · exact (ha ((Subgroup.eq_bot_iff_card X).mpr (by simpa using hk))).elim
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hta : (t : H) * a = a * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp t.2).2
  have hao : orderOf (a : H) = r := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val (hpower a)
    · exact fun h1 => ha1 (Subtype.ext h1)
  exact h a t hao (by rw [Subgroup.orderOf_coe]; exact ht) hta.symm

theorem Standing.false_of_PSL_two {G K : Type} [Group G] [Finite G] [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (hS : Standing G) (hodd : Odd (Nat.card K))
    (e : G ≃* PSL(2, K)) : False := by
  refine hS.false_of_localRank_le_two e fun r hr hr2 => ?_
  have : Fact r.Prime := ⟨hr⟩
  by_cases hrp : r = p
  · subst hrp
    exact (localRank_le_one_of_forall_ne hr hr2
      (fun a t ha ht => not_commute_PSL_two_char_odd hr2 a t ha ht)).trans (by norm_num)
  · refine localRank_le_of_pRank_le hr (pRank_PSL_two_le hr hr2 ?_ hodd)
    intro h0
    have := (CharP.cast_eq_zero_iff K p r).mp (by exact_mod_cast h0)
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp this).symm

end CFSG.LocalAnalysis.RankThreeUC
