module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem case1_mem_normalizer_of_comm {T : Subgroup G} {x : G}
    (hxcT : ∀ t ∈ T, x * t = t * x) : x ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hxcT n hn, mul_inv_cancel_right]
    exact hn
  · intro hn
    have hc := hxcT _ hn
    have e : x * n * x⁻¹ * x = x * n := inv_mul_cancel_right (x * n) x
    have hc' : x * (x * n * x⁻¹) = x * n := hc.trans e
    have key : x * n * x⁻¹ = n := mul_left_cancel hc'
    rw [key] at hn
    exact hn

private theorem case1_arith_A {p a A B C r k : ℕ} (hp0 : 0 < p) (h1 : A * p ^ (k + 1) = C)
    (h2 : C * B = r * p ^ k * (2 ^ a * p)) : A * B = r * 2 ^ a := by
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp0 (k + 1))
  calc A * B * p ^ (k + 1) = (A * p ^ (k + 1)) * B := by ring
    _ = C * B := by rw [h1]
    _ = r * p ^ k * (2 ^ a * p) := h2
    _ = r * 2 ^ a * p ^ (k + 1) := by ring

private theorem case1_arith_B {p a m B C r k : ℕ} (hK : 0 < 2 ^ a * p)
    (h1 : m * (2 ^ a * p) = C) (h2 : C * B = r * p ^ k * (2 ^ a * p)) :
    m * B = r * p ^ k := by
  apply Nat.eq_of_mul_eq_mul_right hK
  calc m * B * (2 ^ a * p) = (m * (2 ^ a * p)) * B := by ring
    _ = C * B := by rw [h1]
    _ = r * p ^ k * (2 ^ a * p) := h2

private theorem case1_arith_C {p a ρ B C r k : ℕ} (hr : 0 < r) (h1 : ρ * r = C)
    (h2 : C * B = r * p ^ k * (2 ^ a * p)) : ρ * B = p ^ (k + 1) * 2 ^ a := by
  apply Nat.eq_of_mul_eq_mul_right hr
  calc ρ * B * r = (ρ * r) * B := by ring
    _ = C * B := by rw [h1]
    _ = r * p ^ k * (2 ^ a * p) := h2
    _ = p ^ (k + 1) * 2 ^ a * r := by ring

private theorem case1_arith_rel {p a ρ : ℕ} (h : ρ * 2 ^ a = 2 ^ a * p) : ρ = p := by
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ a by positivity)
  rw [h]
  ring

private theorem case1_not_two_dvd {p r k : ℕ} (hp2' : Nat.Coprime 2 p) (hr : r ≠ 0)
    (hd : 2 ^ (r.factorization 2) * 2 ∣ r * p ^ k) : False := by
  have hcop : Nat.Coprime (2 ^ (r.factorization 2 + 1)) (p ^ k) :=
    Nat.Coprime.pow _ _ hp2'
  have hpow : 2 ^ (r.factorization 2 + 1) ∣ r * p ^ k := by
    rw [pow_succ (2 : ℕ) (r.factorization 2)]
    exact hd
  have h3 : 2 ^ (r.factorization 2 + 1) ∣ r := Nat.Coprime.dvd_of_dvd_mul_right hcop hpow
  exact Nat.pow_succ_factorization_not_dvd hr Nat.prime_two h3

theorem case1_orders_gen {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {R T Y : Subgroup G} {x : G}
    (hTn : T ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hKn : Y ⊔ zpowers x ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTcard : Nat.card T = p ^ k) (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hxT : x ∉ T) (hxcT : ∀ t ∈ T, x * t = t * x)
    (hY2 : IsPGroup 2 Y) (hxY : x ∈ normalizer (Y : Set G))
    (hYB : CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ R) R) :
    CFSG.ABGLocalTools.IsSylowOf p (T ⊔ zpowers x) ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 Y ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) ∧
    ∀ q : ℕ, q.Prime → q ∣ R.relIndex ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) → q = 2 ∨ q = p := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : 0 < p := hp.pos
  have hp2' : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hRp : ¬ p ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd hp).1 hRcop
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hRne : Nat.card R ≠ 0 := hRpos.ne'
  have hxord : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  obtain ⟨a, ha⟩ := hY2.exists_card_eq
  have ha0 : 0 < 2 ^ a * p := Nat.mul_pos (by positivity) hp0
  have hYp : Nat.Coprime (Nat.card Y) p := by
    rw [ha]
    exact Nat.Coprime.pow_left a hp2'
  have hYx_bot : Y ⊓ zpowers x = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hxord]
    exact hYp
  have hYx_card : Nat.card ↥(Y ⊓ zpowers x) = 1 := Subgroup.card_eq_one.mpr hYx_bot
  have hYK : Nat.card ↥(Y ⊔ zpowers x) = 2 ^ a * p := by
    have h := card_sup_mul_card_inf_of_le_normalizer (N := Y) (K := zpowers x)
      (Subgroup.zpowers_le.mpr hxY)
    rw [hYx_card, mul_one, ha, hxord] at h
    exact h
  have hRT_bot : R ⊓ T = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hTcard]
    exact Nat.Coprime.pow_right k hRcop.symm
  have hRT_card : Nat.card ↥(R ⊓ T) = 1 := Subgroup.card_eq_one.mpr hRT_bot
  have hTR : Nat.card ↥(T ⊔ R) = Nat.card R * p ^ k := by
    have h := card_sup_mul_card_inf_of_le_normalizer (N := R) (K := T) hTn
    rw [hRT_card, mul_one, hTcard, sup_comm] at h
    exact h
  have hTx_card : Nat.card ↥(T ⊓ zpowers x) = 1 := by
    have hdvd : Nat.card ↥(T ⊓ zpowers x) ∣ p := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ zpowers x ≤ zpowers x)
      rwa [hxord] at h
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : T ⊓ zpowers x = zpowers x :=
        Subgroup.eq_of_le_of_card_ge (inf_le_right : T ⊓ zpowers x ≤ zpowers x)
          (le_of_eq (by rw [h1, hxord]))
      have h2 : T ⊓ zpowers x ≤ T := inf_le_left
      rw [heq] at h2
      exact hxT (h2 (Subgroup.mem_zpowers x))
  have hzN : zpowers x ≤ normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr (case1_mem_normalizer_of_comm hxcT)
  have hTx := card_sup_mul_card_inf_of_le_normalizer (N := T) (K := zpowers x) hzN
  rw [hTx_card, mul_one, hTcard, hxord] at hTx
  have hV : Nat.card ↥(T ⊔ zpowers x) = p ^ (k + 1) := by
    rw [hTx]
    ring
  have hH := card_sup_mul_card_inf_of_le_normalizer (N := T ⊔ R) (K := Y ⊔ zpowers x) hKn
  rw [hTR, hYK] at hH
  have hVle : T ⊔ zpowers x ≤ (T ⊔ R) ⊔ (Y ⊔ zpowers x) :=
    sup_le (le_trans le_sup_left le_sup_left) (le_trans le_sup_right le_sup_right)
  have hYle : Y ≤ (T ⊔ R) ⊔ (Y ⊔ zpowers x) := le_trans le_sup_left le_sup_right
  have hRle : R ≤ (T ⊔ R) ⊔ (Y ⊔ zpowers x) := le_trans le_sup_right le_sup_left
  have partA : CFSG.ABGLocalTools.IsSylowOf p (T ⊔ zpowers x)
      ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hVle, IsPGroup.of_card hV, ?_⟩
    intro hdvd
    have hA := Subgroup.relIndex_mul_card (T ⊔ zpowers x) ((T ⊔ R) ⊔ (Y ⊔ zpowers x))
    rw [inf_eq_left.mpr hVle, hV] at hA
    have hAB := case1_arith_A hp0 hA hH
    have hd : p ∣ Nat.card R * 2 ^ a := by
      rw [← hAB]
      exact Dvd.dvd.mul_right hdvd _
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
    · exact hRp h1
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  have partB : CFSG.ABGLocalTools.IsSylowOf 2 Y ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hYle, hY2, ?_⟩
    have hYKr := Subgroup.relIndex_mul_card Y (Y ⊔ zpowers x)
    rw [inf_eq_left.mpr (le_sup_left : Y ≤ Y ⊔ zpowers x), ha, hYK] at hYKr
    have hYr : Y.relIndex (Y ⊔ zpowers x) = p := case1_arith_rel hYKr
    have hsplit := Subgroup.relIndex_mul_relIndex Y (Y ⊔ zpowers x)
      ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) (le_sup_left : Y ≤ Y ⊔ zpowers x) (le_sup_right :
        Y ⊔ zpowers x ≤ (T ⊔ R) ⊔ (Y ⊔ zpowers x))
    rw [hYr] at hsplit
    have hKr := Subgroup.relIndex_mul_card (Y ⊔ zpowers x) ((T ⊔ R) ⊔ (Y ⊔ zpowers x))
    rw [inf_eq_left.mpr (le_sup_right : Y ⊔ zpowers x ≤ (T ⊔ R) ⊔ (Y ⊔ zpowers x)), hYK] at hKr
    have hmB := case1_arith_B ha0 hKr hH
    have hYR : Y ⊓ R ≤ (T ⊔ R) ⊓ (Y ⊔ zpowers x) :=
      le_inf (le_trans inf_le_right le_sup_right) (le_trans inf_le_left le_sup_left)
    have hYRdvd : Nat.card ↥(Y ⊓ R) ∣ Nat.card ↥((T ⊔ R) ⊓ (Y ⊔ zpowers x)) :=
      Subgroup.card_dvd_of_le hYR
    rw [hYB.card_eq] at hYRdvd
    have hm2 : ¬ 2 ∣ (Y ⊔ zpowers x).relIndex ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) := by
      intro h2m
      have hd := mul_dvd_mul hYRdvd h2m
      rw [mul_comm _ ((Y ⊔ zpowers x).relIndex ((T ⊔ R) ⊔ (Y ⊔ zpowers x))), hmB] at hd
      exact case1_not_two_dvd hp2' hRne hd
    rw [← hsplit]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h3).symm
    · exact hm2 h3
  refine ⟨partA, partB, ?_⟩
  intro q hq hqd
  have hR_card := Subgroup.relIndex_mul_card R ((T ⊔ R) ⊔ (Y ⊔ zpowers x))
  rw [inf_eq_left.mpr hRle] at hR_card
  have hRB := case1_arith_C hRpos hR_card hH
  have hqd' : q ∣ p ^ (k + 1) * 2 ^ a := by
    rw [← hRB]
    exact Dvd.dvd.mul_right hqd _
  rcases (Nat.Prime.dvd_mul hq).1 hqd' with h1 | h1
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h1))

theorem case1_orders {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M R T Y : Subgroup G} {x : G}
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hTcard : Nat.card T = p ^ 3) (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hxT : x ∉ T) (hxcT : ∀ t ∈ T, x * t = t * x)
    (hYM : Y ≤ M) (hY2 : IsPGroup 2 Y) (hxY : x ∈ normalizer (Y : Set G))
    (hYB : CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ R) R) :
    CFSG.ABGLocalTools.IsSylowOf p (T ⊔ zpowers x) ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 Y ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) ∧
    ∀ q : ℕ, q.Prime → q ∣ R.relIndex ((T ⊔ R) ⊔ (Y ⊔ zpowers x)) → q = 2 ∨ q = p :=
  case1_orders_gen hp2 (hTM.trans hRn) hRcop
    ((sup_le hYM (Subgroup.zpowers_le.mpr hxM)).trans hNn) hTcard hxp hx1 hxT hxcT hY2 hxY hYB

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
