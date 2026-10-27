module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open MulAction

variable {Q Ω : Type} [Group Q] [MulAction Q Ω]

theorem sec12S8Mod_burn_conj (a c : Q) :
    Nat.card (fixedBy Ω (c * a * c⁻¹)) = Nat.card (fixedBy Ω a) := by
  rw [← smul_fixedBy]
  exact Nat.card_image_of_injective (MulAction.injective c) _

theorem sec12S8Mod_burn_sylow [Finite Q] (hQ : Nat.card Q = 20160) (h : Q)
    (hh : orderOf h = 3) : ∃ P : Subgroup Q, h ∈ P ∧ Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.factorization 20160) 3 = 2 := by
    rw [show 20160 = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime (3 ^ 2) 2240),
      Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2240), add_zero]
  have hzp : IsPGroup 3 (Subgroup.zpowers h) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hh]
    norm_num
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (p := 3) hzp
  refine ⟨(P : Subgroup Q), hP (Subgroup.mem_zpowers h), ?_⟩
  rw [Sylow.card_eq_multiplicity P, hQ, hfac]
  norm_num

theorem sec12S8Mod_burn_dvd [Finite Ω] (P : Subgroup Q) [Fintype P] :
    Nat.card P ∣ ∑ p : P, Nat.card (fixedBy Ω (p : Q)) := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : ∀ p : P, Fintype (fixedBy Ω (p : P)) := fun p => Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := P) (X := Ω)
  have hsum : (∑ p : P, Nat.card (fixedBy Ω (p : Q))) =
      ∑ p : P, Nat.card (fixedBy Ω (p : P)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Nat.card_congr (Equiv.refl _)
  rw [hsum]
  refine ⟨Fintype.card (Quotient (orbitRel P Ω)), ?_⟩
  rw [Nat.card_eq_fintype_card, mul_comm, ← hburn]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.card_eq_fintype_card]

theorem sec12S8Mod_burn_sum (P : Type) [Group P] [Fintype P] (hP : Fintype.card P = 9)
    (f : P → ℕ) (h1 : f 1 = 256) (h3 : ∀ p : P, orderOf p = 3 → f p = 16)
    (hpow : ∀ p : P, ∃ k : ℕ, f p = 2 ^ k)
    (hgen : ∀ p p' : P, Subgroup.zpowers p = Subgroup.zpowers p' → f p = f p') :
    ¬ 9 ∣ ∑ p : P, f p := by
  classical
  have hcases : ∀ p : P, orderOf p = 1 ∨ orderOf p = 3 ∨ orderOf p = 9 := by
    intro p
    have hd : orderOf p ∣ 3 ^ 2 := by
      simpa [Nat.card_eq_fintype_card, hP] using orderOf_dvd_natCard p
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    interval_cases k
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right; simpa using hk
  intro hdvd
  by_cases hB : ∃ p0 : P, orderOf p0 = 9
  · obtain ⟨p0, hp0⟩ := hB
    haveI : IsCyclic P :=
      isCyclic_of_orderOf_eq_card p0 (by rw [hp0, Nat.card_eq_fintype_card, hP])
    obtain ⟨k, hk⟩ := hpow p0
    have hdvd3 : 3 ∣ Fintype.card P := by norm_num [hP]
    have hdvd9 : 9 ∣ Fintype.card P := by norm_num [hP]
    have hcnt3 : (Finset.univ.filter (fun p : P => orderOf p = 3)).card = 2 := by
      rw [IsCyclic.card_orderOf_eq_totient (α := P) (d := 3) hdvd3,
        Nat.totient_prime Nat.prime_three]
    have hcnt9 : (Finset.univ.filter (fun p : P => orderOf p = 9)).card = 6 := by
      rw [IsCyclic.card_orderOf_eq_totient (α := P) (d := 9) hdvd9]
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
        Nat.totient_prime_pow Nat.prime_three (n := 2) (by norm_num)]
      norm_num
    have hf9 : ∀ p ∈ Finset.univ.filter (fun p : P => orderOf p = 9), f p = f p0 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine hgen p p0 ?_
      have hp_top : Subgroup.zpowers p = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by
          rw [Nat.card_zpowers, hp.2, Nat.card_eq_fintype_card, hP])
      have hp0_top : Subgroup.zpowers p0 = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by
          rw [Nat.card_zpowers, hp0, Nat.card_eq_fintype_card, hP])
      exact hp_top.trans hp0_top.symm
    have horders : ∀ p : P, orderOf p ∈ ({1, 3, 9} : Finset ℕ) := by
      intro p
      rcases hcases p with h | h | h <;> simp [h]
    have hinner1 : (∑ p ∈ Finset.univ.filter (fun p : P => orderOf p = 1), f p) = 256 := by
      have hfilter : Finset.univ.filter (fun p : P => orderOf p = 1) = {1} := by
        ext p
        simp [orderOf_eq_one_iff]
      rw [hfilter, Finset.sum_singleton, h1]
    have hinner3 : (∑ p ∈ Finset.univ.filter (fun p : P => orderOf p = 3), f p) = 2 * 16 := by
      rw [Finset.sum_const_nat (fun p hp => h3 p (Finset.mem_filter.1 hp).2), hcnt3]
    have hinner9 : (∑ p ∈ Finset.univ.filter (fun p : P => orderOf p = 9), f p) = 6 * f p0 := by
      rw [Finset.sum_const_nat hf9, hcnt9]
    have hsum : ∑ p : P, f p = 288 + 6 * 2 ^ k := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := orderOf) (t := ({1, 3, 9} : Finset ℕ))
            (fun p _ => horders p)]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [hinner1, hinner3, hinner9, hk]
      ring
    rw [hsum] at hdvd
    have h9_288 : 9 ∣ 288 := by norm_num
    obtain ⟨m, hm⟩ := hdvd
    obtain ⟨j, hj⟩ := h9_288
    have h6 : 9 ∣ 6 * 2 ^ k := ⟨m - j, by omega⟩
    have h3' : 3 ∣ 2 ^ (k + 1) := by
      have hmul : 3 * 3 ∣ 3 * 2 ^ (k + 1) := by
        rw [show 3 * 2 ^ (k + 1) = 6 * 2 ^ k by ring]
        simpa using h6
      exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hmul
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
  · have h9 : ∀ p : P, orderOf p ≠ 9 := fun p h => hB ⟨p, h⟩
    have horder3 : ∀ p : P, p ≠ 1 → orderOf p = 3 := by
      intro p hp1
      rcases hcases p with h | h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hp1
      · exact h
      · exact absurd h (h9 p)
    have hsum : ∑ p : P, f p = 384 := by
      have hf : ∀ p ∈ Finset.univ.erase (1 : P), f p = 16 := by
        intro p hp
        rw [Finset.mem_erase] at hp
        exact h3 p (horder3 p hp.1)
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (1 : P))]
      rw [h1, Finset.sum_const_nat hf, Finset.card_erase_of_mem (Finset.mem_univ (1 : P)),
        Finset.card_univ, hP]
    rw [hsum] at hdvd
    norm_num at hdvd

theorem sec12S8Mod_burn [Finite Q] [Finite Ω] (hQ : Nat.card Q = 20160) (hΩ : Nat.card Ω = 256)
    (hconj : ∀ a b : Q, orderOf a = 3 → orderOf b = 3 → IsConj a b) (h : Q)
    (hh : orderOf h = 3) (hfix : Nat.card (fixedBy Ω h) = 16)
    (hpow : ∀ q : Q, ∃ k : ℕ, Nat.card (fixedBy Ω q) = 2 ^ k) : False := by
  classical
  obtain ⟨P, _hhP, hPcard⟩ := sec12S8Mod_burn_sylow hQ h hh
  haveI : Fintype P := Fintype.ofFinite P
  let f : P → ℕ := fun p => Nat.card (fixedBy Ω (p : Q))
  have hf1 : f 1 = 256 := by
    change Nat.card (fixedBy Ω (((1 : P) : Q))) = 256
    rw [Subgroup.coe_one, MulAction.fixedBy_one_eq_univ, Nat.card_univ, hΩ]
  have hf3 : ∀ p : P, orderOf p = 3 → f p = 16 := by
    intro p hp
    change Nat.card (fixedBy Ω (p : Q)) = 16
    have hpQ : orderOf (p : Q) = 3 := by rw [Subgroup.orderOf_coe, hp]
    obtain ⟨c, hc⟩ := isConj_iff.1 (hconj (p : Q) h hpQ hh)
    rw [← hfix, ← hc]
    exact (sec12S8Mod_burn_conj (p : Q) c).symm
  have hfpow : ∀ p : P, ∃ k : ℕ, f p = 2 ^ k := by
    intro p
    change ∃ k : ℕ, Nat.card (fixedBy Ω (p : Q)) = 2 ^ k
    exact hpow (p : Q)
  have hgen : ∀ p p' : P, Subgroup.zpowers p = Subgroup.zpowers p' → f p = f p' := by
    intro p p' hzp
    have hset : fixedBy Ω (p : Q) = fixedBy Ω (p' : Q) := by
      apply Set.Subset.antisymm
      · intro ω hω
        have hp' : p' ∈ Subgroup.zpowers p := by rw [hzp]; exact Subgroup.mem_zpowers p'
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hp'
        have hcoe : (p' : Q) = (p : Q) ^ n := by rw [← hn, Subgroup.coe_zpow]
        rw [hcoe]
        exact MulAction.mem_fixedBy_zpow hω n
      · intro ω hω
        have hp : p ∈ Subgroup.zpowers p' := by rw [← hzp]; exact Subgroup.mem_zpowers p
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hp
        have hcoe : (p : Q) = (p' : Q) ^ n := by rw [← hn, Subgroup.coe_zpow]
        rw [hcoe]
        exact MulAction.mem_fixedBy_zpow hω n
    change Nat.card (fixedBy Ω (p : Q)) = Nat.card (fixedBy Ω (p' : Q))
    rw [hset]
  have hP9 : Fintype.card P = 9 := by rw [← Nat.card_eq_fintype_card]; exact hPcard
  have hnot : ¬ 9 ∣ ∑ p : P, f p := sec12S8Mod_burn_sum P hP9 f hf1 hf3 hfpow hgen
  have hdvd : 9 ∣ ∑ p : P, f p := by
    have hb := sec12S8Mod_burn_dvd (Ω := Ω) P
    rw [hPcard] at hb
    exact hb
  exact hnot hdvd

end CFSG.OddStandard.SmallF3.Omega
