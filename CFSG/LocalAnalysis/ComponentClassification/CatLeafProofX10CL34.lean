module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CCnt
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CL

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem pf_cases {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hdvd : p ^ f ∣ 20160) : (p = 3 ∧ f = 2) ∨ (p = 5 ∧ f = 1) ∨ (p = 7 ∧ f = 1) := by
  have hp20 : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := (dvd_pow_self p (by omega : f ≠ 0)).trans hdvd
  have hpq : ∀ r : ℕ, r.Prime → p ∣ r → p = r := fun r hr h =>
    (Nat.prime_dvd_prime_iff_eq hp hr).mp h
  rcases (Nat.Prime.dvd_mul hp).mp hp20 with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact absurd (hpq 2 Nat.prime_two (hp.dvd_of_dvd_pow h)) hp2
      ·
        obtain rfl := hpq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)
        left
        refine ⟨rfl, ?_⟩
        by_contra hne
        rcases (show f = 1 ∨ 3 ≤ f by omega) with h1 | h1
        · rw [h1] at hq
          omega
        · have := (Nat.pow_dvd_pow 3 h1).trans hdvd
          norm_num at this
    ·
      obtain rfl := hpq 5 (by norm_num) h
      right; left
      refine ⟨rfl, ?_⟩
      by_contra hne
      have := (Nat.pow_dvd_pow 5 (show 2 ≤ f by omega)).trans hdvd
      norm_num at this
  ·
    obtain rfl := hpq 7 (by norm_num) h
    right; right
    refine ⟨rfl, ?_⟩
    by_contra hne
    have := (Nat.pow_dvd_pow 7 (show 2 ≤ f by omega)).trans hdvd
    norm_num at this

theorem l34_arith {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hdvd : p ^ f ∣ 20160) :
    ¬ p ^ (2 * f) ∣ 20160 ∧ padicValNat 2 (p ^ (2 * f) - 1) ≤ 4 ∧ padicValNat 2 f ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : ∀ n : ℕ, n ≠ 0 → ¬ 2 ^ 5 ∣ n → padicValNat 2 n ≤ 4 := fun n hn h => by
    by_contra hlt
    exact h ((padicValNat_dvd_iff_le hn).mpr (by omega))
  rcases pf_cases hp hp2 hf hq hdvd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by norm_num, h5 _ (by norm_num) (by norm_num), ?_⟩
    rw [padicValNat_self]
  · exact ⟨by norm_num, h5 _ (by norm_num) (by norm_num), by simp⟩
  · exact ⟨by norm_num, h5 _ (by norm_num) (by norm_num), by simp⟩

theorem card_of_lieModel_L34 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSL 3 2 2) :
    Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem padicValNat_two_20160 : padicValNat 2 20160 = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

variable {G : Type} [Group G] [Finite G]

theorem l34_component (hO : pPrimeCore 2 G = ⊥) {L : Subgroup G} (hL : IsComponent L)
    (h34 : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 2) :
    padicValNat 2 (Nat.card L) = padicValNat 2 (Nat.card (center L)) + 6 ∧
      ∀ r m : ℕ, r.Prime → r ≠ 2 → r ^ m ∣ Nat.card L → r ^ m ∣ 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := X10CL.card_of_lieModel_L34 h34
  obtain ⟨-, hZ⟩ := X10CC.isPGroup_center_of_isComponent hO hL
  refine ⟨by rw [X10CC.nu_eq_center_add 2 L, hcard, padicValNat_two_20160], ?_⟩
  intro r m hr hr2 hdvd
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (center L), hcard, hn] at hdvd
  have hcop : Nat.Coprime (r ^ m) (2 ^ n) :=
    Nat.Coprime.pow m n ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  exact hcop.dvd_of_dvd_mul_right hdvd

end CFSG.ComponentClassification.CatLeafProof.X10CL
