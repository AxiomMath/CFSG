module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve
import all CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.HardMathSupport.Malle.Coordinator

def sieveFactors : List (ℕ × ℕ) :=
  [(2, 55), (3, 2), (11, 2), (13, 1), (31, 2), (41, 2), (61, 1), (331, 1), (1321, 1)]

def divsOf : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, e) :: t => (List.range (e + 1)).flatMap fun k => (divsOf t).map (p ^ k * ·)

theorem mem_divsOf : ∀ (l : List (ℕ × ℕ)), (∀ pe ∈ l, pe.1.Prime) → ∀ n : ℕ,
    n ∣ (l.map fun pe => pe.1 ^ pe.2).prod → n ∈ divsOf l
  | [], _, n, hn => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at hn
    simp [divsOf, hn]
  | (p, e) :: t, hp, n, hn => by
    simp only [List.map_cons, List.prod_cons] at hn
    obtain ⟨k₁, k₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.1 hn
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (hp (p, e) (by simp))).1 h₁
    have := mem_divsOf t (fun pe h => hp pe (List.mem_cons_of_mem _ h)) k₂ h₂
    simp only [divsOf, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨i, by omega, k₂, this, rfl⟩

def valOK (n d p : ℕ) : Bool :=
  (List.range 200).all fun a =>
    !decide (p ^ a ∣ 60000 * n ∧ ¬ p ^ (a + 1) ∣ 60000 * n) ||
      (List.range (p ^ a + 1)).any fun s =>
        decide (s ∣ p ^ a ∧ s ∣ 2400 * d ∧ p ^ a % 5 = s % 5)

def cycOK (n p : ℕ) : Bool :=
  !decide (p ∣ n) ||
    (List.range (cyclicCentralizerBound p + 1)).any fun c =>
      decide (p ∣ c ∧ c ∣ cyclicCentralizerBound p) &&
        (List.range p).any fun r =>
          decide (r ∣ p - 1 ∧ c * r ∣ reeF4Order ∧ reeF4Order / (c * r) % p = 1) &&
            (List.range (c * r + 1)).any fun m =>
              decide (p ∣ m ∧ m ∣ c * r ∧ m ∣ 60000 * n ∧ 60000 * n / m % p = 1)

def pass (n d : ℕ) : Bool :=
  decide (n % 625 = 1) && decide (d ∣ 14976) && decide (d ∣ n) && decide (d % 25 = 1) &&
    decide (n % 3125 = (1 + 25 * (d - 1)) % 3125) && valOK n d 3 && valOK n d 13 &&
    [13, 61, 331, 1321].all (cycOK n)

def divs14976 : List ℕ :=
  [1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18, 24, 26, 32, 36, 39, 48, 52, 64, 72, 78, 96, 104, 117,
    128, 144, 156, 192, 208, 234, 288, 312, 384, 416, 468, 576, 624, 832, 936, 1152, 1248, 1664,
    1872, 2496, 3744, 4992, 7488, 14976]

theorem mem_divs14976 {d : ℕ} (h : d ∣ 14976) : d ∈ divs14976 := by
  have hd : d < 14977 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) h)
  have key : (List.range 14977).all
      (fun d => !decide (d ∣ 14976) || decide (d ∈ divs14976)) = true := by decide +kernel
  have := List.all_eq_true.1 key d (List.mem_range.2 hd)
  simpa [h] using this

def checkOne (n : ℕ) : Bool :=
  !decide (n % 625 = 1) ||
    divs14976.all fun d => !pass n d || decide (n = 1 ∨ n = 9381251)

theorem sieve_check : (divsOf sieveFactors).all checkOne = true := by
  decide +kernel

theorem valOK_of {n d p : ℕ} (hp : 0 < p)
    (H : ∀ a : ℕ, p ^ a ∣ 60000 * n → ¬ p ^ (a + 1) ∣ 60000 * n →
      ∃ s : ℕ, s ∣ p ^ a ∧ s ∣ 2400 * d ∧ p ^ a % 5 = s % 5) :
    valOK n d p = true := by
  simp only [valOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq]
  intro a _
  by_cases h : p ^ a ∣ 60000 * n ∧ ¬ p ^ (a + 1) ∣ 60000 * n
  · right
    obtain ⟨s, hs1, hs2, hs3⟩ := H a h.1 h.2
    exact ⟨s, by
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (pow_pos hp a) hs1), hs1, hs2, hs3⟩
  · left
    exact h

theorem cycOK_of {n p : ℕ} (hp : 2 ≤ p) (hcb : 0 < cyclicCentralizerBound p)
    (H : p ∣ n → ∃ c r m : ℕ, p ∣ c ∧ c ∣ cyclicCentralizerBound p ∧ r ∣ p - 1 ∧
        c * r ∣ reeF4Order ∧ reeF4Order / (c * r) % p = 1 ∧ p ∣ m ∧ m ∣ c * r ∧
        m ∣ 60000 * n ∧ 60000 * n / m % p = 1) :
    cycOK n p = true := by
  unfold cycOK
  by_cases hpn : p ∣ n
  · obtain ⟨c, r, m, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := H hpn
    have hc : 0 < c := Nat.pos_of_ne_zero fun h => by
      subst h; exact absurd (zero_dvd_iff.1 h2) hcb.ne'
    have hr : 0 < r := Nat.pos_of_ne_zero fun h => by
      subst h
      have := zero_dvd_iff.1 h3
      omega
    have hcr : 0 < c * r := Nat.mul_pos hc hr
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true,
      List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    right
    refine ⟨c, Nat.lt_succ_of_le (Nat.le_of_dvd hcb h2), ⟨h1, h2⟩, r, ?_, ⟨h3, h4, h5⟩, m, ?_,
      ⟨h6, h7, h8, h9⟩⟩
    · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) h3) (by omega)
    · exact Nat.lt_succ_of_le (Nat.le_of_dvd hcr h7)
  · simp [hpn]

theorem reeF4IndexSieve_proof : ReeF4IndexSieve := by
  intro n d hn h625 hd14976 hdn hd25 h3125 hval hcyc
  have hprod : (sieveFactors.map fun pe => pe.1 ^ pe.2).prod = reeF4SylowIndex := by
    decide +kernel
  have hprime : ∀ pe ∈ sieveFactors, pe.1.Prime := by
    intro pe h
    simp only [sieveFactors, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hmem : n ∈ divsOf sieveFactors := mem_divsOf _ hprime n (by rw [hprod]; exact hn)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; omega
  have hdlt : d ∈ divs14976 := mem_divs14976 hd14976
  have hone := List.all_eq_true.1 sieve_check n hmem
  unfold checkOne at hone
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true,
    decide_eq_true_eq] at hone
  rcases hone with hone | hone
  · exact absurd h625 hone
  have := hone d hdlt
  rcases this with hpass | hres
  · exfalso
    have h3 : valOK n d 3 = true := valOK_of (by norm_num) fun a h1 h2 =>
      hval 3 (by simp) a h1 h2
    have h13 : valOK n d 13 = true := valOK_of (by norm_num) fun a h1 h2 =>
      hval 13 (by simp) a h1 h2
    have hc : [13, 61, 331, 1321].all (cycOK n) = true := by
      rw [List.all_eq_true]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      have hpm : p ∈ ({13, 61, 331, 1321} : Finset ℕ) := by simp [hp]
      refine cycOK_of ?_ ?_ (hcyc p hpm)
      <;> rcases hp with rfl | rfl | rfl | rfl <;> simp [cyclicCentralizerBound]
    have hp : pass n d = true := by
      simp only [pass, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨h625, hd14976⟩, hdn⟩, hd25⟩, h3125⟩, h3⟩, h13⟩, hc⟩
    rw [hp] at hpass
    exact absurd hpass (by simp)
  · exact hres

end CFSG.HardMathSupport.Malle.LocalAction
