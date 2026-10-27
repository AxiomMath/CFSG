module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def SporL2Pair (name : TauCeti.SporadicName) (q0 : ℕ) : Prop :=
  (q0 = 4 ∧ (name = .Ru ∨ name = .Suz ∨ name = .Co1 ∨ name = .Fi22 ∨ name = .Fi23 ∨
    name = .Fi24Prime ∨ name = .Th ∨ name = .B ∨ name = .M)) ∨
  (q0 = 5 ∧ (name = .Ly ∨ name = .Th ∨ name = .B ∨ name = .M))

instance (name : TauCeti.SporadicName) (q0 : ℕ) : Decidable (SporL2Pair name q0) := by
  unfold SporL2Pair
  infer_instance

theorem spor_l2_arith : ∀ s : TauCeti.SporadicName, ∀ l ∈ Finset.range 80, l.Prime →
    ∀ j ∈ Finset.range 64, 1 ≤ j → 4 ≤ l ^ j →
      ((l ^ j) ^ 3) ^ 3 - (l ^ j) ^ 3 ∣ 2 * CFSG.AGLEmbedding.sporOrd s → SporL2Pair s (l ^ j) := by
  decide +kernel

theorem two_mul_sporOrd_lt : ∀ s : TauCeti.SporadicName, 2 * CFSG.AGLEmbedding.sporOrd s < 2 ^ 181 := by
  decide +kernel

theorem tits_l2_arith : ∀ l ∈ Finset.range 80, l.Prime →
    ∀ j ∈ Finset.range 64, 1 ≤ j → 4 ≤ l ^ j →
      ((l ^ j) ^ 3) ^ 3 - (l ^ j) ^ 3 ∣ 2 * 17971200 → False := by
  decide +kernel

theorem prime_lt_of_dvd_two_mul_sporOrd (s : TauCeti.SporadicName) {l : ℕ} (hl : l.Prime)
    (h : l ∣ 2 * CFSG.AGLEmbedding.sporOrd s) : l < 80 := by
  rcases (Nat.Prime.dvd_mul hl).1 h with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have hN : CFSG.AGLEmbedding.sporOrd s ≠ 0 := by cases s <;> simp [CFSG.AGLEmbedding.sporOrd]
    exact CFSG.AGLEmbedding.primeFactors_lt s l (Nat.mem_primeFactors.2 ⟨hl, h2, hN⟩)

theorem prime_lt_of_dvd_two_mul_tits {l : ℕ} (hl : l.Prime) (h : l ∣ 2 * 17971200) : l < 80 := by
  have hN : (2 * 17971200 : ℕ) ≠ 0 := by norm_num
  have hmem : l ∈ (2 * 17971200 : ℕ).primeFactors := Nat.mem_primeFactors.2 ⟨hl, h, hN⟩
  have : (2 * 17971200 : ℕ).primeFactors = {2, 3, 5, 13} := by
    norm_num [Nat.primeFactors]
  rw [this] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem isTypeL2_cube_dvd {Y : Type} [Group Y] {r : ℕ} (h : IsTypeL2 r Y) :
    r ^ 3 - r ∣ 2 * Nat.card (Y ⧸ Subgroup.center Y) := by
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card Y h
  generalize Nat.card (Y ⧸ Subgroup.center Y) = N at *
  generalize r ^ 3 = c at *
  rcases Nat.even_or_odd r with he | ho
  · have h1 := (heven he).1
    exact ⟨2, by omega⟩
  · have h1 := hodd ho
    exact ⟨1, by omega⟩

theorem isTypeL2_prime_pow {Y : Type} [Group Y] {r : ℕ} (h : IsTypeL2 r Y) :
    ∃ l n : ℕ, l.Prime ∧ r = l ^ n := by
  obtain ⟨F, hF, hFin, hcard, -⟩ := h
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcardF⟩ := FiniteField.card' F
  refine ⟨p, n, hp, ?_⟩
  rw [← hcard, Nat.card_eq_fintype_card, hcardF]

theorem exists_prime_pow_of_typeL2 {Y : Type} [Group Y] {q0 : ℕ} (hq0 : 4 ≤ q0)
    (h : IsTypeL2 (q0 ^ 3) Y) {M : ℕ} (hM : Nat.card (Y ⧸ Subgroup.center Y) ∣ M) :
    ∃ l j : ℕ, l.Prime ∧ q0 = l ^ j ∧ 1 ≤ j ∧
      ((q0 ^ 3) ^ 3 - q0 ^ 3 ∣ 2 * M) := by
  obtain ⟨l, n, hl, hn⟩ := isTypeL2_prime_pow h
  have hdvd : q0 ∣ l ^ n := by
    rw [← hn]
    exact dvd_pow_self q0 (by norm_num)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 hdvd
  refine ⟨l, j, hl, hj, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hj] at hq0
      simp at hq0
    · exact hj0
  · exact (isTypeL2_cube_dvd h).trans (mul_dvd_mul_left 2 hM)

@[expose] def I1431SporSurv : Prop :=
  ∀ (name : TauCeti.SporadicName) (q0 : ℕ), SporL2Pair name q0 →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier name) →
      ∀ ψ : MulAut S, ψ ^ 3 = 1 → ψ ≠ 1 → ∀ A : Subgroup S, GLAPComponent 3 (fixSub ψ) A →
        ¬ IsTypeL2 (q0 ^ 3) (barOf 3 A)

theorem i1431SporRest_of_surv
    (hOrd : ∀ s : TauCeti.SporadicName,
      Nat.card (NativeSporadic.Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hTits : ∀ (G : Type) [Group G] (p f : ℕ), ReeTitsModel G .Tits p f → Nat.card G = 17971200)
    (h : I1431SporSurv) : I1431SporRest := by
  intro S _ _ hS ψ hψ3 hψ1 A hA q0 hq0 hL2
  have hsec : Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) ∣ Nat.card S :=
    (Subgroup.card_quotient_dvd_card (Subgroup.center (barOf 3 A))).trans
      ((Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥A)).trans
        (Subgroup.card_subgroup_dvd_card A))
  have hdq : q0 ^ 3 ∣ (q0 ^ 3) ^ 3 - q0 ^ 3 :=
    Nat.dvd_sub (dvd_pow_self _ (by norm_num)) (dvd_refl _)
  have key : ∀ (M : ℕ), 0 < M → 2 * M < 2 ^ 181 → ∀ (l j : ℕ), l.Prime → q0 = l ^ j → 1 ≤ j →
      (q0 ^ 3) ^ 3 - q0 ^ 3 ∣ 2 * M → j ∈ Finset.range 64 := by
    intro M hM0 hM l j hl hqj hj1 hdvd
    have h1 : q0 ^ 3 ≤ 2 * M := Nat.le_of_dvd (by positivity) (hdq.trans hdvd)
    have h2 : (2 ^ j) ^ 3 ≤ q0 ^ 3 := by
      rw [hqj]
      exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hl.two_le j) 3
    have h3 : 2 ^ (j * 3) < 2 ^ 181 := by
      rw [pow_mul]
      omega
    have h4 : j * 3 < 181 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
    exact Finset.mem_range.2 (by omega)
  rcases hS with ⟨s, ⟨e⟩⟩ | ⟨p, f, hT⟩
  · have hcard : Nat.card S = CFSG.AGLEmbedding.sporOrd s :=
      (Nat.card_congr e.toEquiv).trans (hOrd s)
    rw [hcard] at hsec
    obtain ⟨l, j, hl, hqj, hj1, hdvd⟩ := exists_prime_pow_of_typeL2 hq0 hL2 hsec
    have hlq : l ∣ q0 ^ 3 := by
      rw [hqj]
      exact dvd_pow (dvd_pow_self l (by omega)) (by norm_num)
    have hlt : l < 80 := prime_lt_of_dvd_two_mul_sporOrd s hl (hlq.trans (hdq.trans hdvd))
    have hjlt : j ∈ Finset.range 64 :=
      key (CFSG.AGLEmbedding.sporOrd s) (by cases s <;> simp [CFSG.AGLEmbedding.sporOrd])
        (two_mul_sporOrd_lt s) l j hl hqj hj1 hdvd
    subst hqj
    have hpair := spor_l2_arith s l (Finset.mem_range.2 hlt) hl j hjlt hj1 hq0 hdvd
    exact h s (l ^ j) hpair S ⟨e⟩ ψ hψ3 hψ1 A hA hL2
  · have hcard : Nat.card S = 17971200 := hTits S p f hT
    rw [hcard] at hsec
    obtain ⟨l, j, hl, hqj, hj1, hdvd⟩ := exists_prime_pow_of_typeL2 hq0 hL2 hsec
    have hlq : l ∣ q0 ^ 3 := by
      rw [hqj]
      exact dvd_pow (dvd_pow_self l (by omega)) (by norm_num)
    have hlt : l < 80 := prime_lt_of_dvd_two_mul_tits hl (hlq.trans (hdq.trans hdvd))
    have hjlt : j ∈ Finset.range 64 :=
      key 17971200 (by norm_num) (by norm_num) l j hl hqj hj1 hdvd
    subst hqj
    exact tits_l2_arith l (Finset.mem_range.2 hlt) hl j hjlt hj1 hq0 hdvd

end CFSG.HardMathSupport.Dickson.Sec6.I1431
