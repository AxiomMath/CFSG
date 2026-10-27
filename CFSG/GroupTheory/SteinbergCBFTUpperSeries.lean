module

public import CFSG.GroupTheory.SteinbergCBFTCores

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman

section Cores

variable {X : Type*} [Group X]

@[expose] noncomputable def coreAbove (π : Set Nat.Primes) (N : Subgroup X) : Subgroup X :=
  (piCore π (X ⧸ N.normalCore)).comap (QuotientGroup.mk' N.normalCore)

instance coreAbove_normal (π : Set Nat.Primes) (N : Subgroup X) : (coreAbove π N).Normal :=
  Subgroup.Normal.comap inferInstance _

@[expose] def IsPrimeSetNumber (π : Set Nat.Primes) (n : ℕ) : Prop :=
  ∀ r : Nat.Primes, r.val ∣ n → r ∈ π

theorem mem_coreAbove_iff {π : Set Nat.Primes} {N : Subgroup X} {x : X} :
    x ∈ coreAbove π N ↔ (QuotientGroup.mk' N.normalCore x) ∈ piCore π (X ⧸ N.normalCore) :=
  Iff.rfl

theorem le_coreAbove (π : Set Nat.Primes) (N : Subgroup X) [N.Normal] : N ≤ coreAbove π N := by
  intro x hx
  have h1 : QuotientGroup.mk' N.normalCore x = 1 :=
    (QuotientGroup.eq_one_iff x).2 ((normalCore_eq_self N).symm ▸ hx)
  rw [mem_coreAbove_iff, h1]
  exact one_mem _

variable [Finite X]

theorem isPrimeSetNumber_relIndex_coreAbove (π : Set Nat.Primes) (N : Subgroup X) [N.Normal] :
    IsPrimeSetNumber π (N.relIndex (coreAbove π N)) := by
  set K := piCore π (X ⧸ N.normalCore)
  have h1 := relIndex_mul_index (le_coreAbove π N)
  have h2 : (coreAbove π N).index = K.index :=
    index_comap_of_surjective K (QuotientGroup.mk'_surjective _)
  have h3 : N.index = Nat.card K * K.index := by
    rw [card_mul_index, ← index_eq_card, normalCore_eq_self]
  rw [h2, h3] at h1
  have heq : N.relIndex (coreAbove π N) = Nat.card K :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero index_ne_zero_of_finite) h1
  rw [heq]
  exact CFSG.LocalCores.piCore_isPiSubgroup π

omit [Finite X] in
theorem le_coreAbove_of {π : Set Nat.Primes} {N M N' : Subgroup X} [N.Normal] [M.Normal]
    (hN' : N' ≤ N) (hM : IsPrimeSetNumber π (N'.relIndex M)) : M ≤ coreAbove π N := by
  have hle : M.map (QuotientGroup.mk' N.normalCore) ≤ piCore π (X ⧸ N.normalCore) := by
    refine CFSG.LocalCores.le_piCore_of_normal
      (‹M.Normal›.map _ (QuotientGroup.mk'_surjective _)) fun r hr => ?_
    rw [← relIndex_ker, QuotientGroup.ker_mk', normalCore_eq_self] at hr
    exact hM r (hr.trans (relIndex_dvd_of_le_left M hN'))
  exact map_le_iff_le_comap.1 hle

theorem eq_top_of_coreAbove_eq {p : ℕ} [Fact p.Prime]
    (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) {N : Subgroup X} [N.Normal]
    (h1 : coreAbove {q : Nat.Primes | q.val = p} N = N)
    (h2 : coreAbove {q : Nat.Primes | q.val ≠ p} N = N) : N = ⊤ := by
  have hbot : ∀ π : Set Nat.Primes, coreAbove π N = N → piCore π (X ⧸ N.normalCore) = ⊥ := by
    intro π h
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N.normalCore y
    have hx : x ∈ coreAbove π N := hy
    rw [h] at hx
    exact mem_bot.2 ((QuotientGroup.eq_one_iff x).2 ((normalCore_eq_self N).symm ▸ hx))
  have hp := hbot _ h1
  have hp' := hbot _ h2
  have hc := centralizer_pCore_le_pCore (hX.quotient N.normalCore)
    (by rw [pPrimeCore_eq_piCore]; exact hp')
  rw [pCore_eq_piCore, hp] at hc
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' N.normalCore x ∈ (⊥ : Subgroup (X ⧸ N.normalCore)) :=
    hc (by rw [coe_bot, mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff.1 hh]; group)
  rw [mem_bot] at hx
  exact (normalCore_eq_self N) ▸ (QuotientGroup.eq_one_iff x).1 hx

end Cores

section Series

@[expose] def upperPrimes (p n : ℕ) : Set Nat.Primes :=
  if Even n then {q | q.val ≠ p} else {q | q.val = p}

@[expose] noncomputable def upperPSeries (p : ℕ) (X : Type*) [Group X] : ℕ → Subgroup X
  | 0 => ⊥
  | n + 1 => coreAbove (upperPrimes p n) (upperPSeries p X n)

@[expose] noncomputable def pLength (p : ℕ) (X : Type*) [Group X] : ℕ :=
  sInf {n : ℕ | upperPSeries p X (2 * n + 1) = ⊤}

variable {X : Type*} [Group X]

instance upperPSeries_normal (p n : ℕ) : (upperPSeries p X n).Normal := by
  cases n with
  | zero => exact normal_bot
  | succ n => exact coreAbove_normal _ _

@[expose] def HasPSeries (p : ℕ) (X : Type*) [Group X] (n : ℕ) : Prop :=
  ∃ N : ℕ → Subgroup X, N 0 = ⊥ ∧ N n = ⊤ ∧ ∀ i < n, (N (i + 1)).Normal ∧ N i ≤ N (i + 1) ∧
    IsPrimeSetNumber (upperPrimes p i) ((N i).relIndex (N (i + 1)))

theorem le_upperPSeries_of [Finite X] {p : ℕ} {n : ℕ} {N : ℕ → Subgroup X} (h0 : N 0 = ⊥)
    (h : ∀ i < n, (N (i + 1)).Normal ∧ N i ≤ N (i + 1) ∧
      IsPrimeSetNumber (upperPrimes p i) ((N i).relIndex (N (i + 1)))) :
    ∀ i ≤ n, N i ≤ upperPSeries p X i := by
  intro i
  induction i with
  | zero => intro _; rw [h0]; exact bot_le
  | succ i ih =>
    intro hi
    obtain ⟨hn, -, hidx⟩ := h i (by omega)
    exact le_coreAbove_of (ih (by omega)) hidx

theorem upperPSeries_eq_top_of [Finite X] {p n : ℕ} (h : HasPSeries p X n) :
    upperPSeries p X n = ⊤ := by
  obtain ⟨N, h0, htop, h⟩ := h
  exact top_le_iff.1 (htop ▸ le_upperPSeries_of h0 h n le_rfl)

theorem pLength_le_of_hasPSeries [Finite X] {p n : ℕ} (h : HasPSeries p X (2 * n + 1)) :
    pLength p X ≤ n :=
  Nat.sInf_le (upperPSeries_eq_top_of h)

theorem upperPrimes_of_even {p n : ℕ} (h : Even n) :
    upperPrimes p n = {q : Nat.Primes | q.val ≠ p} := by
  simp [upperPrimes, h]

theorem upperPrimes_of_not_even {p n : ℕ} (h : ¬ Even n) :
    upperPrimes p n = {q : Nat.Primes | q.val = p} := by
  simp [upperPrimes, h]

theorem HasPSeries.of_mulEquiv {Y : Type*} [Group Y] {p n : ℕ} (e : X ≃* Y)
    (h : HasPSeries p X n) : HasPSeries p Y n := by
  obtain ⟨N, h0, htop, h⟩ := h
  refine ⟨fun i => (N i).map e.toMonoidHom, by show map _ (N 0) = ⊥; rw [h0, Subgroup.map_bot], by
    show map _ (N n) = ⊤
    rw [htop, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 e.surjective, fun i hi => ?_⟩
  obtain ⟨hn, hle, hidx⟩ := h i hi
  refine ⟨hn.map _ e.surjective, map_mono hle, ?_⟩
  rw [relIndex_map_map_of_injective _ _ e.injective]
  exact hidx

end Series

section Numbers

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem eq_one_of_isPrimeSetNumber_of_coprime {n : ℕ}
    (h1 : IsPrimeSetNumber {q : Nat.Primes | q.val = p} n) (h2 : ¬ p ∣ n) : n = 1 := by
  by_contra hn
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn
  have : r = p := h1 ⟨r, hr⟩ hrn
  exact h2 (this ▸ hrn)

theorem IsPrimeSetNumber.dvd {π : Set Nat.Primes} {m n : ℕ} (h : IsPrimeSetNumber π n)
    (hmn : m ∣ n) : IsPrimeSetNumber π m := fun r hr => h r (hr.trans hmn)

theorem IsPrimeSetNumber.mul {π : Set Nat.Primes} {m n : ℕ} (hm : IsPrimeSetNumber π m)
    (hn : IsPrimeSetNumber π n) : IsPrimeSetNumber π (m * n) := fun r hr =>
  ((Nat.Prime.dvd_mul r.2).1 hr).elim (hm r) (hn r)

theorem isPrimeSetNumber_one (π : Set Nat.Primes) : IsPrimeSetNumber π 1 := fun r hr =>
  absurd (Nat.le_of_dvd one_pos hr) (by have := r.2.two_le; omega)

theorem isPrimeSetNumber_card_of_isPGroup {H : Type*} [Group H] [Finite H] (hH : IsPGroup p H) :
    IsPrimeSetNumber {q : Nat.Primes | q.val = p} (Nat.card H) := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  intro r hr
  rw [hk] at hr
  exact (Nat.prime_dvd_prime_iff_eq r.2 hp.out).1 (r.2.dvd_of_dvd_pow hr)

omit [Finite G] hp in
theorem hasPSeries_five {N₁ N₂ N₃ N₄ : Subgroup G} [N₁.Normal] [N₂.Normal] [N₃.Normal]
    [N₄.Normal] (h₁₂ : N₁ ≤ N₂) (h₂₃ : N₂ ≤ N₃) (h₃₄ : N₃ ≤ N₄)
    (i₁ : IsPrimeSetNumber {q : Nat.Primes | q.val ≠ p} (Nat.card N₁))
    (i₂ : IsPrimeSetNumber {q : Nat.Primes | q.val = p} (N₁.relIndex N₂))
    (i₃ : IsPrimeSetNumber {q : Nat.Primes | q.val ≠ p} (N₂.relIndex N₃))
    (i₄ : IsPrimeSetNumber {q : Nat.Primes | q.val = p} (N₃.relIndex N₄))
    (i₅ : IsPrimeSetNumber {q : Nat.Primes | q.val ≠ p} N₄.index) : HasPSeries p G 5 := by
  refine ⟨fun i => match i with
    | 0 => ⊥ | 1 => N₁ | 2 => N₂ | 3 => N₃ | 4 => N₄ | _ => ⊤, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  · refine ⟨‹N₁.Normal›, bot_le, ?_⟩
    rw [upperPrimes_of_even (by decide)]
    simpa only [relIndex_bot_left] using i₁
  · refine ⟨‹N₂.Normal›, h₁₂, ?_⟩
    rw [upperPrimes_of_not_even (by decide)]
    exact i₂
  · refine ⟨‹N₃.Normal›, h₂₃, ?_⟩
    rw [upperPrimes_of_even (by decide)]
    exact i₃
  · refine ⟨‹N₄.Normal›, h₃₄, ?_⟩
    rw [upperPrimes_of_not_even (by decide)]
    exact i₄
  · refine ⟨normal_top, le_top, ?_⟩
    rw [upperPrimes_of_even (by decide)]
    simpa only [relIndex_top_right] using i₅

theorem hasPSeries_of_isPGroup (hG : IsPGroup p G) : HasPSeries p G 5 :=
  hasPSeries_five (N₁ := ⊥) (N₂ := ⊤) (N₃ := ⊤) (N₄ := ⊤) bot_le le_rfl le_rfl
    (by rw [card_bot]; exact isPrimeSetNumber_one _)
    (by rw [relIndex_bot_left, card_top]; exact isPrimeSetNumber_card_of_isPGroup hG)
    (by rw [relIndex_self]; exact isPrimeSetNumber_one _)
    (by rw [relIndex_self]; exact isPrimeSetNumber_one _)
    (by rw [index_top]; exact isPrimeSetNumber_one _)

end Numbers

section PLengthCount

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

omit [Finite X] hp in
theorem upperPSeries_le_succ (n : ℕ) : upperPSeries p X n ≤ upperPSeries p X (n + 1) :=
  le_coreAbove _ _

omit [Finite X] hp in
theorem upperPSeries_mono : Monotone (upperPSeries p X) :=
  monotone_nat_of_le_succ upperPSeries_le_succ

theorem upperPSeries_ne_of_ne_top (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) (k : ℕ)
    (hk : upperPSeries p X (2 * k + 1) ≠ ⊤) :
    upperPSeries p X (2 * k + 1) ≠ upperPSeries p X (2 * k + 2) := by
  intro h
  apply hk
  have hU := upperPSeries_normal (X := X) p (2 * k + 1)
  have hU0 := upperPSeries_normal (X := X) p (2 * k)
  have h1 : coreAbove {q : Nat.Primes | q.val = p} (upperPSeries p X (2 * k + 1)) =
      upperPSeries p X (2 * k + 1) := by
    have : upperPSeries p X (2 * k + 2) =
        coreAbove (upperPrimes p (2 * k + 1)) (upperPSeries p X (2 * k + 1)) := rfl
    rw [upperPrimes_of_not_even (by simp [parity_simps])] at this
    rw [← this, ← h]
  have h2 : coreAbove {q : Nat.Primes | q.val ≠ p} (upperPSeries p X (2 * k + 1)) =
      upperPSeries p X (2 * k + 1) := by
    have hdef : upperPSeries p X (2 * k + 1) =
        coreAbove (upperPrimes p (2 * k)) (upperPSeries p X (2 * k)) := rfl
    rw [upperPrimes_of_even (by simp)] at hdef
    refine le_antisymm ?_ (le_coreAbove _ _)
    conv_rhs => rw [hdef]
    refine le_coreAbove_of (N := upperPSeries p X (2 * k)) (N' := upperPSeries p X (2 * k)) le_rfl
      ?_
    rw [← relIndex_mul_relIndex _ _ _ (upperPSeries_le_succ _) (le_coreAbove _ _)]
    refine IsPrimeSetNumber.mul ?_ (isPrimeSetNumber_relIndex_coreAbove _ _)
    rw [hdef]
    exact isPrimeSetNumber_relIndex_coreAbove _ _
  exact eq_top_of_coreAbove_eq hX h1 h2

theorem two_pow_le_card_upperPSeries (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) :
    ∀ k : ℕ, (∀ j < k, upperPSeries p X (2 * j + 1) ≠ ⊤) →
      2 ^ k ≤ Nat.card (upperPSeries p X (2 * k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [pow_zero]
    exact Nat.card_pos
  | succ k ih =>
    intro h
    have hk := h k (by omega)
    have hlt : upperPSeries p X (2 * k + 1) < upperPSeries p X (2 * (k + 1) + 1) :=
      lt_of_lt_of_le (lt_of_le_of_ne (upperPSeries_le_succ _) (upperPSeries_ne_of_ne_top hX k hk))
        (upperPSeries_mono (by omega))
    have h2 : 2 ≤ (upperPSeries p X (2 * k + 1)).relIndex (upperPSeries p X (2 * (k + 1) + 1)) := by
      by_contra h3
      have h4 :
          (upperPSeries p X (2 * k + 1)).relIndex (upperPSeries p X (2 * (k + 1) + 1)) = 1 := by
        have := (index_ne_zero_of_finite : ((upperPSeries p X (2 * k + 1)).subgroupOf
          (upperPSeries p X (2 * (k + 1) + 1))).index ≠ 0)
        exact le_antisymm (by omega) (Nat.one_le_iff_ne_zero.2 this)
      exact hlt.not_ge (relIndex_eq_one.1 h4)
    rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hlt.le, pow_succ]
    exact Nat.mul_le_mul (ih fun j hj => h j (by omega)) h2

theorem pLength_eq_ncard_pFactors (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) :
    pLength p X = {k : ℕ | upperPSeries p X (2 * k + 1) ≠ upperPSeries p X (2 * k + 2)}.ncard := by
  have hreach : ∃ j < Nat.card X, upperPSeries p X (2 * j + 1) = ⊤ := by
    by_contra h
    push Not at h
    have h1 := two_pow_le_card_upperPSeries hX (Nat.card X) h
    have h2 := card_le_card_group (upperPSeries p X (2 * Nat.card X + 1))
    have h3 := Nat.lt_two_pow_self (n := Nat.card X)
    omega
  obtain ⟨j, hj, hjtop⟩ := hreach
  have hmem : pLength p X ∈ {n : ℕ | upperPSeries p X (2 * n + 1) = ⊤} := Nat.sInf_mem ⟨j, hjtop⟩
  have hle : pLength p X ≤ j := Nat.sInf_le hjtop
  rw [show {k : ℕ | upperPSeries p X (2 * k + 1) ≠ upperPSeries p X (2 * k + 2)} =
      ↑(Finset.range (pLength p X)) from ?_, Set.ncard_coe_finset, Finset.card_range]
  ext k
  simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
  constructor
  · intro hk
    by_contra hk'
    push Not at hk'
    have htop : upperPSeries p X (2 * k + 1) = ⊤ :=
      top_le_iff.1 (hmem.symm.le.trans (upperPSeries_mono (by omega)))
    have htop' : upperPSeries p X (2 * k + 2) = ⊤ :=
      top_le_iff.1 (htop.symm.le.trans (upperPSeries_le_succ _))
    exact hk (htop.trans htop'.symm)
  · intro hk
    refine upperPSeries_ne_of_ne_top hX k fun h => ?_
    exact absurd (Nat.sInf_le h) (by change ¬ pLength p X ≤ k; omega)

end PLengthCount

end CFSG.GroupTheory.FT63ChII
