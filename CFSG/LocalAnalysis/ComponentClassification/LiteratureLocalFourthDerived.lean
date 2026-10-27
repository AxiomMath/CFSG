module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ComponentClassification.LiteratureLocal

open Equiv

open scoped commutatorElement

theorem derivedSeries_perm_three_eq_bot {α : Type*} [Fintype α] [DecidableEq α]
    (h : Nat.card α = 4) : derivedSeries (Perm α) 3 = ⊥ := by
  have h1 : derivedSeries (Perm α) 1 ≤ alternatingGroup α := by
    rw [derivedSeries_one]
    exact alternatingGroup.commutator_perm_le
  have h2 : derivedSeries (Perm α) 2 ≤
      (alternatingGroup.kleinFour α).map (alternatingGroup α).subtype := by
    rw [derivedSeries_succ, alternatingGroup.kleinFour_eq_commutator h,
      Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono h1 h1
  rw [derivedSeries_succ, ← le_bot_iff]
  refine (Subgroup.commutator_mono h2 h2).trans ?_
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have := mul_comm_of_exponent_two (alternatingGroup.exponent_kleinFour_of_card_eq_four h)
    (⟨b, hb⟩ : alternatingGroup.kleinFour α) ⟨a, ha⟩
  simpa using
    congrArg (fun g : alternatingGroup.kleinFour α => ((g : alternatingGroup α) : Perm α)) this

variable {C : Type*} [Group C]

theorem derivedSeries_succ_le (n : ℕ) : derivedSeries C (n + 1) ≤ derivedSeries C n := by
  rw [derivedSeries_succ]
  exact Subgroup.commutator_le_left _ _

theorem commutator_le_centralizer_of_conj_mem_zpowers {X N : Subgroup C} (hN : N.Normal)
    (h : ∀ x ∈ X, ∀ v ∈ N, x * v * x⁻¹ ∈ Subgroup.zpowers v) :
    ⁅X, X⁆ ≤ Subgroup.centralizer (N : Set C) := by
  rw [Subgroup.commutator_le]
  intro c hc d hd
  have key : ∀ u ∈ N, (c * d) * u * (c * d)⁻¹ = (d * c) * u * (d * c)⁻¹ := by
    intro u hu
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (h d hd u hu)
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (h c hc u hu)
    calc (c * d) * u * (c * d)⁻¹ = c * (d * u * d⁻¹) * c⁻¹ := by group
      _ = c * u ^ s * c⁻¹ := by rw [hs]
      _ = (c * u * c⁻¹) ^ s := conj_zpow.symm
      _ = u ^ (t * s) := by rw [← ht, zpow_mul]
      _ = (d * u * d⁻¹) ^ t := by rw [← hs, ← zpow_mul, mul_comm]
      _ = d * u ^ t * d⁻¹ := conj_zpow
      _ = d * (c * u * c⁻¹) * d⁻¹ := by rw [ht]
      _ = (d * c) * u * (d * c)⁻¹ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hu : (d * c)⁻¹ * v * (d * c) ∈ N := by
    simpa [mul_assoc] using hN.conj_mem v hv (d * c)⁻¹
  have hconj : ⁅c, d⁆ * v * ⁅c, d⁆⁻¹ = v := by
    rw [commutatorElement_def]
    calc c * d * c⁻¹ * d⁻¹ * v * (c * d * c⁻¹ * d⁻¹)⁻¹
        = (c * d) * ((d * c)⁻¹ * v * (d * c)) * (c * d)⁻¹ := by group
      _ = (d * c) * ((d * c)⁻¹ * v * (d * c)) * (d * c)⁻¹ := key _ hu
      _ = v := by group
  calc v * ⁅c, d⁆ = ⁅c, d⁆ * v * ⁅c, d⁆⁻¹ * ⁅c, d⁆ := by rw [hconj]
    _ = ⁅c, d⁆ * v := by group

theorem conj_mem_zpowers_of_isCyclic {N : Subgroup C} (hN : N.Normal) (hcyc : IsCyclic N)
    (x : C) {v : C} (hv : v ∈ N) : x * v * x⁻¹ ∈ Subgroup.zpowers v := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x * g * x⁻¹, hN.conj_mem g g.2 x⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨v, hv⟩)
  have hm' : (g : C) ^ m = x * g * x⁻¹ := by simpa using congrArg Subtype.val hm
  have hj' : (g : C) ^ j = v := by simpa using congrArg Subtype.val hj
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  rw [← hj', ← zpow_mul, mul_comm j m, zpow_mul, hm', conj_zpow]

theorem derivedSeries_four_le_centralizer_of_isCyclic {N : Subgroup C} (hN : N.Normal)
    (hcyc : IsCyclic N) : derivedSeries C 4 ≤ Subgroup.centralizer (N : Set C) := by
  have h1 : derivedSeries C 1 ≤ Subgroup.centralizer (N : Set C) := by
    rw [derivedSeries_one, commutator_def]
    exact commutator_le_centralizer_of_conj_mem_zpowers hN
      (fun x _ v hv => conj_mem_zpowers_of_isCyclic hN hcyc x hv)
  exact (derivedSeries_succ_le 3).trans ((derivedSeries_succ_le 2).trans
    ((derivedSeries_succ_le 1).trans h1))

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {g v : C} (hg : g ^ 3 = 1)
    (hv : v ∈ Subgroup.zpowers g) : v = 1 ∨ v = g ∨ v = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hg' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  rw [zpow_eq_zpow_emod k hg']
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk]
  · left
    exact zpow_zero g
  · right; left
    exact zpow_one g
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact hg'

abbrev NLines (N : Subgroup C) : Type _ :=
  {L : Subgroup C // ∃ v ∈ N, v ≠ 1 ∧ Subgroup.zpowers v = L}

theorem card_nLines_of_card_nine [Finite C] {N : Subgroup C} (hcard : Nat.card N = 9)
    (h3 : ∀ v ∈ N, v ^ 3 = 1) : Nat.card (NLines N) = 4 := by
  classical
  let _ := Fintype.ofFinite C
  let s : Finset C := (Finset.univ.filter fun v => v ∈ N).erase 1
  have hmem : ∀ v, v ∈ s ↔ v ∈ N ∧ v ≠ 1 := by
    intro v
    simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have hs : s.card = 8 := by
    have h9 : (Finset.univ.filter fun v => v ∈ N).card = 9 := by
      rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_erase_of_mem (by simp), h9]
  have hfib : ∀ L ∈ s.image Subgroup.zpowers,
      (s.filter fun v => Subgroup.zpowers v = L).card = 2 := by
    intro L hL
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hv₀N, hv₀1⟩ := (hmem v₀).mp hv₀
    have hne : v₀ ≠ v₀⁻¹ := by
      intro h
      apply hv₀1
      have hsq : v₀ ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h]; exact mul_inv_cancel v₀
      calc v₀ = v₀ ^ 3 * (v₀ ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3 v₀ hv₀N, hsq, inv_one, mul_one]
    have hfilter : (s.filter fun v => Subgroup.zpowers v = Subgroup.zpowers v₀) =
        {v₀, v₀⁻¹} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hmem]
      constructor
      · rintro ⟨⟨-, hv1⟩, hvz⟩
        have hvmem : v ∈ Subgroup.zpowers v₀ := hvz ▸ Subgroup.mem_zpowers v
        rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers (h3 v₀ hv₀N) hvmem with h | h | h
        · exact absurd h hv1
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨⟨hv₀N, hv₀1⟩, rfl⟩
        · exact ⟨⟨N.inv_mem hv₀N, inv_ne_one.mpr hv₀1⟩, Subgroup.zpowers_inv⟩
    rw [hfilter, Finset.card_pair hne]
  have hsum := Finset.card_eq_sum_card_image Subgroup.zpowers s
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hs] at hsum
  have himage : (s.image Subgroup.zpowers).card = 4 := by omega
  rw [← himage, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun L => ?_
  simp only [Finset.mem_image, hmem, and_assoc]

variable {N : Subgroup C}

@[expose] def lineConj (hN : N.Normal) (x : C) (L : NLines N) : NLines N :=
  ⟨L.1.map (MulAut.conj x).toMonoidHom, by
    obtain ⟨v, hvN, hv1, hvL⟩ := L.2
    refine ⟨x * v * x⁻¹, hN.conj_mem v hvN x, ?_, ?_⟩
    · intro h
      apply hv1
      calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [← hvL, MonoidHom.map_zpowers]
      rfl⟩

theorem lineConj_val (hN : N.Normal) (x : C) (L : NLines N) :
    (lineConj hN x L).1 = L.1.map (MulAut.conj x).toMonoidHom :=
  rfl

theorem lineConj_mul (hN : N.Normal) (x y : C) (L : NLines N) :
    lineConj hN (x * y) L = lineConj hN x (lineConj hN y L) := by
  apply Subtype.ext
  simp only [lineConj_val, Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem lineConj_one (hN : N.Normal) (L : NLines N) : lineConj hN 1 L = L := by
  apply Subtype.ext
  rw [lineConj_val]
  have : (MulAut.conj (1 : C)).toMonoidHom = MonoidHom.id C := by
    ext z
    simp
  rw [this, Subgroup.map_id]

@[expose] def linePerm (hN : N.Normal) : C →* Perm (NLines N) where
  toFun x :=
    { toFun := lineConj hN x
      invFun := lineConj hN x⁻¹
      left_inv := fun L => by rw [← lineConj_mul, inv_mul_cancel, lineConj_one]
      right_inv := fun L => by rw [← lineConj_mul, mul_inv_cancel, lineConj_one] }
  map_one' := by
    ext L : 1
    exact lineConj_one hN L
  map_mul' x y := by
    ext L : 1
    exact lineConj_mul hN x y L

theorem derivedSeries_four_le_centralizer_of_exponent_three [Finite C] (hN : N.Normal)
    (hcard : Nat.card N = 9) (h3 : ∀ v ∈ N, v ^ 3 = 1) :
    derivedSeries C 4 ≤ Subgroup.centralizer (N : Set C) := by
  classical
  let _ : Fintype (NLines N) := Fintype.ofFinite _
  have hψ : ∀ x ∈ derivedSeries C 3, linePerm hN x = 1 := by
    intro x hx
    have := map_derivedSeries_le_derivedSeries (linePerm hN) 3 (Subgroup.mem_map_of_mem _ hx)
    rwa [derivedSeries_perm_three_eq_bot (card_nLines_of_card_nine hcard h3),
      Subgroup.mem_bot] at this
  rw [derivedSeries_succ]
  apply commutator_le_centralizer_of_conj_mem_zpowers hN
  intro x hx v hv
  by_cases hv1 : v = 1
  · subst hv1
    simp
  · have hL := congrArg (fun σ : Perm (NLines N) => (σ ⟨Subgroup.zpowers v, v, hv, hv1, rfl⟩).1)
      (hψ x hx)
    change (Subgroup.zpowers v).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers v at hL
    rw [← hL]
    exact ⟨v, Subgroup.mem_zpowers v, by simp⟩

theorem exists_normal_le_card_prime [Finite C] {V : Subgroup C} (hVn : V.Normal) {q d : ℕ}
    [hq : Fact q.Prime] (hqV : q ∣ Nat.card V) (hVd : Nat.card V ∣ q * d) (hd : ¬ q ∣ d)
    (hsyl : ∀ e, e ∣ d → e % q = 1 → e = 1) :
    ∃ N : Subgroup C, N ≤ V ∧ N.Normal ∧ Nat.card N = q := by
  obtain ⟨P⟩ : Nonempty (Sylow q V) := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hindex := (P : Subgroup V).index_mul_card
  have hk1 : k = 1 := by
    have hnot := P.not_dvd_index
    rcases Nat.lt_or_ge k 1 with hk0 | hk2
    · have : k = 0 := by omega
      subst this
      rw [hk, pow_zero, mul_one] at hindex
      exact absurd (hindex ▸ hqV) hnot
    · by_contra hk1
      have h2 : q ^ 2 ∣ q * d := by
        calc q ^ 2 ∣ q ^ k := Nat.pow_dvd_pow q (by omega)
          _ = Nat.card P := hk.symm
          _ ∣ Nat.card V := Subgroup.card_subgroup_dvd_card _
          _ ∣ q * d := hVd
      rw [pow_two] at h2
      exact hd (Nat.dvd_of_mul_dvd_mul_left hq.out.pos h2)
  rw [hk1, pow_one] at hk
  rw [hk] at hindex
  have hindex_dvd : (P : Subgroup V).index ∣ d := by
    have hVd' : (P : Subgroup V).index * q ∣ d * q := by
      rw [hindex, mul_comm d]
      exact hVd
    exact Nat.dvd_of_mul_dvd_mul_right hq.out.pos hVd'
  have hmod : Nat.card (Sylow q V) % q = 1 := by
    have h := card_sylow_modEq_one q V
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hq.out.one_lt] at h
  have hcount : Nat.card (Sylow q V) = 1 :=
    hsyl _ ((Sylow.card_dvd_index P).trans hindex_dvd) hmod
  have : Subsingleton (Sylow q V) := (Nat.card_eq_one_iff_unique.mp hcount).1
  refine ⟨(P : Subgroup V).map V.subtype, Subgroup.map_subtype_le _, inferInstance, ?_⟩
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact hk

theorem derivedSeries_four_le_centralizer_of_card_dvd_nine [Finite C] {V : Subgroup C}
    (hVn : V.Normal) (h9 : Nat.card V ∣ 9) :
    derivedSeries C 4 ≤ Subgroup.centralizer (V : Set C) := by
  by_cases hcyc : IsCyclic V
  · exact derivedSeries_four_le_centralizer_of_isCyclic hVn hcyc
  have h9' : Nat.card V ∣ 3 ^ 2 := h9
  obtain ⟨i, hi, hiV⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9'
  have hcard : Nat.card V = 9 := by
    interval_cases i
    · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp (by simpa using hiV)).1
      exact absurd (inferInstance : IsCyclic V) hcyc
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact absurd (isCyclic_of_prime_card (p := 3) (by simpa using hiV)) hcyc
    · simpa using hiV
  have h3 : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    have hdvd : orderOf (⟨v, hv⟩ : V) ∣ 3 ^ 2 := (orderOf_dvd_natCard _).trans h9'
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj2 : j ≤ 1 := by
      by_contra hj2
      have hj2 : j = 2 := by omega
      apply hcyc
      apply isCyclic_of_orderOf_eq_card (⟨v, hv⟩ : V)
      rw [hjeq, hj2, hcard]
      norm_num
    have hdvd3 : orderOf (⟨v, hv⟩ : V) ∣ 3 := by
      rw [hjeq]
      exact (Nat.pow_dvd_pow 3 hj2).trans (by norm_num)
    have := orderOf_dvd_iff_pow_eq_one.mp hdvd3
    simpa using congrArg Subtype.val this
  exact derivedSeries_four_le_centralizer_of_exponent_three hVn hcard h3

theorem exists_core_centralized_by_fourth_derived [Finite C] {V : Subgroup C} (hVn : V.Normal)
    (hV : V ≠ ⊥) (hcard : Nat.card V ∣ 63 ∨ Nat.card V ∣ 87) :
    ∃ (N : Subgroup C) (q a : ℕ), q.Prime ∧ q ≠ 2 ∧ N ≤ V ∧ N ≠ ⊥ ∧ Nat.card N = q ^ a ∧
      derivedSeries C 4 ≤ Subgroup.centralizer (N : Set C) := by
  have hV1 : Nat.card V ≠ 1 := fun h => hV (Subgroup.card_eq_one.mp h)
  have hprime : ∀ (N : Subgroup C) (q : ℕ), q.Prime → q ≠ 2 → N ≤ V → N.Normal →
      Nat.card N = q →
      ∃ (N : Subgroup C) (q a : ℕ), q.Prime ∧ q ≠ 2 ∧ N ≤ V ∧ N ≠ ⊥ ∧ Nat.card N = q ^ a ∧
        derivedSeries C 4 ≤ Subgroup.centralizer (N : Set C) := by
    intro N q hq hq2 hNV hNn hNcard
    have : Fact q.Prime := ⟨hq⟩
    refine ⟨N, q, 1, hq, hq2, hNV, ?_, by rw [hNcard, pow_one], ?_⟩
    · intro h
      rw [h, Subgroup.card_bot] at hNcard
      exact hq.one_lt.ne hNcard
    · exact derivedSeries_four_le_centralizer_of_isCyclic hNn (isCyclic_of_prime_card hNcard)
  have hthree : Nat.card V ∣ 9 →
      ∃ (N : Subgroup C) (q a : ℕ), q.Prime ∧ q ≠ 2 ∧ N ≤ V ∧ N ≠ ⊥ ∧ Nat.card N = q ^ a ∧
        derivedSeries C 4 ≤ Subgroup.centralizer (N : Set C) := by
    intro h9
    have h9' : Nat.card V ∣ 3 ^ 2 := h9
    obtain ⟨i, -, hiV⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9'
    exact ⟨V, 3, i, Nat.prime_three, by norm_num, le_rfl, hV, hiV,
      derivedSeries_four_le_centralizer_of_card_dvd_nine hVn h9⟩
  rcases hcard with h63 | h87
  · by_cases h7 : 7 ∣ Nat.card V
    · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨N, hNV, hNn, hNcard⟩ := exists_normal_le_card_prime hVn (q := 7) (d := 9) h7
        h63 (by norm_num) (fun e he hmod => by
          have : e ≤ 9 := Nat.le_of_dvd (by norm_num) he
          interval_cases e <;> omega)
      exact hprime N 7 (by norm_num) (by norm_num) hNV hNn hNcard
    · apply hthree
      have hcop : Nat.Coprime (Nat.card V) 7 :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7)
      exact hcop.dvd_of_dvd_mul_left (by simpa using h63)
  · by_cases h29 : 29 ∣ Nat.card V
    · have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
      obtain ⟨N, hNV, hNn, hNcard⟩ := exists_normal_le_card_prime hVn (q := 29) (d := 3) h29
        h87 (by norm_num) (fun e he hmod => by
          have : e ≤ 3 := Nat.le_of_dvd (by norm_num) he
          interval_cases e <;> omega)
      exact hprime N 29 (by norm_num) (by norm_num) hNV hNn hNcard
    · apply hthree
      have hcop : Nat.Coprime (Nat.card V) 29 :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h29)
      exact (hcop.dvd_of_dvd_mul_left (show Nat.card V ∣ 29 * 3 by simpa using h87)).trans
        (by norm_num)

theorem small_odd_semiregular_core_fourth_derived_fixed_set {Ω : Type*} [Finite C]
    [MulAction C Ω] [Finite Ω] {V : Subgroup C} (hVn : V.Normal)
    (hfree : ∀ v ∈ V, ∀ ω : Ω, v • ω = ω → v = 1) (hcard : Nat.card V ∣ 63 ∨ Nat.card V ∣ 87)
    {k : ℕ} (w : Fin k → C) (hw : ∀ i, w i ∈ derivedSeries C 4) {m : ℕ}
    (hfix : Nat.card {ω : Ω // ∀ i, w i • ω = ω} = 2 ^ m) : V = ⊥ := by
  classical
  by_contra hV
  obtain ⟨N, q, a, hq, hq2, hNV, hN1, hNcard, hN4⟩ :=
    exists_core_centralized_by_fourth_derived hVn hV hcard
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨n, hnN⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN1
  have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
  have hcomm : ∀ i, n * w i = w i * n := fun i =>
    Subgroup.mem_centralizer_iff.mp (hN4 (hw i)) n hnN
  have hcomm' : ∀ i, n⁻¹ * w i = w i * n⁻¹ := fun i => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm i, mul_assoc, mul_inv_cancel, mul_one]
  let F := {ω : Ω // ∀ i, w i • ω = ω}
  let _ : Fintype F := Fintype.ofFinite F
  let σ : Perm F :=
    { toFun := fun ω => ⟨n • ω.1, fun i => by rw [← mul_smul, ← hcomm i, mul_smul, ω.2 i]⟩
      invFun := fun ω => ⟨n⁻¹ • ω.1, fun i => by rw [← mul_smul, ← hcomm' i, mul_smul, ω.2 i]⟩
      left_inv := fun ω => Subtype.ext (inv_smul_smul n ω.1)
      right_inv := fun ω => Subtype.ext (smul_inv_smul n ω.1) }
  have hσpow : ∀ j : ℕ, ∀ ω : F, ((σ ^ j) ω).1 = n ^ j • ω.1 := by
    intro j
    induction j with
    | zero => intro ω; simp
    | succ j ih =>
      intro ω
      rw [pow_succ', Perm.mul_apply, pow_succ', mul_smul, ← ih ω]
      rfl
  have hnpow : n ^ q ^ a = 1 := by
    have : (⟨n, hnN⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    rw [hNcard] at this
    simpa using congrArg Subtype.val this
  have hσ : σ ^ q ^ a = 1 := by
    ext ω
    rw [hσpow, hnpow, one_smul]
    rfl
  have hnot : ¬ q ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hfix]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  obtain ⟨ω, hω⟩ := Perm.exists_fixed_point_of_prime hnot hσ
  exact hn1' (hfree n (hNV hnN) ω.1 (congrArg Subtype.val hω))

end CFSG.ComponentClassification.LiteratureLocal
