module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternating
public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ComponentClassification.LiteratureLocal.Order504

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_sylow_eq_of_card_eq {p a m : ℕ} [hp : Fact p.Prime] (h : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Sylow p G) : Nat.card P = p ^ a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [P.card_eq_multiplicity, h, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
    Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

omit [Finite G] in
theorem not_normal_of_card [IsSimpleGroup G] {H : Subgroup G} (h1 : Nat.card H ≠ 1)
    (hG : Nat.card H ≠ Nat.card G) : ¬ H.Normal := by
  intro hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with rfl | rfl
  · exact h1 Subgroup.card_bot
  · exact hG Subgroup.card_top

theorem false_of_normalizer_le_centralizer [IsSimpleGroup G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : p ∣ Nat.card G) (hPG : Nat.card (P : Subgroup G) ≠ Nat.card G)
    (hP : normalizer ((P : Subgroup G) : Set G) ≤ centralizer ((P : Subgroup G) : Set G)) :
    False := by
  obtain ⟨K, hK, -, hindex, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with rfl | rfl
  · rw [index_bot] at hindex
    exact hPG hindex.symm
  · rw [index_top] at hindex
    exact P.ne_bot_of_dvd_card hp (card_eq_one.mp hindex.symm)

theorem card_normalizer_dvd {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p) :
    Nat.card (normalizer (P : Set G)) ∣ (p - 1) * Nat.card (centralizer (P : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  have h1 : Nat.card (normalizer (P : Set G)) =
      Nat.card P.normalizerMonoidHom.ker * Nat.card P.normalizerMonoidHom.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card P.normalizerMonoidHom.ker = Nat.card (centralizer (P : Set G)) := by
    rw [normalizerMonoidHom_ker]
    exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv
  have hrange : Nat.card P.normalizerMonoidHom.range ∣ p - 1 := by
    have h := Subgroup.card_subgroup_dvd_card P.normalizerMonoidHom.range
    rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime hp] at h
  rw [h1, hker, mul_comm (Nat.card (centralizer (P : Set G)))]
  exact Nat.mul_dvd_mul_right hrange _

omit [Finite G] in
theorem toPermHom_sylow_injective [IsSimpleGroup G] {p : ℕ} (P : Sylow p G)
    (hP : ¬ (P : Subgroup G).Normal) :
    Function.Injective (MulAction.toPermHom G (Sylow p G)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom G (Sylow p G)).ker with
    h | h
  · exact h
  · exfalso
    apply hP
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    have hg : g ∈ (MulAction.toPermHom G (Sylow p G)).ker := h ▸ mem_top g
    rw [MonoidHom.mem_ker] at hg
    have hgP : g • P = P := by
      have := congrArg (fun σ : Equiv.Perm (Sylow p G) => σ P) hg
      simpa using this
    exact Sylow.smul_eq_iff_mem_normalizer.mp hgP

theorem index_normalizer_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (normalizer ((P : Subgroup G) : Set G)).index = Nat.card (Sylow p G) :=
  (Sylow.card_eq_index_normalizer P).symm

theorem eq_of_dvd_seventy_two {n : ℕ} (h1 : n ∣ 72) (h2 : n % 7 = 1) :
    n = 1 ∨ n = 8 ∨ n = 36 := by
  have : n ≤ 72 := Nat.le_of_dvd (by norm_num) h1
  interval_cases n <;> omega

theorem eq_of_dvd_fifty_six {n : ℕ} (h1 : n ∣ 56) (h2 : n % 3 = 1) :
    n = 1 ∨ n = 4 ∨ n = 7 ∨ n = 28 := by
  have : n ≤ 56 := Nat.le_of_dvd (by norm_num) h1
  interval_cases n <;> omega

@[expose] def optionCongrHom (Ω : Type*) : Equiv.Perm Ω →* Equiv.Perm (Option Ω) where
  toFun e := Equiv.optionCongr e
  map_one' := Equiv.optionCongr_one
  map_mul' e f := by
    ext x
    cases x <;> simp

theorem optionCongrHom_injective (Ω : Type*) : Function.Injective (optionCongrHom Ω) := by
  intro e f h
  ext a
  have := congrArg (fun σ : Equiv.Perm (Option Ω) => σ (some a)) h
  simpa [optionCongrHom] using this

section Order504

variable [IsSimpleGroup G] (hG : Nat.card G = 504)
include hG

omit [IsSimpleGroup G] in
theorem card_sylow_seven_subgroup (P : Sylow 7 G) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simpa using card_sylow_eq_of_card_eq (p := 7) (a := 1) (m := 72) (by rw [hG]; norm_num)
    (by norm_num) P

omit [IsSimpleGroup G] in
theorem card_sylow_three_subgroup (R : Sylow 3 G) : Nat.card R = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa using card_sylow_eq_of_card_eq (p := 3) (a := 2) (m := 56) (by rw [hG]; norm_num)
    (by norm_num) R

omit [IsSimpleGroup G] in
theorem card_sylow_two_subgroup (S : Sylow 2 G) : Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using card_sylow_eq_of_card_eq (p := 2) (a := 3) (m := 63) (by rw [hG]; norm_num)
    (by norm_num) S

theorem not_card_sylow_seven_eq_eight (h8 : Nat.card (Sylow 7 G) = 8) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  have hP : Nat.card P = 7 := card_sylow_seven_subgroup hG P
  have hPn : ¬ (P : Subgroup G).Normal :=
    not_normal_of_card (by rw [hP]; norm_num) (by rw [hP, hG]; norm_num)
  let _ : Fintype (Sylow 7 G) := Fintype.ofFinite _
  have hinj := toPermHom_sylow_injective P hPn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 7 (by rw [hP])
  have hx : orderOf (y : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
  have hσ : orderOf (MulAction.toPermHom G (Sylow 7 G) y) = 7 := by
    rw [orderOf_injective _ hinj]
    exact hx
  have hcard : Fintype.card (Sylow 7 G) = 7 + 1 := by
    rw [← Nat.card_eq_fintype_card, h8]
  have hcent := CFSG.LocalAnalysis.ComponentInitial.centralizer_singleton_eq hcard hσ
  have hCx : Nat.card (centralizer ({(y : G)} : Set G)) ≤ 7 := by
    have hle : (centralizer ({(y : G)} : Set G)).map (MulAction.toPermHom G (Sylow 7 G)) ≤
        centralizer {MulAction.toPermHom G (Sylow 7 G) y} := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : g ∈ centralizer ({(y : G)} : Set G) := hg
      rw [mem_centralizer_singleton_iff] at hg' ⊢
      rw [← map_mul, hg', map_mul]
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective hinj, hcent, Nat.card_zpowers, hσ] at this
  have hCP : Nat.card (centralizer ((P : Subgroup G) : Set G)) ≤ 7 :=
    (Subgroup.card_le_of_le (centralizer_le (Set.singleton_subset_iff.mpr y.2))).trans hCx
  have hN : Nat.card (normalizer ((P : Subgroup G) : Set G)) = 63 := by
    have h1 := (normalizer ((P : Subgroup G) : Set G)).card_mul_index
    rw [index_normalizer_sylow, h8, hG] at h1
    omega
  have hdvd := card_normalizer_dvd (P := (P : Subgroup G)) (p := 7) (by norm_num) hP
  rw [hN] at hdvd
  have hpos : 0 < Nat.card (centralizer ((P : Subgroup G) : Set G)) := Nat.card_pos
  have := Nat.le_of_dvd (by positivity) hdvd
  omega

theorem card_sylow_seven : Nat.card (Sylow 7 G) = 36 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  have hP : Nat.card P = 7 := card_sylow_seven_subgroup hG P
  have hindex : (P : Subgroup G).index = 72 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hG] at this
    omega
  have hmod : Nat.card (Sylow 7 G) % 7 = 1 := card_sylow_modEq_one 7 G
  have hdvd : Nat.card (Sylow 7 G) ∣ 72 := hindex ▸ P.card_dvd_index
  rcases eq_of_dvd_seventy_two hdvd hmod with h | h | h
  · exfalso
    have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp h).1
    exact not_normal_of_card (H := (P : Subgroup G)) (by rw [hP]; norm_num)
      (by rw [hP, hG]; norm_num) P.normal_of_subsingleton
  · exact (not_card_sylow_seven_eq_eight hG h).elim
  · exact h

theorem card_normalizer_sylow_seven (P : Sylow 7 G) :
    Nat.card (normalizer ((P : Subgroup G) : Set G)) = 14 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := (normalizer ((P : Subgroup G) : Set G)).card_mul_index
  rw [index_normalizer_sylow, card_sylow_seven hG, hG] at h1
  omega

theorem centralizer_sylow_seven (P : Sylow 7 G) : centralizer ((P : Subgroup G) : Set G) = P := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : Nat.card P = 7 := card_sylow_seven_subgroup hG P
  have hPC : (P : Subgroup G) ≤ centralizer ((P : Subgroup G) : Set G) := by
    have : IsCyclic P := isCyclic_of_prime_card hP
    have hcomm : ∀ a b : P, a * b = b * a := isMulCommutative_iff.mp inferInstance
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hcomm ⟨b, hb⟩ ⟨a, ha⟩)
  have hCN := centralizer_le_normalizer ((P : Subgroup G) : Set G)
  have hN := card_normalizer_sylow_seven hG P
  have hdvd1 : Nat.card (centralizer ((P : Subgroup G) : Set G)) ∣ 14 :=
    hN ▸ Subgroup.card_dvd_of_le hCN
  have hdvd2 : 7 ∣ Nat.card (centralizer ((P : Subgroup G) : Set G)) := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [hP] at this
  have hcases : Nat.card (centralizer ((P : Subgroup G) : Set G)) = 7 ∨
      Nat.card (centralizer ((P : Subgroup G) : Set G)) = 14 := by
    have : Nat.card (centralizer ((P : Subgroup G) : Set G)) ≤ 14 :=
      Nat.le_of_dvd (by norm_num) hdvd1
    interval_cases (Nat.card (centralizer ((P : Subgroup G) : Set G))) <;> omega
  rcases hcases with h | h
  · exact (Subgroup.eq_of_le_of_card_ge hPC (by rw [h, hP])).symm
  · exfalso
    have hNC : normalizer ((P : Subgroup G) : Set G) ≤ centralizer ((P : Subgroup G) : Set G) :=
      (Subgroup.eq_of_le_of_card_ge hCN (by rw [h, hN])).ge
    exact false_of_normalizer_le_centralizer P (by rw [hG]; norm_num)
      (by rw [hP, hG]; norm_num) hNC

omit [IsSimpleGroup G] in
theorem exists_sylow_seven_eq_zpowers {x : G} (hx : orderOf x = 7) :
    ∃ P : Sylow 7 G, (P : Subgroup G) = zpowers x := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpg : IsPGroup 7 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
  rw [card_sylow_seven_subgroup hG P, Nat.card_zpowers, hx]

theorem centralizer_of_orderOf_eq_seven {x : G} (hx : orderOf x = 7) :
    centralizer ({x} : Set G) = zpowers x := by
  obtain ⟨P, hP⟩ := exists_sylow_seven_eq_zpowers hG hx
  have h := centralizer_sylow_seven hG P
  have h2 : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [← h2, ← hP]
  exact h

theorem exists_inverting_involution {x : G} (hx : orderOf x = 7) :
    ∃ t : G, orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_seven_eq_zpowers hG hx
  have hN := card_normalizer_sylow_seven hG P
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := normalizer ((P : Subgroup G) : Set G)) 2
    (by rw [hN]; norm_num)
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  refine ⟨t, ht', ?_⟩
  have htx : (t : G) * x * (t : G)⁻¹ ∈ zpowers x := by
    have hxP : x ∈ (P : Subgroup G) := hP ▸ mem_zpowers x
    rw [← hP]
    exact (mem_normalizer_iff.mp t.2 x).mp hxP
  rw [← mem_powers_iff_mem_zpowers] at htx
  obtain ⟨n, hn⟩ := htx
  have hn' : (t : G) * x * (t : G)⁻¹ = x ^ (n % 7) := by
    rw [← hn, ← hx, pow_mod_orderOf]
  have ht2 : (t : G) ^ 2 = 1 := by rw [← ht']; exact pow_orderOf_eq_one _
  set m := n % 7 with hm
  have hm7 : m < 7 := Nat.mod_lt n (by norm_num)
  have hmm : x ^ (m * m) = x := by
    calc x ^ (m * m) = (x ^ m) ^ m := pow_mul x m m
      _ = ((t : G) * x * (t : G)⁻¹) ^ m := by rw [hn']
      _ = (t : G) * x ^ m * (t : G)⁻¹ := conj_pow
      _ = (t : G) * ((t : G) * x * (t : G)⁻¹) * (t : G)⁻¹ := by rw [hn']
      _ = (t : G) ^ 2 * x * ((t : G) ^ 2)⁻¹ := by rw [pow_two]; group
      _ = x := by rw [ht2]; group
  have hx7 : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hdvd : 7 ∣ m * m + 6 := by
    rw [← hx]
    apply orderOf_dvd_of_pow_eq_one
    calc x ^ (m * m + 6) = x ^ (m * m) * x ^ 6 := pow_add _ _ _
      _ = x * x ^ 6 := by rw [hmm]
      _ = x ^ (6 + 1) := (pow_succ' x 6).symm
      _ = 1 := hx7
  interval_cases m
  ·
    simp at hdvd
  ·
    exfalso
    have htC : (t : G) ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      rw [pow_one] at hn'
      calc (t : G) * x = (t : G) * x * (t : G)⁻¹ * t := by group
        _ = x * t := by rw [hn']
    rw [centralizer_of_orderOf_eq_seven hG hx] at htC
    have := orderOf_dvd_of_mem_zpowers htC
    rw [ht', hx] at this
    norm_num at this
  · omega
  · omega
  · omega
  · omega
  · rw [hn']
    exact eq_inv_of_mul_eq_one_left ((pow_succ x 6).symm.trans hx7)

theorem not_injective_perm_eight {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 8) (φ : G →* Equiv.Perm Ω) (hinj : Function.Injective φ) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [hG]; norm_num)
  obtain ⟨t, -, htx⟩ := exists_inverting_involution hG hx
  have hsign : Equiv.Perm.sign (φ t) = 1 := by
    have hker : (Equiv.Perm.sign.comp φ).ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Equiv.Perm.sign.comp φ).ker with h | h
      · exfalso
        have hinj' := (MonoidHom.ker_eq_bot_iff _).mp h
        have := Nat.card_le_card_of_injective _ hinj'
        rw [hG, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
        omega
      · exact h
    have htk : t ∈ (Equiv.Perm.sign.comp φ).ker := by
      rw [hker]
      exact mem_top t
    exact MonoidHom.mem_ker.mp htk
  have hσ : orderOf (φ x) = 7 := by
    rw [orderOf_injective φ hinj]
    exact hx
  have hh : φ t * φ x * (φ t)⁻¹ = (φ x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, htx, map_inv]
  have hneg := CFSG.LocalAnalysis.ComponentInitial.sign_eq_neg_one_of_conj_eq_inv (p := 7)
    (by norm_num) (by rw [hΩ]) hσ hh
  rw [hsign] at hneg
  exact absurd hneg (by decide)

theorem eq_top_of_index_le_eight (H : Subgroup G) (h8 : H.index ≤ 8) : H = ⊤ := by
  classical
  by_contra hne
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exfalso
      exact hne (eq_top_iff.mpr (h ▸ H.normalCore_le))
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcardQ : Fintype.card (G ⧸ H) = H.index := by
    rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]
  have hidx1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hidx0 : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rcases (show H.index ≤ 6 ∨ H.index = 7 ∨ H.index = 8 by omega) with h6 | h7 | h8'
  · have hdvd : Nat.card G ∣ Nat.card (Equiv.Perm (G ⧸ H)) := by
      have h := Subgroup.card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range
      rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := G ⧸ H), hcardQ, hG] at hdvd
    interval_cases hk : H.index <;> revert hdvd <;> decide
  · exact not_injective_perm_eight hG (Ω := Option (G ⧸ H))
      (by rw [Fintype.card_option, hcardQ, h7])
      ((optionCongrHom _).comp (MulAction.toPermHom G (G ⧸ H)))
      ((optionCongrHom_injective _).comp hinj)
  · exact not_injective_perm_eight hG (Ω := G ⧸ H) (by rw [hcardQ, h8']) _ hinj

theorem card_sylow_three : Nat.card (Sylow 3 G) = 28 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hR : Nat.card R = 9 := card_sylow_three_subgroup hG R
  have hindex : (R : Subgroup G).index = 56 := by
    have := (R : Subgroup G).card_mul_index
    rw [hR, hG] at this
    omega
  have hmod : Nat.card (Sylow 3 G) % 3 = 1 := card_sylow_modEq_one 3 G
  have hdvd : Nat.card (Sylow 3 G) ∣ 56 := hindex ▸ R.card_dvd_index
  have hRn : ¬ (R : Subgroup G).Normal :=
    not_normal_of_card (by rw [hR]; norm_num) (by rw [hR, hG]; norm_num)
  have hNtop : normalizer ((R : Subgroup G) : Set G) ≠ ⊤ :=
    fun h => hRn (normalizer_eq_top_iff.mp h)
  have hNidx := index_normalizer_sylow R
  rcases eq_of_dvd_fifty_six hdvd hmod with h | h | h | h
  · exfalso
    have : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h).1
    exact hRn R.normal_of_subsingleton
  · exact absurd (eq_top_of_index_le_eight hG _ (by omega)) hNtop
  · exact absurd (eq_top_of_index_le_eight hG _ (by omega)) hNtop
  · exact h

theorem eq_one_of_commute_orderOf_seven {u y : G} (hy : orderOf y = 7) (hu : u ^ 9 = 1)
    (hc : u * y = y * u) : u = 1 := by
  have hmem : u ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hc
  rw [centralizer_of_orderOf_eq_seven hG hy] at hmem
  have h7 : orderOf u ∣ 7 := hy ▸ orderOf_dvd_of_mem_zpowers hmem
  have h9 : orderOf u ∣ 9 := orderOf_dvd_of_pow_eq_one hu
  have h1 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h7 h9
  exact orderOf_eq_one_iff.mp h1

theorem not_seven_dvd_card_centralizer {u : G} (hu1 : u ≠ 1) (hu : u ^ 9 = 1) :
    ¬ 7 ∣ Nat.card (centralizer ({u} : Set G)) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({u} : Set G)) 7 h7
  apply hu1
  refine eq_one_of_commute_orderOf_seven hG (y := (y : G))
    (by rw [Subgroup.orderOf_coe]; exact hy) hu ?_
  exact (mem_centralizer_singleton_iff.mp y.2).symm

omit [Finite G] [IsSimpleGroup G] in
theorem card_dvd_seventy_two {H : Subgroup G} (h7 : ¬ 7 ∣ Nat.card H) : Nat.card H ∣ 72 := by
  have hdvd : Nat.card H ∣ 72 * 7 := by
    rw [show 72 * 7 = 504 by norm_num, ← hG]
    exact Subgroup.card_subgroup_dvd_card H
  have hcop : Nat.Coprime (Nat.card H) 7 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem card_eq_thirty_six {H : Subgroup G} (h7 : ¬ 7 ∣ Nat.card H) (h36 : 36 ≤ Nat.card H) :
    Nat.card H = 36 := by
  have hdvd := card_dvd_seventy_two hG h7
  have hcases : Nat.card H = 36 ∨ Nat.card H = 72 := by
    have : Nat.card H ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases (Nat.card H) <;> omega
  rcases hcases with h | h
  · exact h
  · exfalso
    have hidx : H.index = 7 := by
      have := H.card_mul_index
      rw [h, hG] at this
      omega
    have htop := eq_top_of_index_le_eight hG H (by omega)
    rw [htop, index_top] at hidx
    omega

theorem not_seven_dvd_card_normalizer_of_card_four {K : Subgroup G} (hK : Nat.card K = 4) :
    ¬ 7 ∣ Nat.card (normalizer (K : Set G)) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (K : Set G)) 7 h7
  have hy' : orderOf (y : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
  have h24 : Nat.card (MulAut K) ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card (MulAut.toPerm K).range
    rw [← Nat.card_congr (MonoidHom.ofInjective (f := (MulAut.toPerm K))
      (fun a b h => MulEquiv.toEquiv_injective h)).toEquiv, Nat.card_perm, hK] at h
    exact h
  have hφ : K.normalizerMonoidHom y = 1 := by
    have h1 : orderOf (K.normalizerMonoidHom y) ∣ 7 := hy ▸ orderOf_map_dvd _ y
    have h2 : orderOf (K.normalizerMonoidHom y) ∣ 24 :=
      (_root_.orderOf_dvd_natCard _).trans h24
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2)
  have hyC : (y : G) ∈ centralizer (K : Set G) := by
    have : y ∈ K.normalizerMonoidHom.ker := hφ
    rw [normalizerMonoidHom_ker] at this
    exact this
  have hKle : K ≤ zpowers (y : G) := by
    rw [← centralizer_of_orderOf_eq_seven hG hy']
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hyC k hk
  have := Subgroup.card_dvd_of_le hKle
  rw [hK, Nat.card_zpowers, hy'] at this
  norm_num at this

theorem sylow_three_inf_eq_bot {R R' : Sylow 3 G} (hne : R ≠ R') :
    (R : Subgroup G) ⊓ R' = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro u ⟨huR, huR'⟩
  rw [mem_bot]
  by_contra hu1
  have hR9 := card_sylow_three_subgroup hG R
  have hu9 : u ^ 9 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (R : Subgroup G) huR
    rw [hR9] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  set H := centralizer ({u} : Set G) with hH
  have hle : ∀ Q : Sylow 3 G, u ∈ (Q : Subgroup G) → (Q : Subgroup G) ≤ H := by
    intro Q huQ q hq
    have hcomm : ∀ a b : (Q : Subgroup G), a * b = b * a := isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        (by rw [card_sylow_three_subgroup hG Q]; norm_num))
    rw [hH, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm ⟨q, hq⟩ ⟨u, huQ⟩)
  have hRH := hle R huR
  have hR'H := hle R' huR'
  let RH : Sylow 3 H := R.subtype hRH
  let R'H : Sylow 3 H := R'.subtype hR'H
  have hneH : RH ≠ R'H := by
    intro h
    apply hne
    apply Sylow.ext
    have h' : (R : Subgroup G).subgroupOf H = (R' : Subgroup G).subgroupOf H := by
      have := congrArg (fun Q : Sylow 3 H => (Q : Subgroup H)) h
      simpa [RH, R'H, Sylow.coe_subtype] using this
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hRH, inf_of_le_left hR'H] at h'
    exact h'
  have hRH9 : Nat.card (RH : Subgroup H) = 9 := by
    rw [Sylow.coe_subtype, ← hR9]
    exact Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv
  have hnH : 4 ≤ Nat.card (Sylow 3 H) := by
    have hmod : Nat.card (Sylow 3 H) % 3 = 1 := card_sylow_modEq_one 3 H
    have : Nontrivial (Sylow 3 H) := ⟨⟨RH, R'H, hneH⟩⟩
    have h2 : 1 < Nat.card (Sylow 3 H) := Finite.one_lt_card
    omega
  have hidxH := (RH : Subgroup H).card_mul_index
  have hdvdH := RH.card_dvd_index
  have hidx4 : 4 ≤ (RH : Subgroup H).index :=
    hnH.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hdvdH)
  have hH36 : Nat.card H = 36 := by
    apply card_eq_thirty_six hG (not_seven_dvd_card_centralizer hG hu1 hu9)
    rw [← hidxH, hRH9]
    omega
  have hidx : (RH : Subgroup H).index = 4 := by
    rw [hRH9, hH36] at hidxH
    omega
  have hnH4 : Nat.card (Sylow 3 H) = 4 := by
    rw [hidx] at hdvdH
    have := Nat.le_of_dvd (by norm_num) hdvdH
    omega
  have hNH : normalizer ((RH : Subgroup H) : Set H) ≤ centralizer ((RH : Subgroup H) : Set H) := by
    have hNidx : (normalizer ((RH : Subgroup H) : Set H)).index = 4 := by
      rw [index_normalizer_sylow, hnH4]
    have hcardN : Nat.card (normalizer ((RH : Subgroup H) : Set H)) = 9 := by
      have := (normalizer ((RH : Subgroup H) : Set H)).card_mul_index
      rw [hNidx, hH36] at this
      omega
    have heq : (RH : Subgroup H) = normalizer ((RH : Subgroup H) : Set H) :=
      Subgroup.eq_of_le_of_card_ge le_normalizer (by rw [hcardN, hRH9])
    rw [← heq]
    have hcomm : ∀ a b : (RH : Subgroup H), a * b = b * a := isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hRH9]; norm_num))
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hcomm ⟨b, hb⟩ ⟨a, ha⟩)
  obtain ⟨K, hK, -, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement RH hNH
  have hK4 : Nat.card K = 4 := by
    have := K.card_mul_index
    rw [hKidx, hRH9, hH36] at this
    omega
  set K' : Subgroup G := K.map H.subtype with hK'
  have hK'4 : Nat.card K' = 4 := by
    rw [hK', Subgroup.card_map_of_injective H.subtype_injective, hK4]
  have hK'H : K' ≤ H := Subgroup.map_subtype_le K
  have hHN : H ≤ normalizer (K' : Set G) := by
    rw [← normal_subgroupOf_iff_le_normalizer hK'H]
    have hsub : K'.subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    rw [hsub]
    exact hK
  have hNcard : Nat.card (normalizer (K' : Set G)) = 36 :=
    card_eq_thirty_six hG (not_seven_dvd_card_normalizer_of_card_four hG hK'4)
      (hH36 ▸ Subgroup.card_le_of_le hHN)
  have hK'2 : IsPGroup 2 K' := IsPGroup.of_card (n := 2) (by rw [hK'4]; norm_num)
  obtain ⟨S, hS⟩ := hK'2.exists_le_sylow
  have hS8 : Nat.card S = 8 := card_sylow_two_subgroup hG S
  have hidx2 : (K'.subgroupOf S).index = 2 := by
    have h1 := (K'.subgroupOf (S : Subgroup G)).card_mul_index
    rw [hS8, Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv, hK'4] at h1
    omega
  have hnormal : (K'.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hidx2
  have hSN : (S : Subgroup G) ≤ normalizer (K' : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hS).mp hnormal
  have := Subgroup.card_dvd_of_le hSN
  rw [hS8, hNcard] at this
  norm_num at this

end Order504

end CFSG.ComponentClassification.LiteratureLocal.Order504
