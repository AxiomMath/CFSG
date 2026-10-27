module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltBlk
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltFib
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltPerm

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltBlk CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltFib
open scoped Pointwise

theorem num_m1 {n e p k : ℕ}
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) (hpn : p ≤ n)
    (h1 : 2 ^ e ≤ (p - 1) * 2 ^ k)
    (h2 : 2 ≤ n - p → 2 ^ (k + 1) ∣ (n - p).factorial) (h3 : n - p ≤ 1 → k = 0) :
    p = 3 ∧ (n = 7 ∨ n = 11) := by
  have hk : k < 16 := by
    by_contra hk
    have hk' : 16 ≤ k := Nat.le_of_not_lt hk
    by_cases h : 2 ≤ n - p
    · have hd := h2 h
      have hle : (n - p).factorial ≤ (8).factorial := by
        apply Nat.factorial_le
        omega
      have h4 := Nat.le_of_dvd (Nat.factorial_pos _) hd
      have h5 : 2 ^ 16 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : (8).factorial = 40320 := by decide
      omega
    · have := h3 (by omega)
      omega
  rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hp with rfl | rfl | rfl | rfl <;>
  first
  | (exfalso; revert h1 h2 h3 hpn; interval_cases k <;> decide)
  | simp

theorem num_m2 {n e p k : ℕ}
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) (hpn : 2 * p ≤ n)
    (h1 : 2 ^ e ≤ 2 * ((p - 1) * 2 ^ k))
    (h2 : 2 ^ (k + 1) ∣ p.factorial * (n - 2 * p).factorial) : False := by
  have hk : k < 14 := by
    by_contra hk
    have hk' : 14 ≤ k := Nat.le_of_not_lt hk
    have hp5 : p ≤ 5 := by omega
    have h3 : p.factorial ≤ (5).factorial := Nat.factorial_le hp5
    have h4 : (n - 2 * p).factorial ≤ (5).factorial := Nat.factorial_le (by omega)
    have h5 := Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) h2
    have h6 : 2 ^ 15 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : p.factorial * (n - 2 * p).factorial ≤ (5).factorial * (5).factorial :=
      Nat.mul_le_mul h3 h4
    have h8 : (5).factorial = 120 := by decide
    rw [h8] at h7
    omega
  rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hp with rfl | rfl | rfl | rfl <;>
  first
  | omega
  | (revert h1 h2 hpn; interval_cases k <;> decide)

section Prime

variable {n e p : ℕ} [hp : Fact p.Prime] {T X : Subgroup (Perm (Fin n))}

theorem n_bounds (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7)) : 7 ≤ n ∧ n ≤ 11 := by
  omega

theorem prime_orbit_target (hp2 : p ≠ 2)
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hTA : T ≤ alternatingGroup (Fin n))
    (hTc : Nat.card ↥T = 2 ^ e) (hX : IsPGroup p ↥X)
    (hN : T ≤ normalizer (X : Set (Perm (Fin n)))) {x₀ : Fin n} (hB : (Orb X x₀).ncard = p) :
    (∀ t ∈ T, ∀ x, t x ∈ Orb X x₀ ↔ x ∈ Orb X x₀) ∧ p = 3 ∧ (n = 7 ∨ n = 11) ∧
      2 ^ e ≤ 2 * Nat.card ↥(fixB T (Orb X x₀)) := by
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hTc
  set B := Orb X x₀ with hBdef
  obtain ⟨hn7, hn11⟩ := n_bounds hne
  have hpn : p ≤ n := by
    have h1 : B.ncard ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ B) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, hB] at h1
    exact h1
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hpP : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    have hpp := hp.out
    have hp11 : p ≤ 11 := by omega
    clear hB hpn hX hp2
    interval_cases p <;>
    first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; left; rfl)
    | (right; right; right; rfl)
    | exact absurd hpp (by decide)
  have hBC := relIndex_mul_ncard_le hN x₀
  rw [hB, Fintype.card_fin] at hBC
  have hmdvd : (stabS T B).relIndex T ∣ 2 ^ e := hTc ▸ relIndex_dvd_card _ _
  obtain ⟨i, hi, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hmdvd
  have hm12 : (stabS T B).relIndex T = 1 ∨ (stabS T B).relIndex T = 2 := by
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · left; simpa using hm
      · right; simpa using hm
    · exfalso
      have h4 : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      rw [hm] at hBC
      have : 4 * p ≤ 2 ^ i * p := Nat.mul_le_mul_right p (by simpa using h4)
      omega
  rcases hm12 with hm1 | hm2
  ·
    have hTle : T ≤ stabS T B := Subgroup.relIndex_eq_one.1 hm1
    have hinv : ∀ t ∈ T, ∀ x, t x ∈ B ↔ x ∈ B := fun t ht => (hTle ht).2
    have hG := card_le_mul_fixB hp2 hX hT2 hN hB hinv
    have hHp : IsPGroup 2 ↥(fixB T B) := hT2.to_le (fixB_le T B)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    rw [hk, hTc] at hG
    have hcompl : (Bᶜ).ncard = n - p := by
      rw [Set.ncard_compl B (Set.toFinite _) (Set.toFinite _), Nat.card_fin, hB]
    have hcl : 2 ≤ n - p → 2 ^ (k + 1) ∣ (n - p).factorial := by
      intro h2
      have hd := card_dvd_fix B ∅ (Set.disjoint_empty B) (fixB T B)
        (fun g hg => hTA hg.1) (fun g hg b hb => hg.2 b hb) (fun g _ x => Iff.rfl)
        (Or.inr (by rw [Set.union_empty, hcompl]; exact h2))
      rw [hk, Set.ncard_empty, Nat.factorial_zero, one_mul, Set.union_empty, hcompl,
        ← pow_succ'] at hd
      exact hd
    have hk0 : n - p ≤ 1 → k = 0 := by
      intro h1
      have hbot : fixB T B = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        refine Equiv.ext fun x => ?_
        by_cases hx : x ∈ B
        · exact hg.2 x hx
        · have hgx : g x ∉ B := by
            intro h
            have := hg.2 _ h
            exact hx (by rw [← g.injective this]; exact h)
          have h2 : (Bᶜ).ncard ≤ 1 := by rw [hcompl]; exact h1
          exact (Set.ncard_le_one_iff (Set.toFinite _)).1 h2 hgx hx
      have hcard1 : Nat.card ↥(fixB T B) = 1 := Subgroup.card_eq_one.2 hbot
      rw [hk] at hcard1
      exact Nat.pow_eq_one.1 hcard1 |>.resolve_left (by norm_num)
    obtain ⟨hp3', hn'⟩ := num_m1 hne hpP hpn hG hcl hk0
    refine ⟨hinv, hp3', hn', ?_⟩
    rw [hk]
    subst hp3'
    simpa using hG
  · exfalso
    set T₀ := stabS T B with hT0def
    have hT0 : IsPGroup 2 ↥T₀ := hT2.to_le (stabS_le T B)
    have hT0N : T₀ ≤ normalizer (X : Set (Perm (Fin n))) := (stabS_le T B).trans hN
    have hinv0 : ∀ t ∈ T₀, ∀ x, t x ∈ B ↔ x ∈ B := fun t ht => ht.2
    have hG0 := card_le_mul_fixB hp2 hX hT0 hT0N hB hinv0
    have hcardT0 : 2 * Nat.card ↥T₀ = 2 ^ e := by
      have h := Subgroup.relIndex_mul_card T₀ T
      rw [inf_eq_left.2 (stabS_le T B), hm2, hTc] at h
      exact h
    obtain ⟨t₁, ht₁T, ht₁⟩ : ∃ t₁ ∈ T, t₁ ∉ T₀ := by
      by_contra hcon
      have hle : T ≤ T₀ := fun t ht => by
        by_contra h
        exact hcon ⟨t, ht, h⟩
      have := Subgroup.relIndex_eq_one.2 hle
      omega
    let B' : Set (Fin n) := (t₁ : Perm (Fin n)) '' B
    have hB'eq : B' = Orb X (t₁ x₀) := image_Orb (hN ht₁T) x₀
    have hB'card : B'.ncard = p := by
      rw [Set.ncard_image_of_injective _ t₁.injective, hB]
    have hmemB' : ∀ y, y ∈ B' ↔ t₁⁻¹ y ∈ B := by
      intro y
      constructor
      · rintro ⟨b, hb, rfl⟩
        simpa using hb
      · intro h
        exact ⟨_, h, by simp⟩
    have hdisj : Disjoint B B' := by
      rw [Set.disjoint_left]
      intro x hxB hxB'
      rw [hB'eq] at hxB'
      have hEq : Orb X x₀ = Orb X (t₁ x₀) := Orb_eq_of_mem_inter hxB hxB'
      apply ht₁
      refine ⟨ht₁T, fun x => ?_⟩
      have h1 : t₁ x ∈ B' ↔ x ∈ B := t₁.injective.mem_set_image
      rw [hB'eq, ← hEq] at h1
      exact h1
    have hnorm : (T₀.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hm2
    have hinvB' : ∀ t ∈ T₀, ∀ x, t x ∈ B' ↔ x ∈ B' := by
      intro t ht x
      have htT : t ∈ T := stabS_le T B ht
      have hs : t₁⁻¹ * t * t₁ ∈ T₀ := by
        have hmem : (⟨t, htT⟩ : ↥T) ∈ T₀.subgroupOf T := ht
        have := hnorm.conj_mem _ hmem ⟨t₁⁻¹, T.inv_mem ht₁T⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      rw [hmemB', hmemB' x]
      have : t₁⁻¹ (t x) = (t₁⁻¹ * t * t₁) (t₁⁻¹ x) := by simp [Perm.mul_apply]
      rw [this]
      exact hs.2 _
    have hH0p : IsPGroup 2 ↥(fixB T₀ B) := hT0.to_le (fixB_le T₀ B)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH0p
    rw [hk] at hG0
    have hunion : (B ∪ B').ncard = 2 * p := by
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hB, hB'card]
      ring
    have hcompl : (B ∪ B')ᶜ.ncard = n - 2 * p := by
      rw [Set.ncard_compl _ (Set.toFinite _) (Set.toFinite _), Nat.card_fin, hunion]
    have hd := card_dvd_fix B B' hdisj (fixB T₀ B) (fun g hg => hTA (stabS_le T B hg.1))
      (fun g hg b hb => hg.2 b hb) (fun g hg x => hinvB' g hg.1 x)
      (Or.inl (by rw [hB'card]; omega))
    rw [hk, hB'card, hcompl, ← pow_succ'] at hd
    have hp2le : 2 * p ≤ n := by
      rw [hm2] at hBC
      exact hBC
    exact num_m2 hne hpP hp2le (by omega) hd

end Prime


theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {g : G} (hg : IsPGroup p ↥(Subgroup.zpowers g)) :
    ∃ h : G, h * g * h⁻¹ ∈ P := by
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨h, ?_⟩
  have hgQ : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
  have h1 : (h • Q : Sylow p G).toSubgroup = P.toSubgroup := by rw [hh]
  rw [Sylow.coe_subgroup_smul] at h1
  have h2 : h * g * h⁻¹ ∈ (MulAut.conj h • (Q : Subgroup G)) :=
    (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨g, hgQ, by simp⟩
  rw [h1] at h2
  exact h2

theorem factorization_two_pow_mul_odd' (e m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem card_alt_fin' {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_alt_exp {n e : ℕ}
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7)) :
    (Nat.card ↥(alternatingGroup (Fin n))).factorization 2 = e := by
  rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [card_alt_fin' (by norm_num), show (7 : ℕ).factorial / 2 = 2 ^ 3 * 315 by decide]
    exact factorization_two_pow_mul_odd' 3 315 (by decide)
  · rw [card_alt_fin' (by norm_num), show (8 : ℕ).factorial / 2 = 2 ^ 6 * 315 by decide]
    exact factorization_two_pow_mul_odd' 6 315 (by decide)
  · rw [card_alt_fin' (by norm_num), show (9 : ℕ).factorial / 2 = 2 ^ 6 * 2835 by decide]
    exact factorization_two_pow_mul_odd' 6 2835 (by decide)
  · rw [card_alt_fin' (by norm_num), show (10 : ℕ).factorial / 2 = 2 ^ 7 * 14175 by decide]
    exact factorization_two_pow_mul_odd' 7 14175 (by decide)
  · rw [card_alt_fin' (by norm_num), show (11 : ℕ).factorial / 2 = 2 ^ 7 * 155925 by decide]
    exact factorization_two_pow_mul_odd' 7 155925 (by decide)

theorem dt_exists {n : ℕ} (hn : 4 ≤ n) :
    ∃ d₀ : Perm (Fin n), d₀ ∈ alternatingGroup (Fin n) ∧ d₀ * d₀ = 1 ∧ d₀.support.card = 4 := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hdisj : Disjoint (swap a b) (swap c d) := by
    intro x
    by_cases hx : x = a ∨ x = b
    · right
      rw [swap_apply_of_ne_of_ne]
      · rcases hx with rfl | rfl <;> simp [a, b, c, Fin.ext_iff]
      · rcases hx with rfl | rfl <;> simp [a, b, d, Fin.ext_iff]
    · left
      push Not at hx
      rw [swap_apply_of_ne_of_ne hx.1 hx.2]
  refine ⟨swap a b * swap c d, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, sign_mul, sign_swap hab, sign_swap hcd]
    rfl
  · have hcomm : Commute (swap a b) (swap c d) := hdisj.commute
    calc swap a b * swap c d * (swap a b * swap c d)
        = (swap a b * swap a b) * (swap c d * swap c d) := by
          rw [mul_assoc, ← mul_assoc (swap c d), ← hcomm.eq, mul_assoc, ← mul_assoc]
      _ = 1 := by simp
  · rw [hdisj.card_support_mul, card_support_swap hab, card_support_swap hcd]

theorem exists_double_transposition {n e : ℕ}
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    {T : Subgroup (Perm (Fin n))} (hTA : T ≤ alternatingGroup (Fin n))
    (hTc : Nat.card ↥T = 2 ^ e) : ∃ d ∈ T, d * d = 1 ∧ d.support.card = 4 := by
  have hn4 : 4 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d₀, hd₀A, hd₀2, hd₀s⟩ := dt_exists hn4
  let T' : Subgroup ↥(alternatingGroup (Fin n)) := T.subgroupOf (alternatingGroup (Fin n))
  have hT'card : Nat.card ↥T' = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv
  let P : Sylow 2 ↥(alternatingGroup (Fin n)) :=
    Sylow.ofCard T' (by rw [hT'card, hTc, card_alt_exp hne])
  let g₀ : ↥(alternatingGroup (Fin n)) := ⟨d₀, hd₀A⟩
  have hg₀2 : g₀ ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hd₀2)
  have hg₀ : IsPGroup 2 ↥(zpowers g₀) := by
    have hord : orderOf g₀ ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hg₀2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨h, hh⟩ := exists_conj_mem_sylow P hg₀
  have hhT : (h : Perm (Fin n)) * d₀ * (h : Perm (Fin n))⁻¹ ∈ T := by
    have h1 : h * g₀ * h⁻¹ ∈ (P : Subgroup ↥(alternatingGroup (Fin n))) := hh
    rw [Sylow.coe_ofCard] at h1
    exact (Subgroup.mem_subgroupOf.1 h1)
  refine ⟨(h : Perm (Fin n)) * d₀ * (h : Perm (Fin n))⁻¹, hhT, ?_, ?_⟩
  · calc (h : Perm (Fin n)) * d₀ * (h : Perm (Fin n))⁻¹ * ((h : Perm (Fin n)) * d₀ *
          (h : Perm (Fin n))⁻¹) = (h : Perm (Fin n)) * (d₀ * d₀) * (h : Perm (Fin n))⁻¹ := by
          group
      _ = 1 := by rw [hd₀2]; group
  · rw [card_support_conj]
    exact hd₀s

section Nine

variable {n e : ℕ} {T X : Subgroup (Perm (Fin n))}

theorem nine_orbit_false
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hTA : T ≤ alternatingGroup (Fin n)) (hTc : Nat.card ↥T = 2 ^ e)
    (hX : IsPGroup 3 ↥X) (hN : T ≤ normalizer (X : Set (Perm (Fin n))))
    {x₀ : Fin n} (hB : (Orb X x₀).ncard = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Orb X x₀ with hBdef
  obtain ⟨hn7, hn11⟩ := n_bounds hne
  have hBC := relIndex_mul_ncard_le hN x₀
  rw [hB, Fintype.card_fin] at hBC
  have hmdvd : (stabS T B).relIndex T ∣ 2 ^ e := hTc ▸ relIndex_dvd_card _ _
  have hm1 : (stabS T B).relIndex T = 1 := by
    obtain ⟨i, hi, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hmdvd
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using hm
    · exfalso
      have h2 : 2 ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hpos
      rw [hm] at hBC
      have : 2 * 9 ≤ 2 ^ i * 9 := Nat.mul_le_mul_right 9 (by simpa using h2)
      omega
  have hTle : T ≤ stabS T B := Subgroup.relIndex_eq_one.1 hm1
  have hinv : ∀ t ∈ T, ∀ x, t x ∈ B ↔ x ∈ B := fun t ht => (hTle ht).2
  obtain ⟨d, hdT, hdd, hds⟩ := exists_double_transposition hne hTA hTc
  obtain ⟨j, hj⟩ := ncard_fixed_Orb (p := 3) (by norm_num) hX hdd (hN hdT)
    (a := x₀) ((hinv d hdT x₀).2 (mem_Orb_self X x₀))
  set F : Set (Fin n) := {b | b ∈ Orb X x₀ ∧ d b = b} with hFdef
  have hFB : F ⊆ B := fun b hb => hb.1
  have hdiff : (B \ F).ncard = 9 - F.ncard := by
    rw [Set.ncard_sdiff hFB (Set.toFinite _), hB]
  have hsupp : (d.support : Set (Fin n)).ncard = 4 := by rw [Set.ncard_coe_finset, hds]
  have hsub1 : B \ F ⊆ (d.support : Set (Fin n)) := by
    rintro b ⟨hbB, hbF⟩
    simp only [Finset.mem_coe, Perm.mem_support]
    intro h
    exact hbF ⟨hbB, h⟩
  have h1 : (B \ F).ncard ≤ 4 := hsupp ▸ Set.ncard_le_ncard hsub1 (Set.toFinite _)
  have hsub2 : (d.support : Set (Fin n)) ⊆ (B \ F) ∪ Bᶜ := by
    intro x hx
    simp only [Finset.mem_coe, Perm.mem_support] at hx
    by_cases hxB : x ∈ B
    · left
      exact ⟨hxB, fun hxF => hx hxF.2⟩
    · right
      exact hxB
  have hcompl : (Bᶜ).ncard = n - 9 := by
    rw [Set.ncard_compl B (Set.toFinite _) (Set.toFinite _), Nat.card_fin, hB]
  have h2 : 4 ≤ (B \ F).ncard + (Bᶜ).ncard := by
    calc 4 = (d.support : Set (Fin n)).ncard := hsupp.symm
      _ ≤ ((B \ F) ∪ Bᶜ).ncard := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      _ ≤ (B \ F).ncard + (Bᶜ).ncard := Set.ncard_union_le _ _
  have hF9 : F.ncard ≤ 9 := hB ▸ Set.ncard_le_ncard hFB (Set.toFinite _)
  have hF1 : 5 ≤ F.ncard := by omega
  have hF2 : F.ncard ≤ 7 := by omega
  rw [hj] at hF1 hF2
  rcases Nat.lt_or_ge j 2 with h | h
  · interval_cases j <;> simp at hF1
  · have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega

end Nine

section Main

variable {n e p : ℕ} [hp : Fact p.Prime] {T X : Subgroup (Perm (Fin n))}

theorem num_m3 {n e k : ℕ}
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hn : n = 7 ∨ n = 11) (h1 : 2 ^ e ≤ 2 * 2 ^ k)
    (h2 : 2 ^ (k + 1) ∣ (3 : ℕ).factorial * (n - 6).factorial) : False := by
  have hk : k < 12 := by
    by_contra hk
    have hk' : 12 ≤ k := Nat.le_of_not_lt hk
    have h5 := Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) h2
    have h4 : (n - 6).factorial ≤ (5).factorial := Nat.factorial_le (by omega)
    have h6 : 2 ^ 13 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : (3 : ℕ).factorial * (n - 6).factorial ≤ (3 : ℕ).factorial * (5).factorial :=
      Nat.mul_le_mul_left _ h4
    have h8 : (3 : ℕ).factorial * (5).factorial = 720 := by decide
    omega
  rcases hn with rfl | rfl <;>
  rcases hne with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
  first
  | omega
  | (revert h1 h2; interval_cases k <;> decide)

theorem perm_core (hp2 : p ≠ 2)
    (hne : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7))
    (hTA : T ≤ alternatingGroup (Fin n)) (hTc : Nat.card ↥T = 2 ^ e) (hX : IsPGroup p ↥X)
    (hN : T ≤ normalizer (X : Set (Perm (Fin n)))) {c : Perm (Fin n)} (hc : c ∈ X)
    (hc1 : c ≠ 1) : p = 3 ∧ (n = 7 ∨ n = 11) ∧ c.IsThreeCycle := by
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hTc
  obtain ⟨hn7, hn11⟩ := n_bounds hne
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hc1 (Equiv.ext h)
  have h3 := three_le_ncard_Orb hp2 hX hc hx₀
  obtain ⟨j, hj⟩ := ncard_Orb_pow hX x₀
  have hle : (Orb X x₀).ncard ≤ n := by
    have h1 : (Orb X x₀).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin] at h1
    exact h1
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hcase : (Orb X x₀).ncard = p ∨ ((Orb X x₀).ncard = 9 ∧ p = 3) := by
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [pow_zero] at hj
        omega
      · left
        rw [hj, pow_one]
    · right
      have h4 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.out.pos h
      have h5 : p ^ 2 = p * p := sq p
      have hp3' : p = 3 := by
        by_contra hne3
        have : 4 ≤ p := by omega
        have : 4 * 4 ≤ p * p := Nat.mul_le_mul this this
        omega
      subst hp3'
      have hj2 : j = 2 := by
        by_contra hne2
        have h6 : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hj2
      exact ⟨by rw [hj]; norm_num, rfl⟩
  rcases hcase with hB | ⟨hB, hp3'⟩
  swap
  · subst hp3'
    exact (nine_orbit_false hne hTA hTc hX hN hB).elim
  obtain ⟨hinv, hp3', hn, hH⟩ := prime_orbit_target hp2 hne hTA hTc hX hN hB
  subst hp3'
  set B := Orb X x₀ with hBdef
  have hfix : ∀ w ∈ X, ∀ x, x ∉ B → w x = x := by
    intro w hw x₁ hx₁
    by_contra hwx
    have h3' := three_le_ncard_Orb hp2 hX hw hwx
    obtain ⟨j₁, hj₁⟩ := ncard_Orb_pow hX x₁
    have hdisj : Disjoint B (Orb X x₁) := by
      rw [Set.disjoint_left]
      intro y hyB hyB1
      have h1 := Orb_eq_of_mem_inter hyB hyB1
      have h2 : x₁ ∈ Orb X x₁ := mem_Orb_self X x₁
      rw [← h1] at h2
      exact hx₁ h2
    have hBB1 : (B ∪ Orb X x₁).ncard = 3 + (Orb X x₁).ncard := by
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hB]
    have hle1 : (B ∪ Orb X x₁).ncard ≤ n := by
      have h1 : (B ∪ Orb X x₁).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_fin] at h1
      exact h1
    have hB1 : (Orb X x₁).ncard = 3 := by
      rcases Nat.lt_or_ge j₁ 2 with h | h
      · interval_cases j₁
        · rw [pow_zero] at hj₁
          omega
        · rw [hj₁, pow_one]
      · exfalso
        have h4 : 3 ^ 2 ≤ 3 ^ j₁ := Nat.pow_le_pow_right (by norm_num) h
        omega
    obtain ⟨hinv1, -, -, -⟩ := prime_orbit_target hp2 hne hTA hTc hX hN hB1
    have hHp : IsPGroup 2 ↥(fixB T B) := hT2.to_le (fixB_le T B)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    have hunion : (B ∪ Orb X x₁).ncard = 6 := by rw [hBB1, hB1]
    have hcompl : (B ∪ Orb X x₁)ᶜ.ncard = n - 6 := by
      rw [Set.ncard_compl _ (Set.toFinite _) (Set.toFinite _), Nat.card_fin, hunion]
    have hd := card_dvd_fix B (Orb X x₁) hdisj (fixB T B) (fun g hg => hTA hg.1)
      (fun g hg b hb => hg.2 b hb) (fun g hg x => hinv1 g hg.1 x) (Or.inl (by omega))
    rw [hk, hB1, hcompl, ← pow_succ'] at hd
    rw [hk] at hH
    exact num_m3 hne hn hH hd
  have hsub : (c.support : Set (Fin n)) ⊆ B := by
    intro x hx
    simp only [Finset.mem_coe, Perm.mem_support] at hx
    by_contra hxB
    exact hx (hfix c hc x hxB)
  have hcard3 : c.support.card ≤ 3 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hB] at this
    exact this
  have hcard1 : c.support.card ≠ 1 := card_support_ne_one c
  have hcard0 : c.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, Perm.support_eq_empty_iff]
    exact hc1
  have hcard2 : c.support.card ≠ 2 := by
    intro h2
    have hswap : c.IsSwap := card_support_eq_two.1 h2
    have hord : orderOf c = 2 := hswap.orderOf
    have hpg := (IsPGroup.iff_orderOf.1 hX) ⟨c, hc⟩
    obtain ⟨i, hi⟩ := hpg
    have hoc : orderOf (⟨c, hc⟩ : ↥X) = orderOf c := Subgroup.orderOf_mk c hc
    rw [hoc, hord] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · norm_num at hi
    · have : 3 ∣ 2 := by
        rw [hi]
        exact dvd_pow_self 3 (by omega)
      omega
  have h3c : c.support.card = 3 := by omega
  exact ⟨rfl, hn, card_support_eq_three_iff.1 h3c⟩

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltPerm
