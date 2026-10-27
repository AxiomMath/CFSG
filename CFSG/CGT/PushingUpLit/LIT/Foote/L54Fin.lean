module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Basic
public import CFSG.CGT.PushingUpLit.LIT.Foote.L53C

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement Frame SylowFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_even_of_not_tight {P L : Subgroup G} (hPL : P ≤ L) (hPeven : Even (Nat.card P))
    (h : ¬ TightlyEmbedded (P.subgroupOf L)) :
    ∃ x ∈ L, x ∉ Subgroup.normalizer (P : Set G) ∧
      Even (Nat.card ↥(P ⊓ rightConjugate P x)) := by
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨?_, fun g' hg' => ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]
    exact hPeven
  · have hg : (g' : G) ∉ Subgroup.normalizer (P : Set G) := by
      intro hN
      apply hg'
      rw [← Subgroup.subgroupOf_normalizer_eq hPL]
      exact hN
    have hNE := hcon g' g'.2 hg
    have heq : P.subgroupOf L ⊓ rightConjugate (P.subgroupOf L) g' =
        (P ⊓ rightConjugate P g').subgroupOf L := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_rightConjugate_iff]
      rfl
    rw [heq]
    have hcard : Nat.card ((P ⊓ rightConjugate P g').subgroupOf L) =
        Nat.card ↥(P ⊓ rightConjugate P g') :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPL)).toEquiv
    rw [hcard]
    exact Nat.not_even_iff_odd.1 hNE

omit [Finite G] in
theorem two_elem_of_mem {T : Subgroup G} (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T) :
    ∃ n : ℕ, t ^ 2 ^ n = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem two_elem_mul {a b : G} (hab : a * b = b * a) (ha : ∃ n : ℕ, a ^ 2 ^ n = 1)
    (hb : ∃ n : ℕ, b ^ 2 ^ n = 1) : ∃ n : ℕ, (a * b) ^ 2 ^ n = 1 := by
  obtain ⟨k₁, h₁⟩ := ha
  obtain ⟨k₂, h₂⟩ := hb
  refine ⟨k₁ + k₂, ?_⟩
  have hc : Commute a b := hab
  rw [hc.mul_pow]
  have e1 : a ^ 2 ^ (k₁ + k₂) = 1 := by rw [pow_add, pow_mul, h₁, one_pow]
  have e2 : b ^ 2 ^ (k₁ + k₂) = 1 := by rw [add_comm, pow_add, pow_mul, h₂, one_pow]
  rw [e1, e2, one_mul]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem eq_one_of_mem_inf_conj (hth : Three M J) {g : G} (hg : g ∉ M) {s : G} (hsJ : s ∈ J)
    (hsJ' : s ∈ rightConjugate J g) (hs2 : ∃ n : ℕ, s ^ 2 ^ n = 1) : s = 1 := by
  by_contra hs1
  obtain ⟨a, ha, hne⟩ := c.exists_conj_ne
  obtain ⟨c', hc', hX, -⟩ := hth.exists_notin_g g (rightConjugate J g) (rightConjugate J g)
  refine hg (c.kp_g hs1 hs2 ha hc' ?_ ?_)
  · intro x hx
    exact (c.comm_J ha hne hsJ hx).symm
  · intro x hx
    refine (c.comm_conj_g g M.one_mem hc' ?_ ?_ hx).symm
    · rw [one_mul]
      exact fun h => hX h.symm
    · rw [one_mul]
      exact hsJ'

theorem not_centralizes_of_mem (hth : Three M J) {g : G} (hg : g ∉ M) {t : G}
    (ht : t ∈ rightConjugate J g) (ht1 : t ≠ 1) (ht2 : ∃ n : ℕ, t ^ 2 ^ n = 1) :
    ¬ ∀ j ∈ J, t * j = j * t := by
  intro hcomm
  obtain ⟨c', hc', hX, -⟩ := hth.exists_notin_g g (rightConjugate J g) (rightConjugate J g)
  refine hg (c.kp_g ht1 ht2 (b := 1) M.one_mem hc' ?_ ?_)
  · intro x hx
    rw [rightConjugate_one] at hx
    exact (hcomm x hx).symm
  · intro x hx
    refine (c.comm_conj_g g M.one_mem hc' ?_ ?_ hx).symm
    · rw [one_mul]
      exact fun h => hX h.symm
    · rw [one_mul]
      exact ht

end CE

omit [Finite G] in
theorem conj_inv_mem_of_mem_normalizer {N : Subgroup G} {j d : G}
    (hj : j ∈ Subgroup.normalizer (N : Set G)) (hd : d ∈ N) : j⁻¹ * d * j ∈ N := by
  have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (N : Set G)).inv_mem hj) d).1 hd
  simpa using this

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem fin_cases (hth : Three M J) {g : G} (hg : g ∉ M) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTJ : T ≤ rightConjugate J g) (hTN : T ≤ Subgroup.normalizer (J : Set G))
    (hTZ : ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t) (hTJbot : T ⊓ J = ⊥) {j : G}
    (hjJ : j ∈ J)
    (hjP : j ∉ Subgroup.normalizer ((T ⊔ (J ⊓ rightConjugate J g) : Subgroup G) : Set G))
    {t₀ : G} (ht₀ : t₀ ∈ T ⊓ rightConjugate T j) (ht₀1 : t₀ ≠ 1) : False := by
  obtain ⟨ht₀T, ht₀j⟩ := Subgroup.mem_inf.1 ht₀
  rw [mem_rightConjugate_iff] at ht₀j
  have hcomm : j * t₀ = t₀ * j := by
    have he : t₀⁻¹ * (j * t₀ * j⁻¹) ∈ T ⊓ J := by
      refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.inv_mem ht₀T) ht₀j, ?_⟩
      have h1 : t₀⁻¹ * j * t₀ ∈ J := conj_inv_mem_of_mem_normalizer (hTN ht₀T) hjJ
      have e : t₀⁻¹ * (j * t₀ * j⁻¹) = (t₀⁻¹ * j * t₀) * j⁻¹ := by group
      rw [e]
      exact J.mul_mem h1 (J.inv_mem hjJ)
    rw [hTJbot, Subgroup.mem_bot] at he
    have : j * t₀ * j⁻¹ = t₀ := by
      calc j * t₀ * j⁻¹ = t₀ * (t₀⁻¹ * (j * t₀ * j⁻¹)) := by group
        _ = t₀ := by rw [he, mul_one]
    calc j * t₀ = j * t₀ * j⁻¹ * j := by group
      _ = t₀ * j := by rw [this]
  have hjM : j ∈ rightConjugate M g :=
    c.centralizer_le_conj (hTJ ht₀T) (two_elem_of_mem hT2 ht₀T) ht₀1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have hm₀ : g * j * g⁻¹ ∈ M := (mem_rightConjugate_iff _ _ _).1 hjM
  have hJ'j : rightConjugate (rightConjugate J g) j = rightConjugate J (g * j * g⁻¹ * g) := by
    rw [rightConjugate_mul]
    congr 1
    group
  by_cases hcase : rightConjugate (rightConjugate J g) j = rightConjugate J g
  ·
    apply hjP
    set D := J ⊓ rightConjugate J g with hD
    set P := T ⊔ D with hP
    have hjN' : j ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
      (rightConjugate_eq_self_iff _ j).1 hcase
    have hjNJ : j ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hjJ
    have hTD : T ≤ Subgroup.normalizer (D : Set G) := by
      intro t ht
      have h1 := Subgroup.mem_normalizer_iff.1 (hTN ht)
      have h2 := Subgroup.mem_normalizer_iff.1
        (Subgroup.le_normalizer (H := rightConjugate J g) (hTJ ht))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hD, Subgroup.mem_inf]
      rw [h1 x, h2 x]
    have hDj : ∀ d ∈ D, j⁻¹ * d * j ∈ D := fun d hd =>
      Subgroup.mem_inf.2 ⟨conj_inv_mem_of_mem_normalizer hjNJ (Subgroup.mem_inf.1 hd).1,
        conj_inv_mem_of_mem_normalizer hjN' (Subgroup.mem_inf.1 hd).2⟩
    have hTj : ∀ t ∈ T, j⁻¹ * t * j ∈ P := by
      intro t ht
      have hcommD : t⁻¹ * j⁻¹ * t * j ∈ D := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h1 : t⁻¹ * j⁻¹ * t ∈ J :=
            conj_inv_mem_of_mem_normalizer (hTN ht) (J.inv_mem hjJ)
          have e : t⁻¹ * j⁻¹ * t * j = (t⁻¹ * j⁻¹ * t) * j := rfl
          rw [e]
          exact J.mul_mem h1 hjJ
        · have h1 : j⁻¹ * t * j ∈ rightConjugate J g :=
            conj_inv_mem_of_mem_normalizer hjN' (hTJ ht)
          have e : t⁻¹ * j⁻¹ * t * j = t⁻¹ * (j⁻¹ * t * j) := by group
          rw [e]
          exact (rightConjugate J g).mul_mem ((rightConjugate J g).inv_mem (hTJ ht)) h1
      have e : j⁻¹ * t * j = t * (t⁻¹ * j⁻¹ * t * j) := by group
      rw [e]
      exact P.mul_mem (le_sup_left (a := T) ht) (le_sup_right (b := D) hcommD)
    have hPj : ∀ y ∈ P, j⁻¹ * y * j ∈ P := by
      intro y hy
      obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_of_mem_sup hTD hy
      have e : j⁻¹ * (t * d) * j = (j⁻¹ * t * j) * (j⁻¹ * d * j) := by group
      rw [e]
      exact P.mul_mem (hTj t ht) (le_sup_right (b := D) (hDj d hd))
    have hle : rightConjugate P j ≤ P := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have := hPj _ hx
      simpa [mul_assoc] using this
    have heq : rightConjugate P j = P :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
    exact (rightConjugate_eq_self_iff P j).1 heq
  ·
    set J' := rightConjugate J g with hJ'
    have hcommJ : ∀ x ∈ J', ∀ y ∈ rightConjugate J' j, x * y = y * x := by
      intro x hx y hy
      rw [hJ'j] at hy
      have hx' : x ∈ rightConjugate J (1 * g) := by rwa [one_mul]
      refine c.comm_conj_g g M.one_mem hm₀ ?_ hx' hy
      rw [one_mul, ← hJ'j]
      exact fun h => hcase h.symm
    have hexists : ∃ s' ∈ rightConjugate T j, s' ∉ T := by
      by_contra hno
      push Not at hno
      have hle : rightConjugate T j ≤ T := fun x hx => hno x hx
      have heq : rightConjugate T j = T :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
      obtain ⟨t, ht, k, hk, hne⟩ := hTZ
      apply hne
      have htj : t ∈ rightConjugate J' j := by
        rw [mem_rightConjugate_iff]
        have : t ∈ rightConjugate T j := by rw [heq]; exact ht
        rw [mem_rightConjugate_iff] at this
        exact hTJ this
      exact (hcommJ k hk t htj).symm
    obtain ⟨s', hs'j, hs'T⟩ := hexists
    have hs'J'' : s' ∈ rightConjugate J' j := by
      rw [mem_rightConjugate_iff]
      rw [mem_rightConjugate_iff] at hs'j
      exact hTJ hs'j
    have hs'sup : s' ∈ T ⊔ J := by
      rw [mem_rightConjugate_iff] at hs'j
      have e : s' = j⁻¹ * (j * s' * j⁻¹) * j := by group
      rw [e]
      have hJ1 : j ∈ T ⊔ J := (le_sup_right : J ≤ T ⊔ J) hjJ
      have hT1 : j * s' * j⁻¹ ∈ T ⊔ J := (le_sup_left : T ≤ T ⊔ J) hs'j
      exact (T ⊔ J).mul_mem ((T ⊔ J).mul_mem ((T ⊔ J).inv_mem hJ1) hT1) hJ1
    obtain ⟨w, hwT, n, hnJ, hwn⟩ := exists_mul_of_mem_sup hTN hs'sup
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hs'T (by rw [← hwn, mul_one]; exact hwT)
    have hn : n = w⁻¹ * s' := by rw [← hwn]; group
    have hws' : w⁻¹ * s' = s' * w⁻¹ := by
      have := hcommJ w⁻¹ ((rightConjugate J g).inv_mem (hTJ hwT)) s' hs'J''
      exact this
    have hs'2 : ∃ k : ℕ, s' ^ 2 ^ k = 1 := by
      rw [mem_rightConjugate_iff] at hs'j
      obtain ⟨k, hk⟩ := two_elem_of_mem hT2 hs'j
      refine ⟨k, ?_⟩
      have : (j * s' * j⁻¹) ^ 2 ^ k = j * s' ^ 2 ^ k * j⁻¹ := conj_pow
      rw [hk] at this
      have h2 : j * s' ^ 2 ^ k * j⁻¹ = 1 := this.symm
      simpa using h2
    have hw2 : ∃ k : ℕ, w⁻¹ ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := two_elem_of_mem hT2 hwT
      exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
    have hr2 : ∃ k : ℕ, n ^ 2 ^ k = 1 := by
      rw [hn]
      refine two_elem_mul ?_ hw2 hs'2
      exact hws'
    obtain ⟨a, ha, hne⟩ := c.exists_conj_ne
    obtain ⟨c', hc', hX1, hX2⟩ := hth.exists_notin_g g J' (rightConjugate J' j)
    refine hg (c.kp_g hn1 hr2 ha hc' ?_ ?_)
    · intro x hx
      exact (c.comm_J ha hne hnJ hx).symm
    · intro y hy
      have h1 : w⁻¹ * y = y * w⁻¹ := by
        have hw' : w⁻¹ ∈ rightConjugate J (1 * g) := by
          rw [one_mul]
          exact (rightConjugate J g).inv_mem (hTJ hwT)
        refine c.comm_conj_g g M.one_mem hc' ?_ hw' hy
        rw [one_mul]
        exact fun h => hX1 h.symm
      have h2 : s' * y = y * s' := by
        have hs'' : s' ∈ rightConjugate J (g * j * g⁻¹ * g) := by rwa [← hJ'j]
        refine c.comm_conj_g g hm₀ hc' ?_ hs'' hy
        rw [← hJ'j]
        exact fun h => hX2 h.symm
      rw [hn]
      calc y * (w⁻¹ * s') = (y * w⁻¹) * s' := by group
        _ = (w⁻¹ * y) * s' := by rw [← h1]
        _ = w⁻¹ * (y * s') := by group
        _ = w⁻¹ * (s' * y) := by rw [← h2]
        _ = w⁻¹ * s' * y := by group

theorem fin (h3 : Theorem3Statement) (hth : Three M J) {g : G} (hg : g ∉ M) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTJ : T ≤ rightConjugate J g)
    (hTN : T ≤ Subgroup.normalizer (J : Set G))
    (hTZ : ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t)
    (hnum : ∀ E : Subgroup G, IsPGroup 2 E → E ≤ J → (∀ e ∈ E, ∀ t ∈ T, e * t = t * e) →
      Nat.card E ≤ Nat.card T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₁, ht₁T, k₁, hk₁, hne₁⟩ := hTZ
  have hT0 : T ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at ht₁T
    apply hne₁
    rw [ht₁T]
    simp
  have hTZ' : ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t := ⟨t₁, ht₁T, k₁, hk₁, hne₁⟩
  have hTJbot : T ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨hsT, hsJ⟩ := Subgroup.mem_inf.1 hs
    exact Subgroup.mem_bot.2
      (c.eq_one_of_mem_inf_conj hth hg hsJ (hTJ hsT) (two_elem_of_mem hT2 hsT))
  have hD : Odd (Nat.card ↥(J ⊓ rightConjugate J g)) := by
    by_contra hnot
    obtain ⟨u, hu, hu1, hu2⟩ := L54.exists_involution_of_even (Nat.not_odd_iff_even.1 hnot)
    exact hu1 (c.eq_one_of_mem_inf_conj hth hg (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hu).2
      (twoElem_of_mul_self hu2))
  set D := J ⊓ rightConjugate J g with hDdef
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := by
    intro t ht
    have h1 := Subgroup.mem_normalizer_iff.1 (hTN ht)
    have h2 := Subgroup.mem_normalizer_iff.1
      (Subgroup.le_normalizer (H := rightConjugate J g) (hTJ ht))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hDdef, Subgroup.mem_inf]
    rw [h1 x, h2 x]
  set P := T ⊔ D with hPdef
  have hPsyl : IsSylowOf 2 T P := L54.isSylowOf_sup_of_odd hT2 hTD hD
  have hPle : P ≤ J ⊔ T :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  have hF : Frame J T := ⟨hTN, hTJbot, hT2⟩
  obtain ⟨S, hS⟩ := hF.exists_sylowFrame
  have hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T := by
    set X := S ⊓ Subgroup.normalizer (T : Set G) with hX
    have hTX : T ≤ X := le_inf hS.le Subgroup.le_normalizer
    have hXpg : IsPGroup 2 X := hS.sylow.isPGroup.to_inf_left
    set Q := X ⊓ J with hQ
    have hQcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q := by
      intro q hq t ht
      obtain ⟨hqX, hqA⟩ := Subgroup.mem_inf.1 hq
      have hqN : q ∈ Subgroup.normalizer (T : Set G) := (Subgroup.mem_inf.1 hqX).2
      have h1 : q * t * q⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hqN t).1 ht
      have h2 : t * q⁻¹ * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hTN ht) q⁻¹).1 (J.inv_mem hqA)
      have hc : q * t * q⁻¹ * t⁻¹ ∈ T ⊓ J :=
        ⟨T.mul_mem h1 (T.inv_mem ht), by
          have := J.mul_mem hqA h2
          simpa [mul_assoc] using this⟩
      rw [hTJbot, Subgroup.mem_bot] at hc
      calc q * t = (q * t * q⁻¹ * t⁻¹) * (t * q) := by group
        _ = t * q := by rw [hc, one_mul]
    have hQcard : Nat.card Q ≤ Nat.card T :=
      hnum Q (hXpg.to_inf_left) inf_le_right hQcomm
    let f : ↥T × ↥Q → ↥X := fun p =>
      ⟨(p.1 : G) * (p.2 : G), X.mul_mem (hTX p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hxX⟩
      have hxS : x ∈ S := (Subgroup.mem_inf.1 hxX).1
      have hxTA : x ∈ T ⊔ J := by
        rw [sup_comm]
        exact hS.sylow.le hxS
      obtain ⟨t, ht, a, ha, hta⟩ := exists_mul_of_mem_sup hTN hxTA
      have haX : a ∈ X := by
        have : a = t⁻¹ * x := by rw [← hta]; group
        rw [this]
        exact X.mul_mem (X.inv_mem (hTX ht)) hxX
      exact ⟨(⟨t, ht⟩, ⟨a, Subgroup.mem_inf.2 ⟨haX, ha⟩⟩), Subtype.ext hta⟩
    have hXcard : Nat.card X ≤ Nat.card T * Nat.card Q := by
      have := Nat.card_le_card_of_surjective f hf
      rwa [Nat.card_prod] at this
    have hmul := Subgroup.relIndex_mul_card T X
    rw [inf_eq_left.2 hTX] at hmul
    have hTpos : 0 < Nat.card T := Nat.card_pos
    have hrel : T.relIndex X ≤ Nat.card Q := by
      refine Nat.le_of_mul_le_mul_right ?_ hTpos
      rw [hmul, mul_comm]
      exact hXcard
    exact hrel.trans hQcard
  have hnt : ¬ TightlyEmbedded (P.subgroupOf (J ⊔ T)) := by
    intro htight
    have hcomm := lemma_5_1 h3 c.block hT0 hS hPsyl hPle htight hidx
    have hcomm' : ∀ j ∈ J, t₁ * j = j * t₁ := by
      intro j hj
      have := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) ht₁T
      exact (Subgroup.mem_centralizer_iff.1 this j hj).symm
    exact c.not_centralizes_of_mem hth hg (hTJ ht₁T) (by
      rintro rfl
      exact hne₁ (by simp)) (two_elem_of_mem hT2 ht₁T) hcomm'
  have hPeven : Even (Nat.card P) := even_card_of_isPGroup hT2 hT0 le_sup_left
  obtain ⟨x, hxK, hxN, hxeven⟩ := exists_even_of_not_tight hPle hPeven hnt
  obtain ⟨w, hwT, n, hnJ, hwn⟩ := exists_mul_of_mem_sup hTN (by rwa [sup_comm] at hxK)
  have hwP : w ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer (le_sup_left (a := T) (b := D) hwT)
  have hPx : rightConjugate P x = rightConjugate P n := by
    rw [← hwn, ← rightConjugate_mul, (rightConjugate_eq_self_iff P w).2 hwP]
  have hnN : n ∉ Subgroup.normalizer (P : Set G) := by
    intro hn
    apply hxN
    rw [← hwn]
    exact Subgroup.mul_mem _ hwP hn
  have hneven : Even (Nat.card ↥(P ⊓ rightConjugate P n)) := by rwa [hPx] at hxeven
  obtain ⟨p₁, hp₁, p₂, hp₂, hTT⟩ := L54.exists_inf_ne_bot_of_even hPsyl hneven
  set y := p₂ * n * p₁ with hy
  have hyK : y ∈ T ⊔ J := by
    have hP' : P ≤ T ⊔ J := hPle.trans (by rw [sup_comm])
    have hn' : n ∈ T ⊔ J := (le_sup_right : J ≤ T ⊔ J) hnJ
    exact (T ⊔ J).mul_mem ((T ⊔ J).mul_mem (hP' hp₂) hn') (hP' hp₁)
  obtain ⟨w', hw'T, j, hjJ, hwj⟩ := exists_mul_of_mem_sup hTN hyK
  have hw'P : w' ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer (le_sup_left (a := T) (b := D) hw'T)
  have hTj : rightConjugate T y = rightConjugate T j := by
    rw [← hwj, ← rightConjugate_mul,
      (rightConjugate_eq_self_iff T w').2 (Subgroup.le_normalizer hw'T)]
  have hjN : j ∉ Subgroup.normalizer (P : Set G) := by
    intro hj
    apply hnN
    have hyN : y ∈ Subgroup.normalizer (P : Set G) := by
      rw [← hwj]
      exact Subgroup.mul_mem _ hw'P hj
    have h1 : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
    have hp₂N := h1 hp₂
    have hp₁N := h1 hp₁
    have : n = p₂⁻¹ * y * p₁⁻¹ := by rw [hy]; group
    rw [this]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ ((Subgroup.normalizer (P : Set G)).inv_mem hp₂N) hyN)
      ((Subgroup.normalizer (P : Set G)).inv_mem hp₁N)
  rw [hTj] at hTT
  obtain ⟨t₀, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTT
  exact c.fin_cases hth hg hT2 hTJ hTN hTZ' hTJbot hjJ hjN t₀.2 (fun h => ht₀1 (Subtype.ext h))

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
