module

public import Certificates.Data.Seitz77CaseB45Data
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Wr
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Certificates.Seitz77CaseB45 Subgroup CFSG.Open

structure Indexing {Q : Type} [Group Q] (T : Subgroup Q) (mt : ℕ → ℕ → ℕ) where
  elt : ℕ → Q
  inj : ∀ i j, i < 256 → j < 256 → elt i = elt j → i = j
  mem : ∀ x, x ∈ T ↔ ∃ i, i < 256 ∧ elt i = x
  mul_lt : ∀ i j, i < 256 → j < 256 → mt i j < 256
  mul : ∀ i j, i < 256 → j < 256 → elt (mt i j) = elt i * elt j
  one : elt 0 = 1

namespace Indexing

variable {Q : Type} [Group Q] {T : Subgroup Q} {mt : ℕ → ℕ → ℕ} (I : Indexing T mt)

theorem elt_mem {i : ℕ} (hi : i < 256) : I.elt i ∈ T := (I.mem _).2 ⟨i, hi, rfl⟩

open Classical in
noncomputable def idx (x : Q) : ℕ := if h : x ∈ T then Classical.choose ((I.mem x).1 h) else 0

theorem idx_eq {x : Q} (hx : x ∈ T) : I.idx x = Classical.choose ((I.mem x).1 hx) := by
  simp [idx, hx]

theorem idx_lt {x : Q} (hx : x ∈ T) : I.idx x < 256 := by
  rw [I.idx_eq hx]
  exact (Classical.choose_spec ((I.mem x).1 hx)).1

theorem elt_idx {x : Q} (hx : x ∈ T) : I.elt (I.idx x) = x := by
  rw [I.idx_eq hx]
  exact (Classical.choose_spec ((I.mem x).1 hx)).2

theorem idx_elt {i : ℕ} (hi : i < 256) : I.idx (I.elt i) = i :=
  I.inj _ _ (I.idx_lt (I.elt_mem hi)) hi (I.elt_idx (I.elt_mem hi))

theorem mt_comm {i j : ℕ} (hi : i < 256) (hj : j < 256)
    (h : I.elt i * I.elt j = I.elt j * I.elt i) : mt i j = mt j i :=
  I.inj _ _ (I.mul_lt i j hi hj) (I.mul_lt j i hj hi) (by rw [I.mul i j hi hj, I.mul j i hj hi, h])

theorem mt_sq {i : ℕ} (hi : i < 256) (h : I.elt i * I.elt i = 1) : mt i i = 0 :=
  I.inj _ _ (I.mul_lt i i hi hi) (by norm_num) (by rw [I.mul i i hi hi, h, I.one])

end Indexing

section EA

variable {Q : Type} [Group Q] [DecidableEq Q]

def EAq (S : Finset Q) : Prop :=
  (1 : Q) ∈ S ∧ ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S ∧ x * y = y * x ∧ x * x = 1

def extq (S : Finset Q) (a : Q) : Finset Q := S ∪ S.image (a * ·)

theorem mem_extq {S : Finset Q} {a x : Q} : x ∈ extq S a ↔ x ∈ S ∨ ∃ s ∈ S, a * s = x := by
  unfold extq
  rw [Finset.mem_union, Finset.mem_image]

theorem EAq.extq {S : Finset Q} (h : EAq S) {a : Q} (ha : a * a = 1)
    (hc : ∀ s ∈ S, a * s = s * a) : EAq (extq S a) := by
  have k1 : ∀ s ∈ S, ∀ t ∈ S, s * (a * t) = a * (s * t) := by
    intro s hs t ht
    rw [← mul_assoc, ← hc s hs, mul_assoc]
  have k2 : ∀ s ∈ S, ∀ t ∈ S, a * s * (a * t) = s * t := by
    intro s hs t ht
    rw [mul_assoc, k1 s hs t ht, ← mul_assoc, ha, one_mul]
  have k3 : ∀ s ∈ S, a * s * (a * s) = 1 := by
    intro s hs
    rw [k2 s hs s hs]
    exact (h.2 s hs s hs).2.2
  refine ⟨mem_extq.2 (Or.inl h.1), ?_⟩
  intro x hx y hy
  rw [mem_extq] at hx hy
  rcases hx with hx | ⟨s, hs, rfl⟩ <;> rcases hy with hy | ⟨t, ht, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := h.2 x hx y hy
    exact ⟨mem_extq.2 (Or.inl h1), h2, h3⟩
  · refine ⟨mem_extq.2 (Or.inr ⟨x * t, (h.2 x hx t ht).1, (k1 x hx t ht).symm⟩), ?_,
      (h.2 x hx x hx).2.2⟩
    calc x * (a * t) = a * (x * t) := k1 x hx t ht
      _ = a * (t * x) := by rw [(h.2 x hx t ht).2.1]
      _ = a * t * x := by rw [mul_assoc]
  · refine ⟨mem_extq.2 (Or.inr ⟨s * y, (h.2 s hs y hy).1, (mul_assoc a s y).symm⟩), ?_, k3 s hs⟩
    calc a * s * y = a * (s * y) := mul_assoc a s y
      _ = a * (y * s) := by rw [(h.2 s hs y hy).2.1]
      _ = y * (a * s) := (k1 y hy s hs).symm
  · refine ⟨mem_extq.2 (Or.inl (by rw [k2 s hs t ht]; exact (h.2 s hs t ht).1)), ?_, k3 s hs⟩
    rw [k2 s hs t ht, k2 t ht s hs]
    exact (h.2 s hs t ht).2.1

theorem card_extq {S : Finset Q} {a : Q} (ha : a ∉ S) (h : EAq S) :
    (extq S a).card = 2 * S.card := by
  unfold extq
  have hdis : Disjoint S (S.image (a * ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx'
    apply ha
    have : a = (a * s) * s := by rw [mul_assoc, (h.2 s hs s hs).2.2, mul_one]
    rw [this]
    exact (h.2 _ hx s hs).1
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (mul_right_injective a)]
  ring

end EA

section Chain

variable {Q : Type} [Group Q] [DecidableEq Q] {T : Subgroup Q} {mt : ℕ → ℕ → ℕ}
  (I : Indexing T mt)

def Lq (L : List ℕ) : Finset Q := (L.map I.elt).toFinset

theorem mem_Lq {L : List ℕ} {x : Q} : x ∈ Lq I L ↔ ∃ i ∈ L, I.elt i = x := by
  simp [Lq]

theorem Lq_extE {L : List ℕ} (hL : ∀ i ∈ L, i < 256) {y : ℕ} (hy : y < 256) :
    Lq I (extE mt L y) = extq (Lq I L) (I.elt y) := by
  ext x
  rw [mem_Lq, mem_extq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold extE at hi
    rw [List.mem_append] at hi
    rcases hi with hi | hi
    · exact Or.inl ((mem_Lq I).2 ⟨i, hi, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact Or.inr ⟨I.elt j, (mem_Lq I).2 ⟨j, hj, rfl⟩, (I.mul y j hy (hL j hj)).symm⟩
  · rintro (h | ⟨s, hs, rfl⟩)
    · obtain ⟨i, hi, rfl⟩ := (mem_Lq I).1 h
      exact ⟨i, List.mem_append.2 (Or.inl hi), rfl⟩
    · obtain ⟨j, hj, rfl⟩ := (mem_Lq I).1 hs
      exact ⟨mt y j, List.mem_append.2 (Or.inr (List.mem_map.2 ⟨j, hj, rfl⟩)),
        I.mul y j hy (hL j hj)⟩

theorem maxE_lt {L : List ℕ} {b : ℕ} (hb : 0 < b) (h : ∀ i ∈ L, i < b) : maxE L < b := by
  unfold maxE
  have : ∀ (L : List ℕ) (acc : ℕ), acc < b → (∀ i ∈ L, i < b) → L.foldl max acc < b := by
    intro L
    induction L with
    | nil => intro acc hacc _; exact hacc
    | cons a L ih =>
      intro acc hacc hL
      exact ih _ (max_lt hacc (hL a (List.mem_cons_self))) fun i hi =>
        hL i (List.mem_cons_of_mem _ hi)
  exact this L 0 hb h

open Classical in
theorem chain (n : ℕ) : ∀ S : Finset Q, S.card = n → EAq S → (∀ x ∈ S, x ∈ T) →
    ∃ k L, L ∈ levelE mt (invsOf mt) k ∧ (∀ i ∈ L, i < 256) ∧ Lq I L = S ∧ S.card = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS hST
  by_cases hS1 : S = {1}
  · subst hS1
    refine ⟨0, [0], by simp [levelE], by simp, ?_, by simp⟩
    ext x
    simp [mem_Lq, I.one, eq_comm]
  ·
    obtain ⟨y, hyS, hymax⟩ := S.exists_max_image I.idx ⟨1, hS.1⟩
    have hidx1 : I.idx (1 : Q) = 0 := by
      rw [← I.one]
      exact I.idx_elt (by norm_num)
    have hy1 : y ≠ 1 := by
      intro h1
      apply hS1
      ext x
      constructor
      · intro hx
        have h0 : I.idx x ≤ 0 := by
          have := hymax x hx
          rwa [h1, hidx1] at this
        have : I.idx x = 0 := Nat.le_zero.1 h0
        have hx' := I.elt_idx (hST x hx)
        rw [this, I.one] at hx'
        simp [← hx']
      · intro hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact hS.1
    have hF : ({1} : Finset Q) ∈ S.powerset.filter (fun S' => EAq S' ∧ y ∉ S') := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, ⟨?_, ?_⟩, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact hS.1
      · exact Finset.mem_singleton_self 1
      · intro x hx z hz
        rw [Finset.mem_singleton] at hx hz
        subst hx
        subst hz
        simp
      · simpa using hy1
    obtain ⟨S', hS'F, hS'max⟩ := (S.powerset.filter (fun S' => EAq S' ∧ y ∉ S')).exists_max_image
      Finset.card ⟨{1}, hF⟩
    have hS'mem := Finset.mem_filter.1 hS'F
    have hS'S : S' ⊆ S := Finset.mem_powerset.1 hS'mem.1
    have hS'EA : EAq S' := hS'mem.2.1
    have hyS' : y ∉ S' := hS'mem.2.2
    have hsq : ∀ a ∈ S, a * a = 1 := fun a ha => (hS.2 a ha a ha).2.2
    have hcover : ∀ a ∈ S, a ∈ S' ∨ ∃ s ∈ S', y * s = a := by
      intro a ha
      by_contra hcon
      push Not at hcon
      obtain ⟨haS', hay⟩ := hcon
      have hEA'' : EAq (extq S' a) := hS'EA.extq (hsq a ha)
        (fun s hs => (hS.2 a ha s (hS'S hs)).2.1)
      have hsub : extq S' a ⊆ S := by
        intro x hx
        rcases mem_extq.1 hx with hx | ⟨s, hs, rfl⟩
        · exact hS'S hx
        · exact (hS.2 a ha s (hS'S hs)).1
      have hy'' : y ∉ extq S' a := by
        intro hy
        rcases mem_extq.1 hy with hy | ⟨s, hs, hsy⟩
        · exact hyS' hy
        · apply hay s hs
          rw [← hsy, mul_assoc, (hS'EA.2 s hs s hs).2.2, mul_one]
      have hmem : extq S' a ∈ S.powerset.filter (fun S' => EAq S' ∧ y ∉ S') :=
        Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hEA'', hy''⟩
      have hle := hS'max _ hmem
      have haext : a ∈ extq S' a := mem_extq.2 (Or.inr ⟨1, hS'EA.1, mul_one a⟩)
      have hlt : S'.card < (extq S' a).card := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => mem_extq.2 (Or.inl hx), fun hsub' => haS' (hsub' haext)⟩
      omega
    have hext : S = extq S' y := by
      ext a
      constructor
      · intro ha
        rcases hcover a ha with h | ⟨s, hs, rfl⟩
        · exact mem_extq.2 (Or.inl h)
        · exact mem_extq.2 (Or.inr ⟨s, hs, rfl⟩)
      · intro ha
        rcases mem_extq.1 ha with h | ⟨s, hs, rfl⟩
        · exact hS'S h
        · exact (hS.2 y hyS s (hS'S hs)).1
    have hcardS : S.card = 2 * S'.card := by
      rw [hext]
      exact card_extq hyS' hS'EA
    have hS'lt : S'.card < n := by
      rw [← hn, hcardS]
      have : 0 < S'.card := Finset.card_pos.2 ⟨1, hS'EA.1⟩
      omega
    obtain ⟨k', L', hL', hL'lt, hLq, hcard'⟩ := ih S'.card hS'lt S' rfl hS'EA
      (fun x hx => hST x (hS'S hx))
    have hyT := hST y hyS
    have hyidx : 0 < I.idx y := by
      rcases Nat.eq_zero_or_pos (I.idx y) with h0 | h0
      · exfalso
        apply hy1
        rw [← I.elt_idx hyT, h0, I.one]
      · exact h0
    have hylt : I.idx y < 256 := I.idx_lt hyT
    have hmax : maxE L' < I.idx y := by
      apply maxE_lt hyidx
      intro i hi
      have hxS' : I.elt i ∈ S' := by rw [← hLq]; exact (mem_Lq I).2 ⟨i, hi, rfl⟩
      have hle := hymax _ (hS'S hxS')
      rw [I.idx_elt (hL'lt i hi)] at hle
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        apply hyS'
        have : I.elt i = y := by rw [h, I.elt_idx hyT]
        rw [← this]
        exact hxS'
    have hyinv : I.idx y ∈ invsOf mt := by
      unfold invsOf
      rw [List.mem_filter, List.mem_range]
      refine ⟨hylt, ?_⟩
      have hsqy := hsq y hyS
      rw [← I.elt_idx hyT] at hsqy
      have := I.mt_sq hylt hsqy
      simp [this]
      omega
    have hycomm : ∀ e ∈ L', mt (I.idx y) e = mt e (I.idx y) := by
      intro e he
      have heS' : I.elt e ∈ S' := by rw [← hLq]; exact (mem_Lq I).2 ⟨e, he, rfl⟩
      have h1 := (hS.2 y hyS _ (hS'S heS')).2.1
      rw [← I.elt_idx hyT] at h1
      exact I.mt_comm hylt (hL'lt e he) h1
    refine ⟨k' + 1, extE mt L' (I.idx y), ?_, ?_, ?_, ?_⟩
    · show extE mt L' (I.idx y) ∈ nextLevel mt (invsOf mt) (levelE mt (invsOf mt) k')
      unfold nextLevel
      rw [List.mem_flatMap]
      refine ⟨L', hL', ?_⟩
      rw [List.mem_map]
      refine ⟨I.idx y, ?_, rfl⟩
      rw [List.mem_filter]
      refine ⟨hyinv, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
      exact ⟨hmax, hycomm⟩
    · intro i hi
      unfold extE at hi
      rcases List.mem_append.1 hi with h | h
      · exact hL'lt i h
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
        exact I.mul_lt _ _ hylt (hL'lt j hj)
    · rw [Lq_extE I hL'lt hylt, hLq, I.elt_idx hyT, ← hext]
    · rw [hcardS, hcard', pow_succ]
      ring

theorem levelE_nil_of {k : ℕ} (h : levelE mt (invsOf mt) k = []) (j : ℕ) :
    levelE mt (invsOf mt) (k + j) = [] := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    show nextLevel mt (invsOf mt) (levelE mt (invsOf mt) (k + j)) = []
    rw [ih]
    rfl

theorem fb7_sound {U : Subgroup Q} {isU : ℕ → Bool}
    (hU : ∀ i, i < 256 → (isU i = true ↔ I.elt i ∈ U)) (h : fb7Check mt isU = true) :
    ∀ E : Subgroup Q, E ≤ T → IsElemAbelian 2 E →
      Nat.card E ≤ 16 ∧ (Nat.card E = 16 → E ≤ U) := by
  classical
  intro E hET hE
  unfold fb7Check fb7Aux at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
  obtain ⟨h5, h4⟩ := h
  have h5' : levelE mt (invsOf mt) 5 = [] := h5
  let S : Finset Q := ((Finset.range 256).filter fun i => I.elt i ∈ E).image I.elt
  have hSE : ∀ x, x ∈ S ↔ x ∈ E := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hi).2
    · intro hx
      obtain ⟨i, hi, rfl⟩ := (I.mem x).1 (hET hx)
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hx⟩, rfl⟩
  have hScard : S.card = Nat.card E := by
    have : Nat.card E = Nat.card {x // x ∈ S} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => (hSE x).symm)
    rw [this, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hEA : EAq S := by
    refine ⟨(hSE 1).2 E.one_mem, fun x hx y hy => ?_⟩
    rw [hSE] at hx hy
    refine ⟨(hSE _).2 (E.mul_mem hx hy), ?_, ?_⟩
    · exact hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> congrArg Subtype.val
    · rw [← pow_two]
      exact hE.2 x hx
  obtain ⟨k, L, hL, hLlt, hLq, hcard⟩ :=
    chain I S.card S rfl hEA (fun x hx => hET ((hSE x).1 hx))
  have hk : k < 5 := by
    by_contra hk
    push Not at hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [levelE_nil_of h5' j] at hL
    simp at hL
  rw [hScard] at hcard
  refine ⟨?_, fun h16 => ?_⟩
  · rw [hcard]
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  · have hk4 : k = 4 := by
      have : 2 ^ k = 2 ^ 4 := by rw [← hcard, h16]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    subst hk4
    intro x hx
    have hxS := (hSE x).2 hx
    rw [← hLq, mem_Lq] at hxS
    obtain ⟨i, hi, rfl⟩ := hxS
    exact (hU i (hLlt i hi)).1 (h4 L hL i hi)

end Chain

section FB6

open Classical in
@[expose] noncomputable def Wgrp {G : Type*} [Group G] (g : G) : ℕ :=
  if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 4 = 1 then 4 else
  if g ^ 8 = 1 then 8 else if g ^ 16 = 1 then 16 else 0

theorem orderOf_two_pow_succ {G : Type*} [Group G] (g : G) (j : ℕ) :
    orderOf g = 2 ^ (j + 1) ↔ g ^ (2 ^ (j + 1)) = 1 ∧ ¬ g ^ (2 ^ j) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    refine ⟨?_, fun h1 => ?_⟩
    · rw [← h]
      exact pow_orderOf_eq_one g
    · have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [h] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime_pow h2 h1

theorem Wgrp_spec {G : Type*} [Group G] (g : G) :
    (g = 1 ∧ Wgrp g = 1) ∨ (orderOf g = 2 ∧ Wgrp g = 2) ∨ (orderOf g = 4 ∧ Wgrp g = 4) ∨
    (orderOf g = 8 ∧ Wgrp g = 8) ∨ (orderOf g = 16 ∧ Wgrp g = 16) ∨
    (Wgrp g = 0 ∧ ¬ g ^ 16 = 1) := by
  have o4 := orderOf_two_pow_succ g 1
  have o8 := orderOf_two_pow_succ g 2
  have o16 := orderOf_two_pow_succ g 3
  norm_num at o4 o8 o16
  by_cases c1 : g = 1
  · exact Or.inl ⟨c1, by simp [Wgrp, c1]⟩
  · by_cases c2 : g ^ 2 = 1
    · exact Or.inr (Or.inl ⟨orderOf_eq_prime c2 c1, by simp [Wgrp, c1, c2]⟩)
    · by_cases c4 : g ^ 4 = 1
      · exact Or.inr (Or.inr (Or.inl ⟨o4.2 ⟨c4, c2⟩, by simp [Wgrp, c1, c2, c4]⟩))
      · by_cases c8 : g ^ 8 = 1
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨o8.2 ⟨c8, c4⟩,
            by simp [Wgrp, c1, c2, c4, c8]⟩)))
        · by_cases c16 : g ^ 16 = 1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨o16.2 ⟨c16, c8⟩,
              by simp [Wgrp, c1, c2, c4, c8, c16]⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [Wgrp, c1, c2, c4, c8, c16],
              c16⟩))))

theorem Wgrp_eq_iff {G : Type*} [Group G] (g : G) :
    (Wgrp g = 1 ↔ g = 1) ∧ (Wgrp g = 2 ↔ orderOf g = 2) ∧ (Wgrp g = 4 ↔ orderOf g = 4) ∧
    (Wgrp g = 8 ↔ orderOf g = 8) ∧ (Wgrp g = 16 ↔ orderOf g = 16) := by
  have key : ∀ k, k ∣ 16 → orderOf g = k → g ^ 16 = 1 := fun k hk h =>
    orderOf_dvd_iff_pow_eq_one.1 (h ▸ hk)
  have hne : g ≠ 1 → orderOf g ≠ 1 := fun h h1 => h (orderOf_eq_one_iff.1 h1)
  rcases Wgrp_spec g with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    simp [h2, orderOf_one]
  · have : g ≠ 1 := fun h => by simp [h] at h1
    refine ⟨by simp [h2, this], by simp [h1, h2], by simp [h1, h2], by simp [h1, h2],
      by simp [h1, h2]⟩
  · have : g ≠ 1 := fun h => by simp [h] at h1
    refine ⟨by simp [h2, this], by simp [h1, h2], by simp [h1, h2], by simp [h1, h2],
      by simp [h1, h2]⟩
  · have : g ≠ 1 := fun h => by simp [h] at h1
    refine ⟨by simp [h2, this], by simp [h1, h2], by simp [h1, h2], by simp [h1, h2],
      by simp [h1, h2]⟩
  · have : g ≠ 1 := fun h => by simp [h] at h1
    refine ⟨by simp [h2, this], by simp [h1, h2], by simp [h1, h2], by simp [h1, h2],
      by simp [h1, h2]⟩
  · have hg1 : g ≠ 1 := fun h => h2 (by simp [h])
    refine ⟨by simp [h1, hg1], ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => by omega, fun h => (h2 (key 2 (by norm_num) h)).elim⟩
    · exact ⟨fun h => by omega, fun h => (h2 (key 4 (by norm_num) h)).elim⟩
    · exact ⟨fun h => by omega, fun h => (h2 (key 8 (by norm_num) h)).elim⟩
    · exact ⟨fun h => by omega, fun h => (h2 (key 16 (by norm_num) h)).elim⟩

variable {Q : Type} [Group Q] {T : Subgroup Q} {mt : ℕ → ℕ → ℕ} (I : Indexing T mt)

@[expose] def evq (v : WEl) : Wr Q := ⟨I.elt v.1, I.elt v.2.1, v.2.2⟩

def Valid (v : WEl) : Prop := v.1 < 256 ∧ v.2.1 < 256

variable {I}

theorem valid_wone : Valid wone := ⟨by norm_num [wone], by norm_num [wone]⟩

theorem valid_wmul (I : Indexing T mt) {v v' : WEl} (hv : Valid v) (hv' : Valid v') :
    Valid (wmul mt v v') := by
  obtain ⟨a, b, e⟩ := v
  obtain ⟨c, d, f⟩ := v'
  obtain ⟨ha, hb⟩ := hv
  obtain ⟨hc, hd⟩ := hv'
  have h1 := fun x y (hx : x < 256) (hy : y < 256) => I.mul_lt x y hx hy
  cases e
  · exact ⟨h1 a c ha hc, h1 b d hb hd⟩
  · exact ⟨h1 a d ha hd, h1 b c hb hc⟩

theorem evq_mul {v v' : WEl} (hv : Valid v) (hv' : Valid v') :
    evq I (wmul mt v v') = evq I v * evq I v' := by
  obtain ⟨a, b, e⟩ := v
  obtain ⟨c, d, f⟩ := v'
  obtain ⟨ha, hb⟩ := hv
  obtain ⟨hc, hd⟩ := hv'
  cases e
  · simp [wmul, evq, I.mul _ _ ha hc, I.mul _ _ hb hd]
  · simp [wmul, evq, I.mul _ _ ha hd, I.mul _ _ hb hc]

theorem evq_one : evq I wone = 1 := by
  simp [evq, wone, I.one, Wr.one_def]

theorem evq_inj {v v' : WEl} (hv : Valid v) (hv' : Valid v') (h : evq I v = evq I v') :
    v = v' := by
  obtain ⟨a, b, e⟩ := v
  obtain ⟨c, d, f⟩ := v'
  have h1 : I.elt a = I.elt c := congrArg Wr.a h
  have h2 : I.elt b = I.elt d := congrArg Wr.b h
  have h3 : e = f := congrArg Wr.e h
  have ha : a < 256 := hv.1
  have hb : b < 256 := hv.2
  have hc : c < 256 := hv'.1
  have hd : d < 256 := hv'.2
  rw [I.inj _ _ ha hc h1, I.inj _ _ hb hd h2, h3]

theorem evq_eq_one_iff {v : WEl} (hv : Valid v) : evq I v = 1 ↔ v = wone := by
  constructor
  · intro h
    apply evq_inj (I := I) hv valid_wone
    rw [h, evq_one]
  · rintro rfl
    exact evq_one

theorem beq_wone_iff {v : WEl} (hv : Valid v) : (v == wone) = true ↔ evq I v = 1 := by
  rw [evq_eq_one_iff hv]
  simp

theorem wOrd_eq_Wgrp {v : WEl} (hv : Valid v) : wOrd mt v = Wgrp (evq I v) := by
  set g := evq I v with hg
  have hv2 := valid_wmul I hv hv
  have hv4 := valid_wmul I hv2 hv2
  have hv8 := valid_wmul I hv4 hv4
  have hv16 := valid_wmul I hv8 hv8
  set w2 := wmul mt v v with hw2
  set w4 := wmul mt w2 w2 with hw4
  set w8 := wmul mt w4 w4 with hw8
  set w16 := wmul mt w8 w8 with hw16
  have e2 : evq I w2 = g ^ 2 := by rw [hw2, evq_mul (I := I) hv hv, pow_two]
  have e4 : evq I w4 = g ^ 4 := by rw [hw4, evq_mul (I := I) hv2 hv2, e2, ← pow_add]
  have e8 : evq I w8 = g ^ 8 := by rw [hw8, evq_mul (I := I) hv4 hv4, e4, ← pow_add]
  have e16 : evq I w16 = g ^ 16 := by rw [hw16, evq_mul (I := I) hv8 hv8, e8, ← pow_add]
  have b1 : (v == wone) = true ↔ g = 1 := beq_wone_iff (I := I) hv
  have b2 : (w2 == wone) = true ↔ g ^ 2 = 1 := by rw [beq_wone_iff (I := I) hv2, e2]
  have b4 : (w4 == wone) = true ↔ g ^ 4 = 1 := by rw [beq_wone_iff (I := I) hv4, e4]
  have b8 : (w8 == wone) = true ↔ g ^ 8 = 1 := by rw [beq_wone_iff (I := I) hv8, e8]
  have b16 : (w16 == wone) = true ↔ g ^ 16 = 1 := by rw [beq_wone_iff (I := I) hv16, e16]
  by_cases c1 : g = 1
  · have h1 := b1.2 c1
    simp [wOrd, Wgrp, h1, c1]
  · have h1 : ¬ (v == wone) = true := fun h => c1 (b1.1 h)
    by_cases c2 : g ^ 2 = 1
    · have h2 := b2.2 c2
      simp [wOrd, Wgrp, h1, c1, c2, h2, ← hw2]
    · have h2 : ¬ (w2 == wone) = true := fun h => c2 (b2.1 h)
      by_cases c4 : g ^ 4 = 1
      · have h4 := b4.2 c4
        simp [wOrd, Wgrp, h1, c1, c2, h2, c4, h4, ← hw2, ← hw4]
      · have h4 : ¬ (w4 == wone) = true := fun h => c4 (b4.1 h)
        by_cases c8 : g ^ 8 = 1
        · have h8 := b8.2 c8
          simp [wOrd, Wgrp, h1, c1, c2, h2, c4, h4, c8, h8, ← hw2, ← hw4, ← hw8]
        · have h8 : ¬ (w8 == wone) = true := fun h => c8 (b8.1 h)
          by_cases c16 : g ^ 16 = 1
          · have h16 := b16.2 c16
            simp [wOrd, Wgrp, h1, c1, c2, h2, c4, h4, c8, h8, c16, h16, ← hw2, ← hw4, ← hw8,
              ← hw16]
          · have h16 : ¬ (w16 == wone) = true := fun h => c16 (b16.1 h)
            simp [wOrd, Wgrp, h1, c1, c2, h2, c4, h4, c8, h8, c16, h16, ← hw2, ← hw4, ← hw8,
              ← hw16]

theorem wOrd_spec {v : WEl} (hv : Valid v) :
    (wOrd mt v = 2 ↔ orderOf (evq I v) = 2) ∧ (wOrd mt v = 4 ↔ orderOf (evq I v) = 4) ∧
    (wOrd mt v = 8 ↔ orderOf (evq I v) = 8) ∧ (wOrd mt v = 16 ↔ orderOf (evq I v) = 16) := by
  rw [wOrd_eq_Wgrp (I := I) hv]
  obtain ⟨-, h2, h4, h8, h16⟩ := Wgrp_eq_iff (evq I v)
  exact ⟨h2, h4, h8, h16⟩

structure Labels (I : Indexing T mt) (U : Subgroup Q) (lab : ℕ → ℕ) (ladd : ℕ → ℕ → ℕ) :
    Prop where
  lt : ∀ i, i < 256 → lab i < 4
  zero : lab 0 = 0
  eq_iff : ∀ i j, i < 256 → j < 256 → (lab i = lab j ↔ (I.elt i)⁻¹ * I.elt j ∈ U)
  hom : ∀ i j, i < 256 → j < 256 → lab (mt i j) = ladd (lab i) (lab j)

theorem exists_mask_aux (f : ℕ → Prop) :
    ∀ n : ℕ, ∃ m < 2 ^ n, ∀ k < n, m.testBit k = true ↔ f k := by
  classical
  intro n
  induction n with
  | zero => exact ⟨0, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    obtain ⟨m', hm', hk'⟩ := ih
    by_cases hf : f n
    · refine ⟨2 ^ n + m', by rw [pow_succ]; omega, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Nat.testBit_two_pow_add_gt hk]
        exact hk' k hk
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hm']
        simp [hf]
    · refine ⟨m', by rw [pow_succ]; omega, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hk' k hk
      · rw [Nat.testBit_eq_false_of_lt hm']
        simp [hf]

theorem exists_mask (M : ℕ → ℕ → Prop) :
    ∃ m < 65536, ∀ p q, p < 4 → q < 4 → (inM m p q = true ↔ M p q) := by
  obtain ⟨m, hm, h⟩ := exists_mask_aux (fun k => M (k / 4) (k % 4)) 16
  refine ⟨m, by simpa using hm, fun p q hp hq => ?_⟩
  have := h (4 * p + q) (by omega)
  have e1 : (4 * p + q) / 4 = p := by omega
  have e2 : (4 * p + q) % 4 = q := by omega
  rw [e1, e2] at this
  exact this

def LabelSet (I : Indexing T mt) (lab : ℕ → ℕ) (R : Subgroup (Wr Q)) (p q : ℕ) : Prop :=
  ∃ i j, i < 256 ∧ j < 256 ∧ lab i = p ∧ lab j = q ∧ (⟨I.elt i, I.elt j, false⟩ : Wr Q) ∈ R

variable {U : Subgroup Q} {lab : ℕ → ℕ} {ladd : ℕ → ℕ → ℕ}

theorem mem_iff_mask (L : Labels I U lab ladd) {R : Subgroup (Wr Q)} (hSS : Wr.ss U ≤ R)
    (hsw : (Wr.swap : Wr Q) ∈ R) {m : ℕ}
    (hm : ∀ p q, p < 4 → q < 4 → (inM m p q = true ↔ LabelSet I lab R p q)) {v : WEl}
    (hv : Valid v) : evq I v ∈ R ↔ inM m (lab v.1) (lab v.2.1) = true := by
  obtain ⟨a, b, e⟩ := v
  obtain ⟨ha, hb⟩ := hv
  have hbase : ∀ (w : Wr Q), w ∈ R ↔ (⟨w.a, w.b, false⟩ : Wr Q) ∈ R := by
    intro w
    obtain ⟨x, y, e⟩ := w
    cases e
    · exact Iff.rfl
    · have hs : (⟨x, y, true⟩ : Wr Q) * Wr.swap = ⟨x, y, false⟩ := by simp [Wr.swap]
      have hs' : (⟨x, y, false⟩ : Wr Q) * Wr.swap = ⟨x, y, true⟩ := by simp [Wr.swap]
      constructor
      · intro h
        rw [← hs]
        exact R.mul_mem h hsw
      · intro h
        rw [← hs']
        exact R.mul_mem h hsw
  show evq I (a, b, e) ∈ R ↔ _
  rw [show evq I (a, b, e) = ⟨I.elt a, I.elt b, e⟩ from rfl, hbase]
  show (⟨I.elt a, I.elt b, false⟩ : Wr Q) ∈ R ↔ _
  rw [hm _ _ (L.lt a ha) (L.lt b hb)]
  constructor
  · intro h
    exact ⟨a, b, ha, hb, rfl, rfl, h⟩
  · rintro ⟨i, j, hi, hj, hli, hlj, hR⟩
    have h1 : (I.elt i)⁻¹ * I.elt a ∈ U := (L.eq_iff i a hi ha).1 hli
    have h2 : (I.elt j)⁻¹ * I.elt b ∈ U := (L.eq_iff j b hj hb).1 hlj
    have hmem : (⟨(I.elt i)⁻¹ * I.elt a, (I.elt j)⁻¹ * I.elt b, false⟩ : Wr Q) ∈ R :=
      hSS (Wr.mem_ss.2 ⟨h1, h2, rfl⟩)
    have := R.mul_mem hR hmem
    simpa using this

theorem allBelow_iff {n : ℕ} {f : ℕ → Bool} :
    CFSG.PSL3Four.Native.allBelow n f = true ↔ ∀ k < n, f k = true := by
  simp [CFSG.PSL3Four.Native.allBelow]

theorem admM_true (L : Labels I U lab ladd) {R : Subgroup (Wr Q)} (hsw : (Wr.swap : Wr Q) ∈ R)
    {m : ℕ} (hm : ∀ p q, p < 4 → q < 4 → (inM m p q = true ↔ LabelSet I lab R p q)) :
    admM ladd m = true := by
  unfold admM
  simp only [Bool.and_eq_true, allBelow_iff, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨?_, fun p hp q hq => ?_⟩
  · refine (hm 0 0 (by norm_num) (by norm_num)).2
      ⟨0, 0, by norm_num, by norm_num, L.zero, L.zero, ?_⟩
    rw [I.one]
    exact (show (⟨1, 1, false⟩ : Wr Q) = 1 from rfl) ▸ R.one_mem
  · by_cases hpq : inM m p q = true
    · right
      obtain ⟨i, j, hi, hj, hli, hlj, hR⟩ := (hm p q hp hq).1 hpq
      have hsym : (⟨I.elt j, I.elt i, false⟩ : Wr Q) ∈ R := by
        have := R.mul_mem (R.mul_mem hsw hR) hsw
        rwa [Wr.swap_mul_mul_swap] at this
      refine ⟨(hm q p hq hp).2 ⟨j, i, hj, hi, hlj, hli, hsym⟩, fun p' hp' q' hq' => ?_⟩
      by_cases hpq' : inM m p' q' = true
      · right
        obtain ⟨i', j', hi', hj', hli', hlj', hR'⟩ := (hm p' q' hp' hq').1 hpq'
        have hprod : (⟨I.elt (mt i i'), I.elt (mt j j'), false⟩ : Wr Q) ∈ R := by
          rw [I.mul i i' hi hi', I.mul j j' hj hj']
          have := R.mul_mem hR hR'
          simpa using this
        have e1 : lab (mt i i') = ladd p p' := by rw [L.hom i i' hi hi', hli, hli']
        have e2 : lab (mt j j') = ladd q q' := by rw [L.hom j j' hj hj', hlj, hlj']
        have l1 : ladd p p' < 4 := by rw [← e1]; exact L.lt _ (I.mul_lt _ _ hi hi')
        have l2 : ladd q q' < 4 := by rw [← e2]; exact L.lt _ (I.mul_lt _ _ hj hj')
        exact (hm _ _ l1 l2).2 ⟨mt i i', mt j j', I.mul_lt _ _ hi hi', I.mul_lt _ _ hj hj', e1,
          e2, hprod⟩
      · left
        simpa using hpq'
    · left
      simpa using hpq

theorem comm_swap_iff (w : Wr Q) : w * Wr.swap = Wr.swap * w ↔ w.a = w.b := by
  obtain ⟨a, b, e⟩ := w
  cases e <;> simp [Wr.swap, eq_comm]

theorem comm_base_iff (a b c d : Q) (e : Bool) :
    (⟨c, d, e⟩ : Wr Q) * ⟨a, b, false⟩ = ⟨a, b, false⟩ * ⟨c, d, e⟩ ↔
      (e = false → c * a = a * c ∧ d * b = b * d) ∧ (e = true → c * b = a * c ∧ d * a = b * d) := by
  cases e <;> simp [Wr.ext_iff]

theorem mem_tauList {m c d : ℕ} {e : Bool} :
    (c, d, e) ∈ tauList lab m ↔ c < 256 ∧ d = c ∧ inM m (lab c) (lab c) = true := by
  unfold tauList
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨c', ⟨h1, h2⟩, rfl, rfl, h3⟩ | ⟨c', ⟨h1, h2⟩, rfl, rfl, h3⟩) <;> exact ⟨h1, rfl, h2⟩
  · rintro ⟨h1, hdc, h2⟩
    rw [hdc]
    cases e
    · exact Or.inl ⟨c, ⟨h1, h2⟩, rfl, rfl, rfl⟩
    · exact Or.inr ⟨c, ⟨h1, h2⟩, rfl, rfl, rfl⟩

theorem nodup_tauList {m : ℕ} : (tauList lab m).Nodup := by
  unfold tauList
  have hF : ((List.range 256).filter fun c => inM m (lab c) (lab c)).Nodup :=
    (List.nodup_range).filter _
  rw [List.nodup_append]
  refine ⟨hF.map (fun x y h => by simpa using congrArg Prod.fst h),
    hF.map (fun x y h => by simpa using congrArg Prod.fst h), ?_⟩
  intro z hz1 z' hz2 heq
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hz1
  obtain ⟨c', -, rfl⟩ := List.mem_map.1 hz2
  simp at heq

theorem getD_labels (f : ℕ → List ℕ) {p : ℕ} (hp : p < 4) :
    ((List.range 4).map f).getD p [] = f p := by
  simp [List.getD_eq_getElem?_getD, hp]

theorem mem_byLabel {m p d : ℕ} {Lst : List ℕ} :
    d ∈ byLabel lab m p Lst ↔ d ∈ Lst ∧ inM m p (lab d) = true := by
  simp [byLabel]

theorem mem_cenBase (hlab : ∀ i, i < 256 → lab i < 4) {a b m c d : ℕ} {e : Bool} :
    (c, d, e) ∈ cenBase mt lab m a b ↔ e = false ∧ c < 256 ∧ d < 256 ∧ mt a c = mt c a ∧
      mt b d = mt d b ∧ inM m (lab c) (lab d) = true := by
  unfold cenBase
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map, Prod.mk.injEq,
    beq_iff_eq]
  constructor
  · rintro ⟨c', ⟨hc', hac⟩, d', hd', rfl, rfl, rfl⟩
    rw [getD_labels _ (hlab c' hc'), mem_byLabel] at hd'
    simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hd'
    exact ⟨rfl, hc', hd'.1.1, hac, hd'.1.2, hd'.2⟩
  · rintro ⟨rfl, hc, hd, hac, hbd, hin⟩
    refine ⟨c, ⟨hc, hac⟩, d, ?_, rfl, rfl, rfl⟩
    rw [getD_labels _ (hlab c hc), mem_byLabel]
    simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨⟨hd, hbd⟩, hin⟩

theorem mem_cenSwap (hlab : ∀ i, i < 256 → lab i < 4) {a b m c d : ℕ} {e : Bool} :
    (c, d, e) ∈ cenSwap mt lab m a b ↔ e = true ∧ c < 256 ∧ d < 256 ∧ mt a c = mt c b ∧
      mt b d = mt d a ∧ inM m (lab c) (lab d) = true := by
  unfold cenSwap
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map, Prod.mk.injEq,
    beq_iff_eq]
  constructor
  · rintro ⟨c', ⟨hc', hac⟩, d', hd', rfl, rfl, rfl⟩
    rw [getD_labels _ (hlab c' hc'), mem_byLabel] at hd'
    simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hd'
    exact ⟨rfl, hc', hd'.1.1, hac, hd'.1.2, hd'.2⟩
  · rintro ⟨rfl, hc, hd, hac, hbd, hin⟩
    refine ⟨c, ⟨hc, hac⟩, d, ?_, rfl, rfl, rfl⟩
    rw [getD_labels _ (hlab c hc), mem_byLabel]
    simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨⟨hd, hbd⟩, hin⟩

theorem nodup_flatMap_pairs {A : List ℕ} (hA : A.Nodup) (f : ℕ → List ℕ) (e : Bool)
    (hf : ∀ c ∈ A, (f c).Nodup) :
    (A.flatMap fun c => (f c).map fun d => (c, d, e)).Nodup := by
  rw [List.nodup_flatMap]
  have inj : ∀ c : ℕ, Function.Injective (fun d : ℕ => ((c, d, e) : ℕ × ℕ × Bool)) :=
    fun c x y h => by simpa using h
  refine ⟨fun c hc => (hf c hc).map (inj c), ?_⟩
  refine List.Pairwise.imp (fun {c c'} hne => ?_) hA
  dsimp only [Function.onFun]
  rw [List.disjoint_left]
  intro z hz1 hz2
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hz1
  obtain ⟨d', -, h⟩ := List.mem_map.1 hz2
  have h1 : c' = c := by simpa using congrArg Prod.fst h
  exact hne h1.symm

theorem nodup_cenBase (hlab : ∀ i, i < 256 → lab i < 4) {a b m : ℕ} :
    (cenBase mt lab m a b).Nodup := by
  unfold cenBase
  refine nodup_flatMap_pairs ((List.nodup_range).filter _) _ false fun c hc => ?_
  simp only [List.mem_filter, List.mem_range] at hc
  rw [getD_labels _ (hlab c hc.1)]
  unfold byLabel
  exact ((List.nodup_range).filter _).filter _

theorem nodup_cenSwap (hlab : ∀ i, i < 256 → lab i < 4) {a b m : ℕ} :
    (cenSwap mt lab m a b).Nodup := by
  unfold cenSwap
  refine nodup_flatMap_pairs ((List.nodup_range).filter _) _ true fun c hc => ?_
  simp only [List.mem_filter, List.mem_range] at hc
  rw [getD_labels _ (hlab c hc.1)]
  unfold byLabel
  exact ((List.nodup_range).filter _).filter _

theorem nodup_cenList (hlab : ∀ i, i < 256 → lab i < 4) {a b m : ℕ} :
    (cenList mt lab m a b).Nodup := by
  unfold cenList
  rw [List.nodup_append]
  refine ⟨nodup_cenBase hlab, nodup_cenSwap hlab, ?_⟩
  intro z hz1 z' hz2 heq
  obtain ⟨c, d, e⟩ := z
  obtain ⟨c', d', e'⟩ := z'
  have h1 := (mem_cenBase hlab).1 hz1
  have h2 := (mem_cenSwap hlab).1 hz2
  have : (c, d, e) = (c', d', e') := heq
  simp only [Prod.mk.injEq] at this
  rw [this.2.2] at h1
  rw [h1.1] at h2
  exact absurd h2.1 (by simp)

theorem natCard_subtype_list {α : Type} [DecidableEq α] {L : List α} (hL : L.Nodup) (P : α → Prop)
    [DecidablePred P] :
    Nat.card {x : {x // x ∈ L} // P x.1} = (L.filter fun x => decide (P x)).length := by
  have hnd : (L.filter fun x => decide (P x)).Nodup := hL.filter _
  have e : {x : {x // x ∈ L} // P x.1} ≃ {x // x ∈ L.filter fun x => decide (P x)} :=
    { toFun := fun x => ⟨x.1.1, List.mem_filter.2 ⟨x.1.2, by simpa using x.2⟩⟩
      invFun := fun x =>
        ⟨⟨x.1, (List.mem_filter.1 x.2).1⟩, by simpa using (List.mem_filter.1 x.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

structure ListsC (I : Indexing T mt) (C : Subgroup (Wr Q)) (L : List WEl) : Prop where
  nodup : L.Nodup
  valid : ∀ v ∈ L, Valid v
  mem : ∀ w, w ∈ C ↔ ∃ v ∈ L, evq I v = w

namespace ListsC

variable {C : Subgroup (Wr Q)} {L : List WEl} (h : ListsC I C L)

include h

@[expose] noncomputable def equiv : {v : WEl // v ∈ L} ≃ ↥C :=
  Equiv.ofBijective (fun v => ⟨evq I v.1, (h.mem _).2 ⟨v.1, v.2, rfl⟩⟩)
    ⟨fun v v' hvv => Subtype.ext (evq_inj (h.valid _ v.2) (h.valid _ v'.2)
      (congrArg Subtype.val hvv)), fun w => by
      obtain ⟨v, hv, hvw⟩ := (h.mem w.1).1 w.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩⟩

theorem coe_equiv (v : {v : WEl // v ∈ L}) : (h.equiv v : Wr Q) = evq I v.1 := rfl

theorem natCard : Nat.card C = L.length := by
  rw [← Nat.card_congr h.equiv,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h.nodup]

theorem natCard_order {k : ℕ} (hk : k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16) :
    Nat.card {g : ↥C // orderOf g = k} = (L.filter fun v => wOrd mt v == k).length := by
  have hiff : ∀ x : {x // x ∈ L}, wOrd mt x.1 = k ↔ orderOf (h.equiv x) = k := by
    intro x
    rw [← Subgroup.orderOf_coe, h.coe_equiv]
    obtain ⟨h2, h4, h8, h16⟩ := wOrd_spec (I := I) (h.valid _ x.2)
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  have e : {x : {x // x ∈ L} // wOrd mt x.1 = k} ≃ {g : ↥C // orderOf g = k} :=
    Equiv.subtypeEquiv h.equiv hiff
  rw [← Nat.card_congr e]
  refine (natCard_subtype_list h.nodup (fun a => wOrd mt a = k)).trans ?_
  congr 1

theorem natCard_center : Nat.card (center ↥C) = zOf mt L := by
  have hiff : ∀ x : {x // x ∈ L}, (∀ v' ∈ L, wmul mt x.1 v' = wmul mt v' x.1) ↔
      h.equiv x ∈ center ↥C := by
    intro x
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hc g
      obtain ⟨y, rfl⟩ := h.equiv.surjective g
      apply Subtype.ext
      have := hc y.1 y.2
      have hx := h.valid _ x.2
      have hy := h.valid _ y.2
      show evq I y.1 * evq I x.1 = evq I x.1 * evq I y.1
      rw [← evq_mul hy hx, ← evq_mul hx hy, this]
    · intro hc v' hv'
      have := congrArg Subtype.val (hc (h.equiv ⟨v', hv'⟩))
      have hx := h.valid _ x.2
      have hy := h.valid _ hv'
      change evq I v' * evq I x.1 = evq I x.1 * evq I v' at this
      rw [← evq_mul hy hx, ← evq_mul hx hy] at this
      exact (evq_inj (valid_wmul I hx hy) (valid_wmul I hy hx) this.symm)
  have e : {x : {x // x ∈ L} // ∀ v' ∈ L, wmul mt x.1 v' = wmul mt v' x.1} ≃
      {g : ↥C // g ∈ center ↥C} := Equiv.subtypeEquiv h.equiv hiff
  classical
  have : Nat.card (center ↥C) = Nat.card {g : ↥C // g ∈ center ↥C} := rfl
  rw [this, ← Nat.card_congr e]
  refine (natCard_subtype_list h.nodup
    (fun a => ∀ v' ∈ L, wmul mt a v' = wmul mt v' a)).trans ?_
  unfold zOf
  congr 1
  apply List.filter_congr
  intro v _
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, beq_iff_eq]

end ListsC

theorem exists_valid_of_mem_sub {w : Wr Q} (hw : w ∈ Wr.sub T) :
    ∃ v : WEl, Valid v ∧ evq I v = w := by
  obtain ⟨i, hi, hia⟩ := (I.mem w.a).1 hw.1
  obtain ⟨j, hj, hjb⟩ := (I.mem w.b).1 hw.2
  exact ⟨(i, j, w.e), ⟨hi, hj⟩, by simp [evq, hia, hjb]⟩

theorem elt_eq_iff {i j : ℕ} (hi : i < 256) (hj : j < 256) : I.elt i = I.elt j ↔ i = j :=
  ⟨I.inj i j hi hj, fun h => h ▸ rfl⟩

theorem comm_iff_mt {a b c d : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (e : Bool) :
    (⟨I.elt c, I.elt d, e⟩ : Wr Q) * ⟨I.elt a, I.elt b, false⟩ =
        ⟨I.elt a, I.elt b, false⟩ * ⟨I.elt c, I.elt d, e⟩ ↔
      (e = false → mt a c = mt c a ∧ mt b d = mt d b) ∧
      (e = true → mt a c = mt c b ∧ mt b d = mt d a) := by
  rw [comm_base_iff]
  have k1 : I.elt c * I.elt a = I.elt a * I.elt c ↔ mt a c = mt c a := by
    rw [← I.mul c a hc ha, ← I.mul a c ha hc, elt_eq_iff (I.mul_lt c a hc ha) (I.mul_lt a c ha hc)]
    exact eq_comm
  have k2 : I.elt d * I.elt b = I.elt b * I.elt d ↔ mt b d = mt d b := by
    rw [← I.mul d b hd hb, ← I.mul b d hb hd, elt_eq_iff (I.mul_lt d b hd hb) (I.mul_lt b d hb hd)]
    exact eq_comm
  have k3 : I.elt c * I.elt b = I.elt a * I.elt c ↔ mt a c = mt c b := by
    rw [← I.mul c b hc hb, ← I.mul a c ha hc, elt_eq_iff (I.mul_lt c b hc hb) (I.mul_lt a c ha hc)]
    exact eq_comm
  have k4 : I.elt d * I.elt a = I.elt b * I.elt d ↔ mt b d = mt d a := by
    rw [← I.mul d a hd ha, ← I.mul b d hb hd, elt_eq_iff (I.mul_lt d a hd ha) (I.mul_lt b d hb hd)]
    exact eq_comm
  rw [k1, k2, k3, k4]

variable {U : Subgroup Q} {lab : ℕ → ℕ} {ladd : ℕ → ℕ → ℕ}

theorem listsC_tau (L : Labels I U lab ladd) {R : Subgroup (Wr Q)} (hRT : R ≤ Wr.sub T)
    (hSS : Wr.ss U ≤ R) (hsw : (Wr.swap : Wr Q) ∈ R) {m : ℕ}
    (hm : ∀ p q, p < 4 → q < 4 → (inM m p q = true ↔ LabelSet I lab R p q)) :
    ListsC I (R ⊓ centralizer {(Wr.swap : Wr Q)}) (tauList lab m) := by
  refine ⟨nodup_tauList, fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨c, d, e⟩ := v
    obtain ⟨h1, h2, -⟩ := mem_tauList.1 hv
    exact ⟨h1, h2 ▸ h1⟩
  · constructor
    · rintro ⟨hwR, hwc⟩
      obtain ⟨v, hv, rfl⟩ := exists_valid_of_mem_sub (I := I) (hRT hwR)
      obtain ⟨c, d, e⟩ := v
      have hcomm := (Subgroup.mem_centralizer_singleton_iff.1 hwc)
      have hab := (comm_swap_iff _).1 hcomm
      have hcd : c = d := (elt_eq_iff hv.1 hv.2).1 hab
      subst hcd
      have hbit := (mem_iff_mask L hSS hsw hm hv).1 hwR
      exact ⟨(c, c, e), mem_tauList.2 ⟨hv.1, rfl, hbit⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨c, d, e⟩ := v
      obtain ⟨h1, h2, h3⟩ := mem_tauList.1 hv
      subst h2
      exact ⟨(mem_iff_mask L hSS hsw hm ⟨h1, h1⟩).2 h3,
        Subgroup.mem_centralizer_singleton_iff.2 ((comm_swap_iff _).2 rfl)⟩

theorem listsC_cen (L : Labels I U lab ladd) {R : Subgroup (Wr Q)} (hRT : R ≤ Wr.sub T)
    (hSS : Wr.ss U ≤ R) (hsw : (Wr.swap : Wr Q) ∈ R) {m : ℕ}
    (hm : ∀ p q, p < 4 → q < 4 → (inM m p q = true ↔ LabelSet I lab R p q)) {a b : ℕ}
    (ha : a < 256) (hb : b < 256) :
    ListsC I (R ⊓ centralizer {(⟨I.elt a, I.elt b, false⟩ : Wr Q)}) (cenList mt lab m a b) := by
  have hmem : ∀ c d e, c < 256 → d < 256 →
      ((c, d, e) ∈ cenList mt lab m a b ↔ (⟨I.elt c, I.elt d, e⟩ : Wr Q) ∈ R ∧
        (⟨I.elt c, I.elt d, e⟩ : Wr Q) ∈ centralizer {(⟨I.elt a, I.elt b, false⟩ : Wr Q)}) := by
    intro c d e hc hd
    have hR : (⟨I.elt c, I.elt d, e⟩ : Wr Q) ∈ R ↔ inM m (lab c) (lab d) = true :=
      mem_iff_mask L hSS hsw hm (v := (c, d, e)) ⟨hc, hd⟩
    rw [Subgroup.mem_centralizer_singleton_iff, comm_iff_mt ha hb hc hd, hR, cenList,
      List.mem_append, mem_cenBase L.lt, mem_cenSwap L.lt]
    cases e <;> simp [hc, hd] <;> tauto
  refine ⟨nodup_cenList L.lt, fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨c, d, e⟩ := v
    rcases List.mem_append.1 hv with h | h
    · obtain ⟨-, h1, h2, -⟩ := (mem_cenBase L.lt).1 h
      exact ⟨h1, h2⟩
    · obtain ⟨-, h1, h2, -⟩ := (mem_cenSwap L.lt).1 h
      exact ⟨h1, h2⟩
  · have hvalid : ∀ v ∈ cenList mt lab m a b, Valid v := by
      intro v hv
      obtain ⟨c, d, e⟩ := v
      rcases List.mem_append.1 hv with h | h
      · obtain ⟨-, h1, h2, -⟩ := (mem_cenBase L.lt).1 h
        exact ⟨h1, h2⟩
      · obtain ⟨-, h1, h2, -⟩ := (mem_cenSwap L.lt).1 h
        exact ⟨h1, h2⟩
    constructor
    · rintro ⟨hwR, hwc⟩
      obtain ⟨v, hv, rfl⟩ := exists_valid_of_mem_sub (I := I) (hRT hwR)
      obtain ⟨c, d, e⟩ := v
      exact ⟨(c, d, e), (hmem c d e hv.1 hv.2).2 ⟨hwR, hwc⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨c, d, e⟩ := v
      exact (hmem c d e (hvalid _ hv).1 (hvalid _ hv).2).1 hv

theorem ordStats_eq (L : List WEl) :
    ordStats mt L = [2, 4, 8, 16].map fun k => (L.filter fun v => wOrd mt v == k).length := by
  unfold ordStats
  simp only [List.filter_map, List.length_map]
  rfl

theorem mem_center_equiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) (g : A) :
    g ∈ center A ↔ f g ∈ center B := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h b
    obtain ⟨a, rfl⟩ := f.surjective b
    rw [← map_mul, ← map_mul, h a]
  · intro h a
    apply f.injective
    rw [map_mul, map_mul]
    exact h (f a)

theorem fb6_sound (L : Labels I U lab ladd) (h : fb6Check mt lab ladd = true)
    {R : Subgroup (Wr Q)} (hRT : R ≤ Wr.sub T) (hSS : Wr.ss U ≤ R) (hsw : (Wr.swap : Wr Q) ∈ R)
    {x : Wr Q} (hxR : x ∈ R) (hxe : x.e = false) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ Nonempty (↥(R ⊓ centralizer {x}) ≃* ↥(R ⊓ centralizer {(Wr.swap : Wr Q)})) := by
  classical
  obtain ⟨v, hv, hxv⟩ := exists_valid_of_mem_sub (I := I) (hRT hxR)
  obtain ⟨a, b, e⟩ := v
  have ha : a < 256 := hv.1
  have hb : b < 256 := hv.2
  have hx' : x = ⟨I.elt a, I.elt b, e⟩ := hxv.symm
  have he : e = false := by rw [hx'] at hxe; exact hxe
  subst he
  subst hx'
  rintro ⟨f⟩
  obtain ⟨m, hm65, hm⟩ := exists_mask (LabelSet I lab R)
  have hadm := admM_true L hsw hm
  have hall := h
  unfold fb6Check at hall
  rw [List.all_eq_true] at hall
  have hmain := hall m (List.mem_range.2 hm65)
  rw [hadm] at hmain
  simp only [Bool.not_true, Bool.false_or] at hmain
  unfold mainOK mainAux at hmain
  rw [List.all_eq_true] at hmain
  have hainv : a ∈ (List.range 256).filter fun i => mt i i == 0 := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨ha, ?_⟩
    have := congrArg Wr.a hx2
    simp only [Wr.mk_mul_mk_false, Wr.one_def] at this
    simpa using I.mt_sq ha this
  have hbinv : b ∈ (List.range 256).filter fun i => mt i i == 0 := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨hb, ?_⟩
    have := congrArg Wr.b hx2
    simp only [Wr.mk_mul_mk_false, Wr.one_def] at this
    simpa using I.mt_sq hb this
  have hmain2 := (List.all_eq_true.1 (hmain a hainv)) b hbinv
  have hne : ¬ (a == 0 && b == 0) = true := by
    intro hab
    simp only [Bool.and_eq_true, beq_iff_eq] at hab
    apply hx1
    obtain ⟨rfl, rfl⟩ := hab
    simp [I.one, Wr.one_def]
  have hbit : inM m (lab a) (lab b) = true :=
    (hm _ _ (L.lt a ha) (L.lt b hb)).2 ⟨a, b, ha, hb, rfl, rfl, hxR⟩
  have hd : differs mt (cenList mt lab m a b) (tauList lab m).length
      (ordStats mt (tauList lab m)) (zOf mt (tauList lab m)) = true := by
    simp only [Bool.or_eq_true] at hmain2
    rcases hmain2 with h1 | h1
    · rcases h1 with h2 | h2
      · exact absurd h2 hne
      · simp [hbit] at h2
    · exact h1
  have hC := listsC_cen L hRT hSS hsw hm ha hb
  have hT := listsC_tau L hRT hSS hsw hm
  have e1 : (cenList mt lab m a b).length = (tauList lab m).length := by
    rw [← hC.natCard, ← hT.natCard]
    exact Nat.card_congr f.toEquiv
  have e3 : zOf mt (cenList mt lab m a b) = zOf mt (tauList lab m) := by
    rw [← hC.natCard_center, ← hT.natCard_center]
    exact Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun g => mem_center_equiv f g)
  have e2 : ordStats mt (cenList mt lab m a b) = ordStats mt (tauList lab m) := by
    rw [ordStats_eq, ordStats_eq]
    apply List.map_congr_left
    intro k hk
    have hk' : k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 := by simpa using hk
    rw [← hC.natCard_order hk', ← hT.natCard_order hk']
    exact Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun g => by
      rw [show orderOf (f.toEquiv g) = orderOf g from MulEquiv.orderOf_eq f g])
  unfold differs at hd
  simp [e1, e2, e3] at hd

end FB6

end CFSG.OddStandard.Seitz77.CaseB45
