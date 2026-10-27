module

public import CFSG.Open.LocalVocabulary

public section

open Equiv Finset Subgroup MulAction CFSG.Open
open scoped Classical

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Orbit

variable {n : ℕ}

noncomputable def orbF (P : Subgroup (Perm (Fin n))) (t : Fin n) : Finset (Fin n) :=
  univ.filter fun s => ∃ g : P, (g : Perm (Fin n)) t = s

theorem mem_orbF (P : Subgroup (Perm (Fin n))) {t s : Fin n} :
    s ∈ orbF P t ↔ ∃ g : P, (g : Perm (Fin n)) t = s := by
  simp [orbF]

theorem coe_orbF (P : Subgroup (Perm (Fin n))) (t : Fin n) :
    ((orbF P t : Finset (Fin n)) : Set (Fin n)) = MulAction.orbit P t := by
  ext s
  rw [Finset.mem_coe, mem_orbF, MulAction.mem_orbit_iff]
  rfl

theorem card_orbF_eq (P : Subgroup (Perm (Fin n))) (t : Fin n) :
    (orbF P t).card = (MulAction.stabilizer P t).index := by
  rw [MulAction.index_stabilizer, ← coe_orbF, Set.ncard_coe_finset]

abbrev stabP (P : Subgroup (Perm (Fin n))) (t : Fin n) : Subgroup P :=
  MulAction.stabilizer P t

theorem mem_stabP (P : Subgroup (Perm (Fin n))) {t : Fin n} {g : P} :
    g ∈ stabP P t ↔ (g : Perm (Fin n)) t = t := by
  rw [MulAction.mem_stabilizer_iff]
  rfl

theorem perm_mul_apply_comm (P : Subgroup (Perm (Fin n))) (hcomm : ∀ g h : P, g * h = h * g)
    (g h : P) (t : Fin n) :
    (g : Perm (Fin n)) ((h : Perm (Fin n)) t) = (h : Perm (Fin n)) ((g : Perm (Fin n)) t) := by
  have hgh : (g : Perm (Fin n)) * (h : Perm (Fin n)) = (h : Perm (Fin n)) * (g : Perm (Fin n)) := by
    have := congrArg (fun x : P => (x : Perm (Fin n))) (hcomm g h)
    simpa using this
  rw [← Equiv.Perm.mul_apply, hgh, Equiv.Perm.mul_apply]

theorem perm_inv_apply_apply' (σ : Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by simp

theorem pow_ge_mul_add {p : ℕ} (hp : 3 ≤ p) : ∀ j : ℕ, 2 ≤ j → p * j + p ≤ p ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => nlinarith
  | succ m hm ih =>
    rw [pow_succ]
    have := Nat.mul_le_mul_right p ih
    nlinarith [Nat.le_mul_of_pos_right (p * m) (show 0 < p by omega),
      Nat.mul_le_mul_right p (show 2 ≤ p by omega)]

theorem mem_finset_inf' {Q : Type*} [Group Q] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Subgroup Q) (x : Q) : x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Subgroup.mem_inf, ih, Finset.forall_mem_insert]

theorem index_inf_finset_le {Q : Type*} [Group Q] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Subgroup Q) : (s.inf f).index ≤ ∏ i ∈ s, (f i).index := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha]
    exact (Subgroup.index_inf_le).trans (Nat.mul_le_mul_left _ ih)

theorem exists_rep (P : Subgroup (Perm (Fin n))) (hcomm : ∀ g h : P, g * h = h * g) (s : Fin n) :
    ∃ r : Fin n, (∀ g : P, r ≤ (g : Perm (Fin n)) r) ∧ s ∈ orbF P r := by
  have hne : (orbF P s).Nonempty := ⟨s, (mem_orbF P).2 ⟨1, by simp⟩⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (orbF P s) id hne
  have hrs : r ∈ orbF P s := hr
  obtain ⟨h, hh⟩ := (mem_orbF P).1 hrs
  have hsr : s ∈ orbF P r := (mem_orbF P).2 ⟨h⁻¹, by
    rw [← hh]
    simp⟩
  refine ⟨r, fun g => hmin _ ?_, hsr⟩
  rw [mem_orbF]
  refine ⟨g * h, ?_⟩
  rw [← hh, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem rep_unique (P : Subgroup (Perm (Fin n))) (hcomm : ∀ g h : P, g * h = h * g) {r r' : Fin n}
    (hr : ∀ g : P, r ≤ (g : Perm (Fin n)) r) (hr' : ∀ g : P, r' ≤ (g : Perm (Fin n)) r')
    {s : Fin n} (hs : s ∈ orbF P r) (hs' : s ∈ orbF P r') : r = r' := by
  obtain ⟨g, hg⟩ := (mem_orbF P).1 hs
  obtain ⟨g', hg'⟩ := (mem_orbF P).1 hs'
  set x : P := g'⁻¹ * g with hx
  have hxr : (x : Perm (Fin n)) r = r' := by
    rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hg, ← hg',
      perm_inv_apply_apply']
  have h1 : r ≤ r' := by
    have := hr x
    rwa [hxr] at this
  have h2 : r' ≤ r := by
    have hinv : ((x⁻¹ : P) : Perm (Fin n)) r' = r := by
      rw [← hxr, Subgroup.coe_inv, perm_inv_apply_apply']
    have := hr' x⁻¹
    rwa [hinv] at this
  exact le_antisymm h1 h2

theorem eq_one_of_fix_reps (P : Subgroup (Perm (Fin n))) (hcomm : ∀ g h : P, g * h = h * g)
    (R : Finset (Fin n)) (hrep : ∀ s : Fin n, ∃ r ∈ R, s ∈ orbF P r) (g : P)
    (hg : ∀ r ∈ R, g ∈ stabP P r) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro t
  obtain ⟨r, hr, hsr⟩ := hrep t
  obtain ⟨h, hh⟩ := (mem_orbF P).1 hsr
  have hgr : (g : Perm (Fin n)) r = r := (mem_stabP P).1 (hg r hr)
  rw [← hh, perm_mul_apply_comm P hcomm g h r, hgr]
  simp

theorem sum_card_orbF_le (P : Subgroup (Perm (Fin n))) (R : Finset (Fin n))
    (hdisj : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (orbF P r) (orbF P r')) :
    ∑ r ∈ R, (orbF P r).card ≤ n := by
  have h1 : (R.biUnion (orbF P)).card = ∑ r ∈ R, (orbF P r).card :=
    Finset.card_biUnion (fun r hr r' hr' hne => hdisj r hr r' hr' hne)
  have h2 : (R.biUnion (orbF P)).card ≤ n := by
    have := Finset.card_le_univ (R.biUnion (orbF P))
    simpa using this
  omega

theorem mul_add_le_pow {p : ℕ} (hp : 3 ≤ p) (j : ℕ) :
    p * j + p * (if 2 ≤ j then 1 else 0) ≤ p ^ j := by
  by_cases hj : 2 ≤ j
  · rw [if_pos hj]
    have := pow_ge_mul_add hp j hj
    linarith
  · rw [if_neg hj]
    interval_cases j
    · simp
    · simp

theorem pcycle_of_rep {p : ℕ} (hp : p.Prime) (P : Subgroup (Perm (Fin n)))
    (hP : IsElemAbelian p P) (R R1 : Finset (Fin n))
    (hcomm : ∀ g h : P, g * h = h * g)
    (hrep : ∀ s, ∃ r ∈ R, s ∈ orbF P r)
    (hstab_out : ∀ r ∈ R, r ∉ R1 → stabP P r = ⊤)
    (r₁ : Fin n) (hr₁ : r₁ ∈ R1)
    (hQne : (R1.erase r₁).inf (stabP P) ≠ ⊥)
    (hQinf : (R1.erase r₁).inf (stabP P) ⊓ stabP P r₁ = ⊥) :
    ∃ a : P, a ≠ 1 ∧ ∀ j : ℕ, ¬ p ∣ j → ∀ t : Fin n,
      ((a ^ j : P) : Perm (Fin n)) t ≠ t ↔ t ∈ orbF P r₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hap : a ^ p = 1 := by
    apply Subtype.ext
    simpa using hP.2 _ a.2
  have hord : orderOf a = p := orderOf_eq_prime hap ha1'
  have hpow_iff : ∀ j : ℕ, p ∣ j ↔ a ^ j = 1 := fun j => by
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
  refine ⟨a, ha1', ?_⟩
  intro j hj
  have hnofix : ((a ^ j : P) : Perm (Fin n)) r₁ ≠ r₁ := by
    intro h
    have hmem : a ^ j ∈ (R1.erase r₁).inf (stabP P) ⊓ stabP P r₁ :=
      ⟨Subgroup.pow_mem _ ha j, (mem_stabP P).2 h⟩
    rw [hQinf, Subgroup.mem_bot] at hmem
    exact hj ((hpow_iff j).2 hmem)
  intro t
  constructor
  · intro hne
    by_contra hnot
    obtain ⟨r, hrR, htr⟩ := hrep t
    obtain ⟨g, hg⟩ := (mem_orbF P).1 htr
    have hrr : r ≠ r₁ := by
      rintro rfl
      exact hnot htr
    have hfix : ((a ^ j : P) : Perm (Fin n)) r = r := by
      by_cases hr1 : r ∈ R1
      · have hmem : a ^ j ∈ (R1.erase r₁).inf (stabP P) :=
          Subgroup.pow_mem _ ha j
        rw [mem_finset_inf'] at hmem
        exact (mem_stabP P).1 (hmem r (Finset.mem_erase.2 ⟨hrr, hr1⟩))
      · have : a ^ j ∈ stabP P r := by
          rw [hstab_out r hrR hr1]
          exact Subgroup.mem_top _
        exact (mem_stabP P).1 this
    apply hne
    rw [← hg, perm_mul_apply_comm P hcomm (a ^ j) g r, hfix]
  · intro ht heq
    obtain ⟨g, hg⟩ := (mem_orbF P).1 ht
    rw [← hg, perm_mul_apply_comm P hcomm (a ^ j) g r₁] at heq
    exact hnofix ((g : Perm (Fin n)).apply_eq_iff_eq.1 heq)

theorem orbit_pCycles {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (P : Subgroup (Perm (Fin n))) (hP : IsElemAbelian p P)
    (hcard : p ^ (n / p) ≤ Nat.card P) :
    Nat.card P = p ^ (n / p) ∧
      (2 ≤ n / p → ∃ a b : Perm (Fin n), a ∈ P ∧ b ∈ P ∧ ∃ A B : Finset (Fin n),
        A.card = p ∧ B.card = p ∧ Disjoint A B ∧
        (∀ j : ℕ, ¬ p ∣ j → ∀ t : Fin n, (a ^ j) t ≠ t ↔ t ∈ A) ∧
        (∀ j : ℕ, ¬ p ∣ j → ∀ t : Fin n, (b ^ j) t ≠ t ↔ t ∈ B)) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = n / p := ⟨_, rfl⟩
  rw [← hk] at hcard ⊢
  have hcomm : ∀ g h : P, g * h = h * g := fun g h => hP.1.is_comm.comm g h
  haveI : Fact p.Prime := ⟨hp⟩
  have hpgrp : IsPGroup p P := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hP.2 _ g.2
  obtain ⟨e, he⟩ := hpgrp.exists_card_eq
  obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin n),
      R = univ.filter (fun r => ∀ g : P, r ≤ (g : Perm (Fin n)) r) := ⟨_, rfl⟩
  have hR_mem : ∀ r, r ∈ R ↔ ∀ g : P, r ≤ (g : Perm (Fin n)) r := by
    intro r; rw [hRdef]; simp
  have hrep : ∀ s, ∃ r ∈ R, s ∈ orbF P r := fun s => by
    obtain ⟨r, hr, hs⟩ := exists_rep P hcomm s
    exact ⟨r, (hR_mem r).2 hr, hs⟩
  have hdisj : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (orbF P r) (orbF P r') := by
    intro r hr r' hr' hne
    rw [Finset.disjoint_left]
    intro s hs hs'
    exact hne (rep_unique P hcomm ((hR_mem r).1 hr) ((hR_mem r').1 hr') hs hs')
  have hdvd : ∀ r, (orbF P r).card ∣ p ^ e := fun r => by
    rw [← he, card_orbF_eq]; exact Subgroup.index_dvd_card _
  have hpow : ∀ r, ∃ j, (orbF P r).card = p ^ j := fun r => by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (hdvd r)
    exact ⟨j, hj⟩
  choose jf hjf using hpow
  obtain ⟨R1, hR1def⟩ : ∃ R1 : Finset (Fin n),
      R1 = R.filter (fun r => 1 < (orbF P r).card) := ⟨_, rfl⟩
  have hR1_mem : ∀ r, r ∈ R1 ↔ r ∈ R ∧ 1 < (orbF P r).card := by
    intro r; rw [hR1def]; simp
  have hR1sub : R1 ⊆ R := fun r hr => ((hR1_mem r).1 hr).1
  have hstab_out : ∀ r ∈ R, r ∉ R1 → stabP P r = ⊤ := by
    intro r hr hnot
    have hle : (orbF P r).card ≤ 1 := by
      by_contra h
      exact hnot ((hR1_mem r).2 ⟨hr, by omega⟩)
    have hpos : 0 < (orbF P r).card :=
      Finset.card_pos.2 ⟨r, (mem_orbF P).2 ⟨1, by simp⟩⟩
    rw [← Subgroup.index_eq_one, ← card_orbF_eq]
    omega
  have hfaith : ∀ g : P, (∀ r ∈ R1, g ∈ stabP P r) → g = 1 := by
    intro g hg
    apply eq_one_of_fix_reps P hcomm R hrep g
    intro r hr
    by_cases h1 : r ∈ R1
    · exact hg r h1
    · rw [hstab_out r hr h1]; exact Subgroup.mem_top g
  have hinf : R1.inf (stabP P) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [mem_finset_inf'] at hg
    rw [Subgroup.mem_bot]
    exact hfaith g hg
  have hPeq : Nat.card P = (R1.inf (stabP P)).index := by rw [hinf, Subgroup.index_bot]
  have hprod : ∏ r ∈ R1, (orbF P r).card = p ^ (∑ r ∈ R1, jf r) := by
    rw [Finset.prod_congr rfl (fun r _ => hjf r), Finset.prod_pow_eq_pow_sum]
  obtain ⟨J, hJ⟩ : ∃ J, J = ∑ r ∈ R1, jf r := ⟨_, rfl⟩
  have hbJ : Nat.card P ≤ p ^ J := by
    have hb : Nat.card P ≤ ∏ r ∈ R1, (orbF P r).card := by
      rw [hPeq]
      refine (index_inf_finset_le R1 (stabP P)).trans (le_of_eq ?_)
      exact Finset.prod_congr rfl (fun r _ => (card_orbF_eq P r).symm)
    rw [hJ]
    exact hb.trans (le_of_eq hprod)
  have hjpos : ∀ r ∈ R1, 1 ≤ jf r := by
    intro r hr
    have h1 := ((hR1_mem r).1 hr).2
    rw [hjf r] at h1
    by_contra h0
    have h00 : jf r = 0 := by omega
    rw [h00, pow_zero] at h1
    omega
  have hsumcount : ∑ r ∈ R1, p ^ jf r ≤ n := by
    have h := sum_card_orbF_le P R1 (fun r hr r' hr' hne =>
      hdisj r (hR1sub hr) r' (hR1sub hr') hne)
    calc ∑ r ∈ R1, p ^ jf r = ∑ r ∈ R1, (orbF P r).card :=
          Finset.sum_congr rfl (fun r _ => (hjf r).symm)
      _ ≤ n := h
  obtain ⟨m, hm⟩ : ∃ m, m = (R1.filter (fun r => 2 ≤ jf r)).card := ⟨_, rfl⟩
  have hlow : p * J + p * m ≤ ∑ r ∈ R1, p ^ jf r := by
    have h1 : ∑ r ∈ R1, (p * jf r + p * (if 2 ≤ jf r then 1 else 0)) ≤
        ∑ r ∈ R1, p ^ jf r :=
      Finset.sum_le_sum (fun r _ => mul_add_le_pow hp3 (jf r))
    have h2 : ∑ r ∈ R1, (p * jf r + p * (if 2 ≤ jf r then 1 else 0)) = p * J + p * m := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hJ, hm]
      congr 2
      simp [Finset.sum_boole]
    omega
  have hk_le : k ≤ J := by
    have h := hcard.trans hbJ
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hn_lt : n < p * (k + 1) := by
    have := Nat.lt_mul_div_succ n (show 0 < p by omega)
    rw [← hk] at this
    linarith [mul_comm p (k + 1)]
  have hJm : J + m ≤ k := by
    have h3 : p * (J + m) < p * (k + 1) := by
      rw [Nat.mul_add]
      linarith
    exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h3)
  have hm0 : m = 0 := by omega
  have hJk : J = k := by omega
  have hj1 : ∀ r ∈ R1, jf r = 1 := by
    intro r hr
    have h1 : ¬ 2 ≤ jf r := by
      intro h2
      have hmem : r ∈ R1.filter (fun r => 2 ≤ jf r) := Finset.mem_filter.2 ⟨hr, h2⟩
      have hpos : 0 < (R1.filter (fun r => 2 ≤ jf r)).card :=
        Finset.card_pos.2 ⟨r, hmem⟩
      omega
    have := hjpos r hr
    omega
  have hR1card : R1.card = k := by
    have h1 : J = R1.card := by
      rw [hJ, Finset.sum_congr rfl (fun r hr => hj1 r hr)]
      simp
    omega
  have hcardP : Nat.card P = p ^ k := by
    apply le_antisymm
    · rw [← hJk]; exact hbJ
    · exact hcard
  refine ⟨hcardP, fun hk2 => ?_⟩
  obtain ⟨r₁, hr₁, r₂, hr₂, hne12⟩ := Finset.one_lt_card.1 (by rw [hR1card]; exact hk2)
  have hA1 : (orbF P r₁).card = p := by rw [hjf r₁, hj1 r₁ hr₁, pow_one]
  have hA2 : (orbF P r₂).card = p := by rw [hjf r₂, hj1 r₂ hr₂, pow_one]
  have hQne : ∀ r ∈ R1, (R1.erase r).inf (stabP P) ≠ ⊥ := by
    intro r hr hbot
    have h1 := index_inf_finset_le (R1.erase r) (stabP P)
    rw [hbot, Subgroup.index_bot, hcardP] at h1
    have h2 : ∏ i ∈ R1.erase r, (stabP P i).index = p ^ (R1.erase r).card := by
      have hi : ∀ i ∈ R1.erase r, (stabP P i).index = p := by
        intro i hi
        have hiR1 := Finset.mem_of_mem_erase hi
        rw [← card_orbF_eq, hjf i, hj1 i hiR1, pow_one]
      rw [Finset.prod_congr rfl hi, Finset.prod_const]
    have hcard_erase : (R1.erase r).card = k - 1 := by
      rw [Finset.card_erase_of_mem hr, hR1card]
    rw [h2, hcard_erase] at h1
    have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd h1 (not_le.2 hlt)
  have hQinf : ∀ r ∈ R1, (R1.erase r).inf (stabP P) ⊓ stabP P r = ⊥ := by
    intro r hr
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgQ, hgr⟩ := hg
    rw [Subgroup.mem_bot]
    apply hfaith g
    intro r' hr'
    by_cases hrr : r' = r
    · rw [hrr]; exact hgr
    · exact (mem_finset_inf' _ _ _).1 hgQ r' (Finset.mem_erase.2 ⟨hrr, hr'⟩)
  obtain ⟨a, ha1, ha⟩ := pcycle_of_rep hp P hP R R1 hcomm hrep hstab_out r₁ hr₁ (hQne r₁ hr₁)
    (hQinf r₁ hr₁)
  obtain ⟨b, hb1, hb⟩ := pcycle_of_rep hp P hP R R1 hcomm hrep hstab_out r₂ hr₂ (hQne r₂ hr₂)
    (hQinf r₂ hr₂)
  refine ⟨(a : Perm (Fin n)), (b : Perm (Fin n)), a.2, b.2, orbF P r₁, orbF P r₂, hA1, hA2,
    hdisj r₁ (hR1sub hr₁) r₂ (hR1sub hr₂) hne12, ?_, ?_⟩
  · intro j hj t
    simpa only [Subgroup.coe_pow] using ha j hj t
  · intro j hj t
    simpa only [Subgroup.coe_pow] using hb j hj t

end CFSG.LocalAnalysis.GLTheoremA.KD264Orbit
