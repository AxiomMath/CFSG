module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09A8Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I1312A8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I1312Lie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Equiv Equiv.Perm Subgroup

theorem a8_orbit_pow3 (g : Perm (Fin 8)) (hg3 : g ^ 3 = 1) (x : Fin 8) (hgx : g x ≠ x)
    (m : ℕ) (hm : (g ^ m) x = x) : 3 ∣ m := by
  have hm' : (g ^ (m % 3)) x = x := by
    have h := hm
    rw [← Nat.div_add_mod m 3, pow_add, Perm.mul_apply, pow_mul, hg3, one_pow, Perm.one_apply] at h
    exact h
  have e3 : g ^ 3 = g * g ^ 2 := by rw [← pow_succ']
  obtain h0 | h1 | h2 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  · exact Nat.dvd_of_mod_eq_zero h0
  · rw [h1, pow_one] at hm'
    exact absurd hm' hgx
  · rw [h2] at hm'
    exfalso
    apply hgx
    have : (g ^ 3) x = g ((g ^ 2) x) := by rw [e3, Perm.mul_apply]
    rw [hm', hg3, Perm.one_apply] at this
    exact this.symm

theorem a8_comm_of_mc {G : Type*} [Group G] [IsMulCommutative G] (a b : G) : a * b = b * a :=
  IsMulCommutative.is_comm.comm a b

theorem a8_three_orbit (g : Perm (Fin 8)) (hc : g.cycleType = {3}) (hg3 : g ^ 3 = 1) :
    ∃ x : Fin 8, g x ≠ x ∧ g x ≠ (g ^ 2) x ∧ x ≠ (g ^ 2) x ∧
      ∀ y, g y ≠ y → y = x ∨ y = g x ∨ y = (g ^ 2) x := by
  have hs : g.support.card = 3 := by
    have := sum_cycleType g
    rw [hc] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ : g.support.Nonempty := by
    rw [← Finset.card_pos, hs]; norm_num
  have hgx : g x ≠ x := mem_support.1 hx
  have hE : g ((g ^ 2) x) = x := by
    have e : g ^ 3 = g * g ^ 2 := pow_succ' g 2
    have := congrArg (fun π : Perm (Fin 8) => π x) hg3
    rw [e, Perm.mul_apply, Perm.one_apply] at this
    exact this
  have h2x : (g ^ 2) x ≠ x := by
    intro h
    rw [h] at hE
    exact hgx hE
  have hgg : g x ≠ (g ^ 2) x := by
    intro h
    apply hgx
    have h2 : (g ^ 2) x = g (g x) := by rw [pow_two, Perm.mul_apply]
    rw [← h] at h2
    exact (g.injective h2).symm
  have hsub : ({x, g x, (g ^ 2) x} : Finset (Fin 8)) ⊆ g.support := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [mem_support]
    rcases hy with rfl | rfl | rfl
    · exact hgx
    · intro h
      apply hgx
      have h2 : (g ^ 2) x = g x := by rw [pow_two, Perm.mul_apply, h]
      rw [h2] at hE
      exact h.symm.trans hE
    · intro h
      apply h2x
      rw [h] at hE
      exact hE
  have hcard3 : ({x, g x, (g ^ 2) x} : Finset (Fin 8)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hgg]
    simp [hgx.symm, h2x.symm]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hs])
  refine ⟨x, hgx, hgg, h2x.symm, fun y hy => ?_⟩
  have : y ∈ g.support := mem_support.2 hy
  rw [← heq] at this
  simpa using this

theorem a8_two_fixed (g : Perm (Fin 8)) (hs : g.support.card ≤ 6) :
    ∃ u v : Fin 8, u ≠ v ∧ g u = u ∧ g v = v := by
  have hcard : 1 < (Finset.univ.filter fun y : Fin 8 => g y = y).card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 8)))
      (fun y : Fin 8 => g y = y)
    have hsupp : (Finset.univ.filter fun y : Fin 8 => ¬ g y = y) = g.support := by
      ext y; simp [mem_support]
    rw [hsupp, Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcard
  exact ⟨u, v, huv, by simpa using hu, by simpa using hv⟩

theorem a8_swap_mem (g : Perm (Fin 8)) (u v : Fin 8) (hu : g u = u) (hv : g v = v) :
    swap u v ∈ centralizer {g} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := swap_apply_apply g u v
  rw [hu, hv] at h
  calc swap u v * g = (g * swap u v * g⁻¹) * g := by rw [← h]
    _ = g * swap u v := by group

theorem a8_comm_of_dvd_four (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hdiv : Nat.card R ∣ 4) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hk2 : k ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have h8 : 2 ^ 3 ∣ Nat.card R := by rw [hk]; exact pow_dvd_pow 2 hcon
    exact absurd (h8.trans hdiv) (by norm_num)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq R (by rw [hk]; rfl))
  have hcomm : IsMulCommutative R := by
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI := isCyclic_of_prime_card (p := 2) (by rw [hk]; norm_num)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hk])
  intro a ha b hb
  exact congrArg Subtype.val (a8_comm_of_mc (⟨a, ha⟩ : R) ⟨b, hb⟩)

theorem a8_exists_invol (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ∃ t ∈ R, t ≠ 1 ∧ t * t = 1 := by
  have hn : Nat.card R ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq R h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
    rw [hk]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (by rw [hk, h0]; simp) hn
    · exact dvd_pow_self 2 h0.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨x, x.2, fun h => ?_, ?_⟩
  · have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    norm_num at hx
  · have := congrArg Subtype.val hx2
    simpa [pow_two] using this

theorem a8_pow_apply_comm (g r : Perm (Fin 8)) (hgr : g * r = r * g) (x : Fin 8) (i : ℕ)
    (hi : r x = (g ^ i) x) (m : ℕ) : (r ^ m) x = (g ^ (i * m)) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : r * g ^ (i * m) = g ^ (i * m) * r :=
      (Commute.pow_right (show Commute r g from hgr.symm) (i * m)).eq
    have hx := congrArg (fun π : Perm (Fin 8) => π x) hc
    simp only [Perm.mul_apply] at hx
    rw [pow_succ', Perm.mul_apply, ih, hx, hi, ← Perm.mul_apply, ← pow_add]
    rw [show i * m + i = i * (m + 1) by ring]

theorem a8_three_card_dvd (g : Perm (Fin 8)) (hc : g.cycleType = {3}) (R : Subgroup (Perm (Fin 8)))
    (hR : IsPGroup 2 R) (hRA : ∀ r ∈ R, sign r = 1) (hcomm : ∀ r ∈ R, g * r = r * g)
    (u v : Fin 8) (huv : u ≠ v) (hu : g u = u) (hv : g v = v) : Nat.card R ∣ 4 := by
  have hsw := a8_swap_mem g u v hu hv
  have hRle : R ≤ centralizer {g} ⊓ alternatingGroup (Fin 8) := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨?_, mem_alternatingGroup.2 (hRA r hr)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm r hr).symm
  have h1 := a8_card_alt_inf (centralizer {g}) (swap u v) hsw (sign_swap huv)
  rw [a8_cent3 g hc] at h1
  have hdiv : Nat.card R ∣ Nat.card ↥(centralizer {g} ⊓ alternatingGroup (Fin 8)) :=
    Subgroup.card_dvd_of_le hRle
  have h180 : Nat.card ↥(centralizer {g} ⊓ alternatingGroup (Fin 8)) = 180 := by omega
  rw [h180] at hdiv
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hk2 : k ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have h8 : 2 ^ 3 ∣ Nat.card R := by rw [hk]; exact pow_dvd_pow 2 hcon
    exact absurd (h8.trans hdiv) (by norm_num)
  rw [hk]
  exact (pow_dvd_pow 2 hk2).trans (by norm_num)

theorem a8_pow_card_mem (R : Subgroup (Perm (Fin 8))) (r : Perm (Fin 8)) (hr : r ∈ R) :
    r ^ Nat.card R = 1 :=
  orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard R hr)

theorem a8_caseA_fix (g : Perm (Fin 8)) (hg3 : g ^ 3 = 1) (x : Fin 8) (hgx : g x ≠ x)
    (hSig : ∀ y, g y ≠ y → y = x ∨ y = g x ∨ y = (g ^ 2) x) (R : Subgroup (Perm (Fin 8)))
    (hN3 : ¬ 3 ∣ Nat.card R) (hcomm : ∀ r ∈ R, g * r = r * g) :
    ∀ r ∈ R, r x = x ∧ r (g x) = g x ∧ r ((g ^ 2) x) = (g ^ 2) x := by
  intro r hr
  have hgr : g * r = r * g := hcomm r hr
  have hgr' : ∀ y, g (r y) = r (g y) := fun y => by
    have := congrArg (fun π : Perm (Fin 8) => π y) hgr
    simpa [Perm.mul_apply] using this
  have hsupp : g (r x) ≠ r x := by
    intro h
    rw [hgr' x] at h
    exact hgx (r.injective h)
  have hrx : r x = x := by
    rcases hSig (r x) hsupp with h | h | h
    · exact h
    · exfalso
      have h1 := a8_pow_apply_comm g r hgr x 1 (by rw [h, pow_one]) (Nat.card R)
      rw [a8_pow_card_mem R r hr, Perm.one_apply] at h1
      have h2 := a8_orbit_pow3 g hg3 x hgx (1 * Nat.card R) h1.symm
      exact hN3 (by simpa using h2)
    · exfalso
      have h1 := a8_pow_apply_comm g r hgr x 2 (by rw [h]) (Nat.card R)
      rw [a8_pow_card_mem R r hr, Perm.one_apply] at h1
      have h2 := a8_orbit_pow3 g hg3 x hgx (2 * Nat.card R) h1.symm
      exact hN3 ((Nat.Prime.dvd_mul Nat.prime_three).1 h2 |>.resolve_left (by norm_num))
  have hgx' : r (g x) = g x := by rw [← hgr' x, hrx]
  refine ⟨hrx, hgx', ?_⟩
  rw [pow_two, Perm.mul_apply, ← hgr' (g x), hgx']

theorem a8_three_set_card (g : Perm (Fin 8)) (x : Fin 8) (hgx : g x ≠ x)
    (hgg : g x ≠ (g ^ 2) x) (h2x : x ≠ (g ^ 2) x) :
    ({x, g x, (g ^ 2) x} : Finset (Fin 8)).card = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_pair hgg]
  simp [hgx.symm, h2x]

theorem a8_norm_fix (R : Subgroup (Perm (Fin 8))) (n : Perm (Fin 8))
    (hn : n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) (y : Fin 8)
    (h : ∀ r ∈ R, r y = y) : ∀ r ∈ R, r (n y) = n y := by
  intro r hr
  have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) r).1 hr
  simp only [inv_inv] at h'
  have h1 := h _ h'
  simp only [Perm.mul_apply] at h1
  have h2 := congrArg (⇑n) h1
  rwa [a8_app_inv] at h2

theorem a8_klein_fixT {a b c d : Fin 8} (R : Subgroup (Perm (Fin 8))) (t : Perm (Fin 8))
    (htR : t ∈ R) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hmem : ∀ y, t y = y ↔ (y = a ∨ y = b ∨ y = c ∨ y = d))
    (hfixt : ∀ r ∈ R, ∀ y, t y = y → r y = y) :
    (∀ w ∈ a8_kW a b c d, sign w = 1) ∧ IsPGroup 2 (a8_kW a b c d) ∧
      (∀ w ∈ a8_kW a b c d, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ a8_kW a b c d,
        n * w * n⁻¹ ∈ a8_kW a b c d) := by
  refine a8_kW_props R hab hac had hbc hbd hcd (fun r hr y hy => hfixt r hr y ((hmem y).2 hy)) ?_
  intro n hn y
  rw [← hmem, ← hmem]
  constructor
  · intro hy
    have := a8_norm_fix R n hn y (fun r hr => hfixt r hr y hy) t htR
    exact this
  · intro hy
    have h2 := a8_norm_fix R n⁻¹ (inv_mem hn) (n y) (fun r hr => hfixt r hr _ hy) t htR
    simpa only [a8_inv_app] using h2

theorem a8_caseA (g : Perm (Fin 8)) (hc : g.cycleType = {3}) (hg3 : g ^ 3 = 1)
    (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hRA : ∀ r ∈ R, sign r = 1) (hcomm : ∀ r ∈ R, g * r = r * g) :
    ∃ W : Subgroup (Perm (Fin 8)), (∀ w ∈ W, sign w = 1) ∧ IsPGroup 2 W ∧
      (∀ w ∈ W, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ W, n * w * n⁻¹ ∈ W) ∧
      ∃ w ∈ W, g * w ≠ w * g := by
  obtain ⟨x, hgx, hgg, h2x, hSig⟩ := a8_three_orbit g hc hg3
  obtain ⟨u, v, huv, hu, hv⟩ := a8_two_fixed g (by
    have := g.sum_cycleType; simp [hc] at this; omega)
  have hdiv4 := a8_three_card_dvd g hc R hR hRA hcomm u v huv hu hv
  have hN3 : ¬ 3 ∣ Nat.card R := fun h => by
    have := h.trans hdiv4; norm_num at this
  have hfix := a8_caseA_fix g hg3 x hgx hSig R hN3 hcomm
  obtain ⟨t, htR, ht1, ht2⟩ := a8_exists_invol R hR hne
  have hab := a8_comm_of_dvd_four R hR hne hdiv4
  set Sg : Finset (Fin 8) := {x, g x, (g ^ 2) x} with hSgdef
  have hSgc : Sg.card = 3 := a8_three_set_card g x hgx hgg h2x
  have htSg : ∀ y ∈ Sg, t y = y := by
    intro y hy
    simp only [hSgdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h <;> rw [h]
    · exact (hfix t htR).1
    · exact (hfix t htR).2.1
    · exact (hfix t htR).2.2
  have hsupp4 : t.support.card = 4 := by
    have hsign := a8_sign_involution t ht2
    rw [hRA t htR] at hsign
    have heven : Even (t.support.card / 2) :=
      (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
    have hsub : t.support ⊆ Finset.univ \ Sg := fun y hy => Finset.mem_sdiff.2
      ⟨Finset.mem_univ _, fun hyS => mem_support.1 hy (htSg y hyS)⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ_diff, Fintype.card_fin, hSgc] at hle
    have hpos : t.support.card ≠ 0 := by
      rw [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]; exact ht1
    obtain ⟨m, hm⟩ := two_dvd_card_support ht2
    obtain ⟨j, hj⟩ := heven
    omega
  set F : Finset (Fin 8) := Finset.univ.filter (fun y => t y = y) with hFdef
  have hFc : F.card = 4 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 8)))
      (fun y : Fin 8 => t y = y)
    rw [show (Finset.univ.filter fun y : Fin 8 => ¬ t y = y) = t.support from by
      ext y; simp [mem_support], hsupp4, Finset.card_univ, Fintype.card_fin] at h
    rw [hFdef]; omega
  have hSgF : Sg ⊆ F := fun y hy => by
    rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htSg y hy⟩
  have h1 : (F \ Sg).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSgF, hFc, hSgc]
  obtain ⟨p, hpset⟩ := Finset.card_eq_one.1 h1
  have hpF : p ∈ F \ Sg := by rw [hpset]; exact Finset.mem_singleton_self p
  have hpF' : t p = p := by
    have := (Finset.mem_sdiff.1 hpF).1
    rw [hFdef, Finset.mem_filter] at this; exact this.2
  have hpS : p ∉ Sg := (Finset.mem_sdiff.1 hpF).2
  have hfixed : ∀ y, t y = y → y = x ∨ y = g x ∨ y = (g ^ 2) x ∨ y = p := by
    intro y hy
    by_cases hyS : y ∈ Sg
    · simp only [hSgdef, Finset.mem_insert, Finset.mem_singleton] at hyS
      tauto
    · have hyF : y ∈ F \ Sg := Finset.mem_sdiff.2
        ⟨by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy⟩, hyS⟩
      rw [hpset, Finset.mem_singleton] at hyF
      exact Or.inr (Or.inr (Or.inr hyF))
  have hfixt : ∀ r ∈ R, ∀ y, t y = y → r y = y := by
    intro r hr y hy
    have htrp : ∀ z, t z = z → t (r z) = r z := fun z hz => by
      have := congrArg (fun π : Perm (Fin 8) => π z) (hab t htR r hr)
      simpa [Perm.mul_apply, hz] using this
    rcases hfixed y hy with h | h | h | h <;> rw [h]
    · exact (hfix r hr).1
    · exact (hfix r hr).2.1
    · exact (hfix r hr).2.2
    · rcases hfixed (r p) (htrp p hpF') with h' | h' | h' | h'
      · have : r (r p) = r p := by rw [h']; exact (hfix r hr).1
        exact r.injective this
      · have : r (r p) = r p := by rw [h']; exact (hfix r hr).2.1
        exact r.injective this
      · have : r (r p) = r p := by rw [h']; exact (hfix r hr).2.2
        exact r.injective this
      · exact h'
  have hmem : ∀ y, t y = y ↔ (y = x ∨ y = g x ∨ y = (g ^ 2) x ∨ y = p) := fun y =>
    ⟨hfixed y, fun h => by
      rcases h with h | h | h | h <;> rw [h]
      · exact (hfix t htR).1
      · exact (hfix t htR).2.1
      · exact (hfix t htR).2.2
      · exact hpF'⟩
  have hgx' : x ≠ g x := hgx.symm
  have hxp : x ≠ p := fun h => hpS (by rw [← h]; simp [hSgdef])
  have hgxp : g x ≠ p := fun h => hpS (by rw [← h]; simp [hSgdef])
  have hg2p : (g ^ 2) x ≠ p := fun h => hpS (by rw [← h]; simp [hSgdef])
  obtain ⟨hs, hp, hn, hnn'⟩ := a8_klein_fixT R t htR hgx' h2x hxp hgg hgxp hg2p hmem hfixt
  refine ⟨a8_kW x (g x) ((g ^ 2) x) p, hs, hp, hn, hnn', ?_⟩
  refine ⟨swap x (g x) * swap ((g ^ 2) x) p, subset_closure (by simp), fun h => ?_⟩
  have hw1 : (swap x (g x)) ((swap ((g ^ 2) x) p) x) = g x := by
    rw [swap_apply_of_ne_of_ne h2x hxp, swap_apply_left]
  have hw2 : (swap x (g x)) ((swap ((g ^ 2) x) p) (g x)) = x := by
    rw [swap_apply_of_ne_of_ne hgg hgxp, swap_apply_right]
  have e1 := congrArg (fun π : Perm (Fin 8) => π x) h
  simp only [Perm.mul_apply] at e1
  rw [hw1, hw2] at e1
  have h3 : (g ^ 2) x = x := by rw [pow_two, Perm.mul_apply, e1]
  exact h2x h3.symm

theorem a8_four_pts (F : Finset (Fin 8)) (h : F.card = 4) :
    ∃ a b c d : Fin 8, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ y, y ∈ F ↔ (y = a ∨ y = b ∨ y = c ∨ y = d) := by
  obtain ⟨a, ha⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
  have hc3 : (F.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, h]
  obtain ⟨b, c, d, hbc, hbd, hcd, hset⟩ := Finset.card_eq_three.1 hc3
  have hb : b ∈ F.erase a := by rw [hset]; simp
  have hc : c ∈ F.erase a := by rw [hset]; simp
  have hd : d ∈ F.erase a := by rw [hset]; simp
  have ha_ne : ∀ z ∈ F.erase a, z ≠ a := fun z hz => (Finset.mem_erase.1 hz).1
  refine ⟨a, b, c, d, Ne.symm (ha_ne b hb), Ne.symm (ha_ne c hc), Ne.symm (ha_ne d hd), hbc,
    hbd, hcd, fun y => ?_⟩
  constructor
  · intro hy
    by_cases hya : y = a
    · exact Or.inl hya
    · have : y ∈ F.erase a := Finset.mem_erase.2 ⟨hya, hy⟩
      rw [hset] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  · rintro (rfl | rfl | rfl | rfl)
    · exact ha
    · have := hb; exact (Finset.mem_erase.1 this).2
    · have := hc; exact (Finset.mem_erase.1 this).2
    · have := hd; exact (Finset.mem_erase.1 this).2

theorem a8_R_le_cent (g : Perm (Fin 8)) (R : Subgroup (Perm (Fin 8))) (hRA : ∀ r ∈ R, sign r = 1)
    (hcomm : ∀ r ∈ R, g * r = r * g) : R ≤ centralizer {g} ⊓ alternatingGroup (Fin 8) := by
  intro r hr
  refine Subgroup.mem_inf.2 ⟨?_, mem_alternatingGroup.2 (hRA r hr)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm r hr).symm

theorem a8_not_cent18 (g : Perm (Fin 8))
    (h18 : Nat.card ↥(centralizer {g} ⊓ alternatingGroup (Fin 8)) = 18)
    (W : Subgroup (Perm (Fin 8))) (hW : IsPGroup 2 W) (hWA : ∀ w ∈ W, sign w = 1)
    (x y z : Perm (Fin 8)) (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ∃ w ∈ W, g * w ≠ w * g := by
  by_contra hcon
  push_neg at hcon
  have hle : W ≤ centralizer {g} ⊓ alternatingGroup (Fin 8) := fun w hw => Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcon w hw).symm, mem_alternatingGroup.2 (hWA w hw)⟩
  have hd := Subgroup.card_dvd_of_le hle
  rw [h18] at hd
  exact absurd ((a8_card_four_dvd W hW x y z hx hy hz hxy hxz hyz).trans hd) (by norm_num)

theorem a8_card_two (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hdiv : Nat.card R ∣ 18) : Nat.card R = 2 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq R (by rw [hk]; rfl))
  have hk1 : k ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h4 : 2 ^ 2 ∣ Nat.card R := by rw [hk]; exact pow_dvd_pow 2 hcon
    exact absurd (h4.trans hdiv) (by norm_num)
  rw [hk, show k = 1 by omega]
  rfl

theorem a8_caseB (g : Perm (Fin 8)) (hc : g.cycleType = {3, 3})
    (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hRA : ∀ r ∈ R, sign r = 1) (hcomm : ∀ r ∈ R, g * r = r * g) :
    ∃ W : Subgroup (Perm (Fin 8)), (∀ w ∈ W, sign w = 1) ∧ IsPGroup 2 W ∧
      (∀ w ∈ W, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ W, n * w * n⁻¹ ∈ W) ∧
      ∃ w ∈ W, g * w ≠ w * g := by
  have hs6 : g.support.card = 6 := by
    have := g.sum_cycleType
    simp [hc] at this
    omega
  obtain ⟨u, v, huv, hu, hv⟩ := a8_two_fixed g (by omega)
  have h18 : Nat.card ↥(centralizer {g} ⊓ alternatingGroup (Fin 8)) = 18 := by
    have := a8_card_alt_inf _ _ (a8_swap_mem g u v hu hv) (sign_swap huv)
    rw [a8_cent33 g hc] at this
    omega
  have hdiv := Subgroup.card_dvd_of_le (a8_R_le_cent g R hRA hcomm)
  rw [h18] at hdiv
  have hcard2 := a8_card_two R hR hne hdiv
  obtain ⟨t, htR, ht1, ht2⟩ := a8_exists_invol R hR hne
  have hRt : ∀ r ∈ R, r = 1 ∨ r = t := by
    intro r hr
    by_cases h1 : r = 1
    · exact Or.inl h1
    · obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).1 hcard2
      exact Or.inr (congrArg Subtype.val ((huniq ⟨r, hr⟩ (fun h => h1 (congrArg Subtype.val h))).trans
        (huniq ⟨t, htR⟩ (fun h => ht1 (congrArg Subtype.val h))).symm))
  have hnt : ∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ y, n (t y) = t (n y) := by
    intro n hn y
    rcases hRt _ ((Subgroup.mem_normalizer_iff.1 hn t).1 htR) with h' | h'
    · exact absurd (by calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h']; group) ht1
    · have hcm : n * t = t * n := by
        calc n * t = (n * t * n⁻¹) * n := by group
          _ = t * n := by rw [h']
      simpa [Perm.mul_apply] using congrArg (fun π : Perm (Fin 8) => π y) hcm
  have hsupp : t.support.card = 4 ∨ t.support.card = 8 := by
    have hsign := a8_sign_involution t ht2
    rw [hRA t htR] at hsign
    have heven : Even (t.support.card / 2) :=
      (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
    have hpos : t.support.card ≠ 0 := by
      rw [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]
      exact ht1
    obtain ⟨m, hm⟩ := two_dvd_card_support ht2
    obtain ⟨j, hj⟩ := heven
    have hle : t.support.card ≤ 8 := by simpa using Finset.card_le_univ t.support
    omega
  rcases hsupp with h4 | h8
  ·
    have hFc : (Finset.univ.filter fun y : Fin 8 => t y = y).card = 4 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 8)))
        (fun y : Fin 8 => t y = y)
      rw [show (Finset.univ.filter fun y : Fin 8 => ¬ t y = y) = t.support from by
        ext y; simp [mem_support], h4, Finset.card_univ, Fintype.card_fin] at h
      omega
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hmem⟩ := a8_four_pts _ hFc
    have hmt : ∀ y, t y = y ↔ (y = a ∨ y = b ∨ y = c ∨ y = d) := fun y => by
      rw [← hmem y]; simp
    have hfixt : ∀ r ∈ R, ∀ y, t y = y → r y = y := by
      intro r hr y hy
      rcases hRt r hr with h | h
      · rw [h]; rfl
      · rw [h]; exact hy
    obtain ⟨hs, hp, hn, hnn⟩ := a8_klein_fixT R t htR hab hac had hbc hbd hcd hmt hfixt
    have hA : swap a b * swap c d ∈ a8_kW a b c d := subset_closure (by simp)
    have hB : swap a c * swap b d ∈ a8_kW a b c d := subset_closure (by simp)
    have ne1A : (1 : Perm (Fin 8)) ≠ swap a b * swap c d := fun h => by
      have := congrArg (fun π : Perm (Fin 8) => π a) h
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne, swap_apply_left, hab, hac, had] at this
    have ne1B : (1 : Perm (Fin 8)) ≠ swap a c * swap b d := fun h => by
      have := congrArg (fun π : Perm (Fin 8) => π a) h
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne, swap_apply_left, hab, hac, had] at this
    have neAB : swap a b * swap c d ≠ swap a c * swap b d := fun h => by
      have := congrArg (fun π : Perm (Fin 8) => π a) h
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne, swap_apply_left, hab, hac, had, hbc, hbd,
        hcd] at this
    exact ⟨a8_kW a b c d, hs, hp, hn, hnn,
      a8_not_cent18 g h18 _ hp hs 1 _ _ (one_mem _) hA hB ne1A ne1B neAB⟩
  ·
    have hfp : ∀ y, t y ≠ y := by
      intro y hy
      have hsub : t.support ⊆ Finset.univ.erase y := fun z hz => Finset.mem_erase.2
        ⟨fun h => (mem_support.1 hz) (h ▸ hy), Finset.mem_univ _⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, h8] at this
      omega
    obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := a8_pW_three t ht2 hfp
    refine ⟨a8_pW t, fun w hw => mem_alternatingGroup.1 (Subgroup.mem_inf.1 hw).2,
      a8_pW_isPGroup t ht2, fun w hw => a8_comm_normalizer R w (fun r hr => ?_),
      fun n hn w hw => a8_pW_normal t ht2 n (hnt n hn) w hw, ?_⟩
    · rcases hRt r hr with h | h
      · rw [h]; simp
      · rw [h]; exact a8_pW_commute t ht2 w hw
    · exact a8_not_cent18 g h18 _ (a8_pW_isPGroup t ht2) (fun w hw => mem_alternatingGroup.1 (Subgroup.mem_inf.1 hw).2)
        1 a b (one_mem _) ha hb (Ne.symm ha1) (Ne.symm hb1) hab

theorem a8_card_R_false (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (m : ℕ) (hm : Nat.card R ∣ m) (hcop : Nat.Coprime 2 m) : False := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hc : Nat.Coprime (Nat.card R) m := by rw [hk]; exact Nat.Coprime.pow_left k hcop
  exact hne (Subgroup.eq_bot_of_card_eq R (Nat.Coprime.eq_one_of_dvd hc hm))

theorem a8_core_prime (g : Perm (Fin 8)) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf g = p) (hp3 : p = 3 ∨ p = 5 ∨ p = 7) (R : Subgroup (Perm (Fin 8)))
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) (hRA : ∀ r ∈ R, sign r = 1)
    (hcomm : ∀ r ∈ R, g * r = r * g) :
    ∃ W : Subgroup (Perm (Fin 8)), (∀ w ∈ W, sign w = 1) ∧ IsPGroup 2 W ∧
      (∀ w ∈ W, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ W, n * w * n⁻¹ ∈ W) ∧
      ∃ w ∈ W, g * w ≠ w * g := by
  have hg3 : g ^ p = 1 := hord ▸ pow_orderOf_eq_one g
  obtain ⟨k, hk, hkp⟩ := CFSG.LocalAnalysis.GLTheoremA.cycleType_of_prime_order g hp hord
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h0 : g = 1 := Equiv.Perm.cycleType_eq_zero.1 (by rw [hk, Multiset.replicate_zero])
    rw [h0, orderOf_one] at hord
    exact hp.one_lt.ne hord
  rcases hp3 with rfl | rfl | rfl
  · rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · exact a8_caseA g (by rw [hk]; rfl) hg3 R hR hne hRA hcomm
    · exact a8_caseB g (by rw [hk]; rfl) R hR hne hRA hcomm
  · exfalso
    have hc : g.cycleType = {5} := by rw [hk, show k = 1 by omega]; rfl
    have hs5 : g.support.card = 5 := by
      have := sum_cycleType g
      rw [hc] at this
      simpa using this.symm
    obtain ⟨u, v, huv, hu, hv⟩ := a8_two_fixed g (by rw [hs5]; norm_num)
    have h1 := a8_card_alt_inf (centralizer {g}) (swap u v) (a8_swap_mem g u v hu hv)
      (sign_swap huv)
    rw [a8_cent5 g hc] at h1
    have h15 : Nat.card ↥(centralizer {g} ⊓ alternatingGroup (Fin 8)) = 15 := by omega
    have hd := Subgroup.card_dvd_of_le (a8_R_le_cent g R hRA hcomm)
    rw [h15] at hd
    exact a8_card_R_false R hR hne 15 hd (by decide)
  · exfalso
    have hc : g.cycleType = {7} := by rw [hk, show k = 1 by omega]; rfl
    have hd := Subgroup.card_dvd_of_le ((a8_R_le_cent g R hRA hcomm).trans inf_le_left)
    rw [a8_cent7 g hc] at hd
    exact a8_card_R_false R hR hne 7 hd (by decide)

theorem a8_prime_dvd (p : ℕ) (hp : p.Prime) (h : p ∣ 40320) (hodd : Odd p) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exfalso
        have h2' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        rw [h2'] at hodd
        exact absurd hodd (by decide)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1))

theorem a8_core (g : Perm (Fin 8)) (hodd : Odd (orderOf g)) (hg1 : g ≠ 1)
    (R : Subgroup (Perm (Fin 8))) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hRA : ∀ r ∈ R, sign r = 1) (hcomm : ∀ r ∈ R, g * r = r * g) :
    ∃ W : Subgroup (Perm (Fin 8)), (∀ w ∈ W, sign w = 1) ∧ IsPGroup 2 W ∧
      (∀ w ∈ W, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ W, n * w * n⁻¹ ∈ W) ∧
      ∃ w ∈ W, g * w ≠ w * g := by
  have hord1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  have hp : (orderOf g).minFac.Prime := Nat.minFac_prime hord1
  have hpd : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  have hpodd : Odd (orderOf g).minFac := Odd.of_dvd_nat hodd hpd
  have hg' : orderOf (g ^ (orderOf g / (orderOf g).minFac)) = (orderOf g).minFac :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd
  have hcard : Fintype.card (Perm (Fin 8)) = 40320 := by rw [Fintype.card_perm, Fintype.card_fin]; rfl
  have hp3 : (orderOf g).minFac = 3 ∨ (orderOf g).minFac = 5 ∨ (orderOf g).minFac = 7 :=
    a8_prime_dvd _ hp (by rw [← hcard, ← hg']; exact orderOf_dvd_card) hpodd
  have hcomm' : ∀ r ∈ R, g ^ (orderOf g / (orderOf g).minFac) * r = r * g ^ (orderOf g / (orderOf g).minFac) :=
    fun r hr => (Commute.pow_left (hcomm r hr : Commute g r) _).eq
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := a8_core_prime _ _ hp hpodd hg' hp3 R hR hne hRA hcomm'
  refine ⟨W, h1, h2, h3, h4, ?_⟩
  by_contra hall
  push_neg at hall
  obtain ⟨w, hw, hne'⟩ := h5
  exact hne' (Commute.pow_left (show Commute g w from hall w hw) _).eq

theorem a8_center_alt8_bot : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 8)))
    with h | h
  · exact h
  · exfalso
    have hm1 : (swap (0 : Fin 8) 1 * swap 1 2) ∈ alternatingGroup (Fin 8) := by
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
      norm_num
    have hm2 : (swap (0 : Fin 8) 1 * swap 1 3) ∈ alternatingGroup (Fin 8) := by
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
      norm_num
    have hnc : (swap (0 : Fin 8) 1 * swap 1 2) * (swap 0 1 * swap 1 3) ≠
        (swap (0 : Fin 8) 1 * swap 1 3) * (swap 0 1 * swap 1 2) := by decide
    have ha : (⟨_, hm1⟩ : alternatingGroup (Fin 8)) ∈ Subgroup.center (alternatingGroup (Fin 8)) :=
      h ▸ Subgroup.mem_top _
    have hc := (Subgroup.mem_center_iff.1 ha) ⟨_, hm2⟩
    have hc' : (swap (0 : Fin 8) 1 * swap 1 3) * (swap 0 1 * swap 1 2) =
        (swap (0 : Fin 8) 1 * swap 1 2) * (swap 0 1 * swap 1 3) := congrArg Subtype.val hc
    exact hnc hc'.symm

theorem a8_center_bot {H : Type} [Group H] [Finite H] (hperf : commutator H = ⊤)
    (e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 8))
    (hZcop : Nat.Coprime (Nat.card (Subgroup.center H)) 2) :
    Subgroup.center H = ⊥ := by
  set η : H →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηk : η.ker = Subgroup.center H := by
    ext h
    simp [hη, MonoidHom.mem_ker]
  haveI : Group.IsPerfect H := ⟨hperf⟩
  have hodd : Odd (Nat.card η.ker) := by
    rw [hηk]
    exact Nat.coprime_two_right.1 hZcop
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 6) (by norm_num) η hηs
    hηk.le hodd
  rw [hηk] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem a8_main {H : Type} [Group H] [Finite H] (Q : Subgroup H) (α : MulAut H) (m : ℕ)
    (hperf : commutator H = ⊤) (e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 8))
    (hZcop : Nat.Coprime (Nat.card (Subgroup.center H)) 2) (hQp : IsPGroup 2 Q)
    (hQne : ¬ Q ≤ Subgroup.center H) (hm : Nat.Coprime m 2) (hαm : α ^ m = 1)
    (hQfix : ∀ x ∈ Q, α x = x)
    (hcore : ∀ t ∈ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Q : Set H)), α t = t) : α = 1 := by
  have hZ := a8_center_bot hperf e hZcop
  let e2 : H ≃* alternatingGroup (Fin 8) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let ψ : H →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp e2.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact e2.injective (Subtype.ext hxy)
  have hψA : ∀ h : H, ψ h ∈ alternatingGroup (Fin 8) := fun h => (e2 h).2
  let R : Subgroup (Perm (Fin 8)) := Q.map ψ
  have hmemR : ∀ x : H, ψ x ∈ R ↔ x ∈ Q := fun x => by
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 hx
      rw [← hψinj hqx]; exact hq
    · intro hx; exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hRp : IsPGroup 2 R := hQp.map ψ
  have hQbot : Q ≠ ⊥ := fun h => hQne (by rw [h]; exact bot_le)
  have hRne : R ≠ ⊥ := by
    intro h
    apply hQbot
    apply Subgroup.eq_bot_of_card_eq
    have hc : Nat.card R = Nat.card Q := Subgroup.card_map_of_injective hψinj
    rw [h, Subgroup.card_bot] at hc
    exact hc.symm
  have hRA : ∀ r ∈ R, sign r = 1 := by
    intro r hr
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.1 hr
    exact mem_alternatingGroup.1 (hψA q)
  let β : MulAut (alternatingGroup (Fin 8)) := MulAut.congr e2 α
  have hβm : β ^ m = 1 := by rw [← map_pow, hαm, map_one]
  have hmodd : Odd m := Nat.coprime_two_right.1 hm
  have hβodd : Odd (orderOf β) := Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hβm)
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.oddInner_alt8 β hβodd
  have hβ : ∀ h : H, β (e2 h) = e2 (α h) := fun h => by
    simp [β, MulAut.congr_apply]
  have hgc : ∀ h : H, g * e2 h * g⁻¹ = e2 (α h) := fun h => by
    rw [← hβ h, hg, MulAut.conj_apply]
  have hgodd : Odd (orderOf (g : Perm (Fin 8))) := by
    have hgm : g ^ m = 1 := by
      have h1 : MulAut.conj (g ^ m) = 1 := by rw [map_pow, ← hg, hβm]
      have hcen : g ^ m ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
        rw [Subgroup.mem_center_iff]
        intro x
        have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 8)) => φ x) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        exact (mul_inv_eq_iff_eq_mul.1 h2).symm
      rw [a8_center_alt8_bot, Subgroup.mem_bot] at hcen
      exact hcen
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hgm)
  have hcommR : ∀ r ∈ R, (g : Perm (Fin 8)) * r = r * g := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hr
    have h := hgc q
    rw [hQfix q hq] at h
    exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 h)
  have hpsi_norm : ∀ k ∈ Subgroup.normalizer (Q : Set H),
      ψ k ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hr
      have h1 : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hk q).1 hq
      have e : ψ k * ψ q * (ψ k)⁻¹ = ψ (k * q * k⁻¹) := by simp [map_mul, map_inv]
      rw [e]
      exact (hmemR _).2 h1
    · intro hs
      obtain ⟨q', hq', hqs⟩ := Subgroup.mem_map.1 hs
      have hk' : k⁻¹ * q' * k⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (inv_mem hk) q').1 hq'
      refine Subgroup.mem_map.2 ⟨k⁻¹ * q' * k⁻¹⁻¹, hk', ?_⟩
      rw [inv_inv, map_mul, map_mul, map_inv, hqs]
      group
  have hg1 : g = 1 := by
    by_contra hg1
    have hgP : (g : Perm (Fin 8)) ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨W, hWsign, hWp, hWn, hWnorm, w0, hw0, hne0⟩ :=
      a8_core (g : Perm (Fin 8)) hgodd hgP R hRp hRne hRA hcommR
    let WH : Subgroup H := W.comap ψ
    have hWH_mem : ∀ x : H, x ∈ WH ↔ ψ x ∈ W := fun x => Iff.rfl
    have hWH_p : IsPGroup 2 WH := by
      intro x
      obtain ⟨k, hk⟩ := hWp ⟨ψ x.1, (hWH_mem x.1).1 x.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      apply hψinj
      show ψ (x.1 ^ 2 ^ k) = ψ 1
      rw [map_pow, map_one]
      have := congrArg Subtype.val hk
      simpa using this
    have hWH_sub : WH ≤ Subgroup.normalizer (Q : Set H) := by
      intro h hh
      have hW := (Subgroup.mem_normalizer_iff.1 (hWn (ψ h) ((hWH_mem h).1 hh)))
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have := hW (ψ q)
      rw [hmemR q, show ψ h * ψ q * (ψ h)⁻¹ = ψ (h * q * h⁻¹) by simp [map_mul, map_inv],
        hmemR] at this
      exact this
    have hWH_norm : ∀ k ∈ Subgroup.normalizer (Q : Set H), ∀ x ∈ WH, k * x * k⁻¹ ∈ WH := by
      intro k hk x hx
      have hW := hWnorm (ψ k) (hpsi_norm k hk) (ψ x) ((hWH_mem x).1 hx)
      rw [hWH_mem, show ψ (k * x * k⁻¹) = ψ k * ψ x * (ψ k)⁻¹ by simp [map_mul, map_inv]]
      exact hW
    have hWH_core := CFSG.LocalAnalysis.GLTheoremA.i1312_le_pCoreOf
      (Subgroup.normalizer (Q : Set H)) WH hWH_sub hWH_norm hWH_p
    have hWH_fix : ∀ x ∈ WH, α x = x := fun x hx => hcore x (hWH_core hx)
    have hall : ∀ w ∈ W, (g : Perm (Fin 8)) * w = w * g := by
      intro w hw
      have hA : w ∈ alternatingGroup (Fin 8) := mem_alternatingGroup.2 (hWsign w hw)
      obtain ⟨h, hh⟩ : ∃ h : H, ψ h = w := ⟨e2.symm ⟨w, hA⟩, by simp [ψ]⟩
      have hhW : h ∈ WH := (hWH_mem h).2 (by rw [hh]; exact hw)
      have h1 := hgc h
      rw [hWH_fix h hhW] at h1
      have h2 : (g : Perm (Fin 8)) * ψ h = ψ h * g := congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 h1)
      rw [hh] at h2
      exact h2
    exact hne0 (hall w0 hw0)
  refine MulEquiv.ext fun h => ?_
  have h1 := hgc h
  rw [hg1] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  rw [MulAut.one_apply]
  exact (e2.injective h1).symm

theorem i1312Alt8Constrained_holds : I1312Alt8Constrained := by
  intro H _ _ Q α m hperf _ _ ⟨e⟩ hZcop hQp hQne hm hαm hQfix hcore
  exact a8_main Q α m hperf e hZcop hQp hQne hm hαm hQfix hcore

end CFSG.LocalAnalysis.GLTheoremA
