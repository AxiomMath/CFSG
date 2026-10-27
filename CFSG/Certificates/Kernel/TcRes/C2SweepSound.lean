module

public import CFSG.Certificates.Kernel.TcRes.TransSound
public import CFSG.Certificates.Kernel.TcRes.PlaneSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK Matrix

theorem fact_prime_five_tcres : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] fact_prime_five_tcres

@[expose] noncomputable def v5 (c : ℕ) : Fin 4 → ZMod 5 := fun i => (dg5 c i : ZMod 5)

@[expose] noncomputable def lam (B : ℕ) (c : Fin 4 → ZMod 5) : Fin 8 → ZMod 5 :=
  ∑ i, c i • bvec B i

structure Sweep5Raw (a e : ℕ) (pr : ℕ → (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5)) : Prop where
  mem : ∀ p, a ≤ p → p < e → IsReduced (pr p).1 (pr p).2
  inj : ∀ p, a ≤ p → p < e → ∀ p', a ≤ p' → p' < e → pr p = pr p' → p = p'
  card : Nat.card {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) // IsReduced x.1 x.2} = e - a

section Sweep5Decode

theorem tab5_lanes {U L M : ℕ → ℕ} (htab : ∀ i < 5, tabs5OK U L M i = true) {c : ℕ}
    (hc : c < 625) {m : ℕ} (hm : m < 4) :
    fld (U m) 12 c = dg5 c m ∧ fld (L m) 12 c = b2n (ld5OK c m) ∧
      fld (M m) 12 c = b2n (m5Pred c m) := by
  have h := htab (c / 125) (by omega)
  simp only [tabs5OK, Lane.allLt_iff, Lane.nadd, Lane.nmul] at h
  have h2 := h (c % 125) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at h2
  simp only [tab5OK, Lane.allLt_iff, Lane.andB_eq_true, Lane.beq_eq_true] at h2
  exact h2 m hm

theorem dg5_lt (c m : ℕ) : dg5 c m < 5 := Nat.mod_lt _ (by norm_num)

theorem dg5_digits : ∀ c < 625, c = ∑ m ∈ Finset.range 4, dg5 c m * 5 ^ m := by
  decide +kernel

theorem ld5OK_iff_dg : ∀ c < 625, ∀ j < 4, ld5OK c j = true ↔
    (dg5 c j = 1 ∧ ∀ i < 4, j < i → dg5 c i = 0) := by
  decide +kernel

theorem v5_eq_iff {c c' : ℕ} {m : Fin 4} : v5 c m = v5 c' m ↔ dg5 c m = dg5 c' m := by
  simp only [v5]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dg5_lt c m), Nat.mod_eq_of_lt (dg5_lt c' m)]

theorem v5_eq_nat {c a : ℕ} {m : Fin 4} (ha : a < 5) : v5 c m = (a : ZMod 5) ↔ dg5 c m = a := by
  simp only [v5]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dg5_lt c m), Nat.mod_eq_of_lt ha]

theorem v5_inj {c c' : ℕ} (hc : c < 625) (hc' : c' < 625) (h : v5 c = v5 c') : c = c' := by
  rw [dg5_digits c hc, dg5_digits c' hc']
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have := (v5_eq_iff (m := ⟨m, hm⟩)).1 (congrFun h _)
  exact congrArg (· * 5 ^ m) this

theorem v5_surj (x : Fin 4 → ZMod 5) : ∃ c < 625, v5 c = x := by
  have hN : Nat.card (Fin 4 → ZMod 5) = 625 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hinj : Function.Injective (fun c : Fin 625 => v5 c) := fun c c' h =>
    Fin.ext (v5_inj c.2 c'.2 h)
  obtain ⟨c, hc⟩ := surjective_of_injective_card hN _ hinj x
  exact ⟨c, c.2, hc⟩

theorem isLead5_iff {c : ℕ} (hc : c < 625) (j : Fin 4) : ld5OK c j = true ↔ IsLead (v5 c) j := by
  rw [ld5OK_iff_dg c hc j j.2, IsLead]
  have e1 : v5 c j = 1 ↔ dg5 c j = 1 := by
    have := v5_eq_nat (c := c) (m := j) (a := 1) (by norm_num)
    rwa [Nat.cast_one] at this
  have e0 : ∀ i : Fin 4, v5 c i = 0 ↔ dg5 c i = 0 := fun i => by
    have := v5_eq_nat (c := c) (m := i) (a := 0) (by norm_num)
    rwa [Nat.cast_zero] at this
  rw [e1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => (e0 i).2 (h2 i.1 i.2 hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi hji => (e0 ⟨i, hi⟩).1 (h2 ⟨i, hi⟩ hji)⟩

theorem m5Pred_iff {c : ℕ} (hc : c < 625) (j : Fin 4) : m5Pred c j = true ↔
    (∃ i : Fin 4, j < i ∧ IsLead (v5 c) i) ∧ v5 c j = 0 := by
  have e0 : v5 c j = 0 ↔ dg5 c j = 0 := by
    have := v5_eq_nat (c := c) (m := j) (a := 0) (by norm_num)
    rwa [Nat.cast_zero] at this
  simp only [m5Pred, Lane.andB_eq_true, Lane.anyLt_iff, Lane.blt_eq_true, Lane.beq_eq_true, e0]
  constructor
  · rintro ⟨⟨i, hi, hji, hl⟩, h0⟩
    exact ⟨⟨⟨i, hi⟩, hji, (isLead5_iff hc ⟨i, hi⟩).1 hl⟩, h0⟩
  · rintro ⟨⟨i, hji, hl⟩, h0⟩
    exact ⟨⟨i, i.2, hji, (isLead5_iff hc i).2 hl⟩, h0⟩

theorem isLead5_unique {v : Fin 4 → ZMod 5} {i j : Fin 4} (hi : IsLead v i) (hj : IsLead v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hi.2 j h
    rw [hj.1] at this
    exact absurd this one_ne_zero
  · exact h
  · have := hj.2 i h
    rw [hi.1] at this
    exact absurd this one_ne_zero

open Classical in
theorem card_red5 : Nat.card {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) // IsReduced x.1 x.2} =
    ∑ j ∈ Finset.range 4, ((Finset.range 625).filter (fun c => m5Pred c j = true)).card *
      ((Finset.range 625).filter (fun c => ld5OK c j = true)).card := by
  let S : Finset (ℕ × ℕ) := ((Finset.range 625) ×ˢ (Finset.range 625)).filter
    (fun p => IsReduced (v5 p.1) (v5 p.2))
  let f : ℕ × ℕ → (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) := fun p => (v5 p.1, v5 p.2)
  have himg : {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) | IsReduced x.1 x.2} = f '' ↑S := by
    ext ⟨x1, x2⟩
    constructor
    · intro h
      obtain ⟨a, ha, rfl⟩ := v5_surj x1
      obtain ⟨b, hb, rfl⟩ := v5_surj x2
      refine ⟨(a, b), ?_, rfl⟩
      simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨⟨ha, hb⟩, h⟩
    · rintro ⟨⟨a, b⟩, hab, he⟩
      simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq] at hab
      simp only [f, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hab.2
  have hinj : Set.InjOn f ↑S := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
    simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_setOf_eq] at hab hab'
    simp only [f, Prod.mk.injEq] at he
    rw [v5_inj hab.1.1 hab'.1.1 he.1, v5_inj hab.1.2 hab'.1.2 he.2]
  have hS : S = (Finset.range 4).biUnion (fun j =>
      ((Finset.range 625).filter (fun c => m5Pred c j = true)) ×ˢ
      ((Finset.range 625).filter (fun c => ld5OK c j = true))) := by
    ext ⟨a, b⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨ha, hb⟩, ⟨i, j, hji, hi, hj, h0⟩⟩
      exact ⟨j, j.2, ⟨ha, (m5Pred_iff ha j).2 ⟨⟨i, hji, hi⟩, h0⟩⟩, ⟨hb, (isLead5_iff hb j).2 hj⟩⟩
    · rintro ⟨j, hj, ⟨ha, hm⟩, ⟨hb, hl⟩⟩
      obtain ⟨⟨i, hji, hi⟩, h0⟩ := (m5Pred_iff ha ⟨j, hj⟩).1 hm
      exact ⟨⟨ha, hb⟩, ⟨i, ⟨j, hj⟩, hji, hi, (isLead5_iff hb ⟨j, hj⟩).1 hl, h0⟩⟩
  have e0 : Nat.card {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) // IsReduced x.1 x.2} =
      Nat.card ↥{x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) | IsReduced x.1 x.2} := rfl
  rw [e0, himg, Nat.card_image_of_injOn hinj]
  have hc : Nat.card (↑(↑S : Set (ℕ × ℕ))) = S.card := by
    rw [Nat.card_eq_card_toFinset, Finset.toFinset_coe]
  rw [hc, hS, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun j _ => Finset.card_product _ _
  · intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at h1 h2
    rw [Finset.mem_coe, Finset.mem_range] at hj hj'
    have := isLead5_unique ((isLead5_iff h1.2.1 ⟨j, hj⟩).1 h1.2.2)
      ((isLead5_iff h2.2.1 ⟨j', hj'⟩).1 h2.2.2)
    exact hne (congrArg Fin.val this)

theorem LOW625_lt : LOW625 < 2 ^ (12 * 625) := Lane.low_lt (w := 12) (by decide) 625

theorem fld_LOW625 {i : ℕ} (hi : i < 625) : fld LOW625 12 i = 1 := by
  have := Lane.fld_mul_low (w := 12) (K := 625) (c := 1) (by norm_num) (by norm_num) hi
  rwa [one_mul] at this

theorem pop625_eq {x : ℕ} (hx : x < 2 ^ (12 * 625)) (hxl : ∀ i, fld x 12 i ≤ 1) :
    pop625 x = ∑ c ∈ Finset.range 625, fld x 12 c := by
  have hLl : ∀ i, fld LOW625 12 i ≤ 1 := fun i => by
    rcases lt_or_ge i 625 with h | h
    · rw [fld_LOW625 h]
    · rw [Lane.fld_eq_zero_of_lt 12 625 _ LOW625_lt h]
      omega
  have hb := Lane.conv_le 12 625 x LOW625 1 1 hx hxl hLl
  change fld (x * LOW625) 12 624 = _
  rw [Lane.fld_mul 12 625 625 x LOW625 hx LOW625_lt
    (fun k => lt_of_le_of_lt (hb k) (by norm_num)) 624]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [fld_LOW625 (by omega), mul_one]

open Classical in
theorem pop625_tab {X : ℕ} {B : ℕ → Bool} (hX : X < 2 ^ (12 * 625))
    (hl : ∀ c < 625, fld X 12 c = b2n (B c)) :
    pop625 X = ((Finset.range 625).filter (fun c => B c = true)).card := by
  have hl1 : ∀ i, fld X 12 i ≤ 1 := fun i => by
    rcases lt_or_ge i 625 with h | h
    · rw [hl i h, Lane.b2n_eq]
      split_ifs <;> norm_num
    · rw [Lane.fld_eq_zero_of_lt 12 625 _ hX h]
      omega
  rw [pop625_eq hX hl1, Finset.card_filter]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [hl c (Finset.mem_range.1 hc), Lane.b2n_eq]

@[expose] noncomputable def rc1 (LF : ℕ → ℕ) (p : ℕ) : ℕ := Nat.land (prec5 LF p) 1023

@[expose] noncomputable def rc2 (LF : ℕ → ℕ) (p : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (prec5 LF p) 10) 1023

theorem sw5Walk_spec (L M LF : ℕ → ℕ) (s : ℕ) : ∀ c p prev,
    sw5Walk L M LF s c p prev = true →
    (∀ t < c, ∃ j < 4, lane1 (L j) (rc2 LF (p + t)) = true ∧ lane1 (M j) (rc1 LF (p + t)) = true) ∧
    ∀ t t', t < t' → t' < c →
      625 * rc1 LF (p + t) + rc2 LF (p + t) < 625 * rc1 LF (p + t') + rc2 LF (p + t') := by
  have hstep : ∀ c p prev, sw5Walk L M LF s (c + 1) p prev = true →
      (∃ j < 4, lane1 (L j) (rc2 LF p) = true ∧ lane1 (M j) (rc1 LF p) = true) ∧
      prev < 625 * rc1 LF p + rc2 LF p ∧ sw5Walk L M LF s c (p + 1) (625 * rc1 LF p + rc2 LF p) =
        true := by
    intro c p prev h
    change strictB (prec5 LF p) (fun e =>
      strictB (Nat.land e 1023) fun c1 =>
      strictB (Nat.land (Nat.shiftRight e 10) 1023) fun c2 =>
      strictB (Nat.add (Nat.mul 625 c1) c2) fun key =>
        CFSG.TcRes.TK.andB (Nat.beq (Nat.land (Nat.shiftRight e 20) 1) s)
          (CFSG.TcRes.TK.andB (anyLt 4 fun j => CFSG.TcRes.TK.andB (lane1 (L j) c2) (lane1 (M j) c1))
            (CFSG.TcRes.TK.andB (Nat.blt prev key) (sw5Walk L M LF s c (Nat.succ p) key)))) = true at h
    simp only [Lane.strictB_eq, Lane.andB_eq_true, Lane.anyLt_iff, Lane.blt_eq_true] at h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  intro c
  induction c with
  | zero => intro p prev _; exact ⟨fun t h => absurd h (Nat.not_lt_zero _),
      fun t t' _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ c ih =>
    intro p prev h
    obtain ⟨hr, -, hw⟩ := hstep c p prev h
    obtain ⟨i1, i2⟩ := ih _ _ hw
    have hs : ∀ t, p + 1 + t = p + (t + 1) := fun t => by omega
    refine ⟨fun t ht => ?_, fun t t' htt ht' => ?_⟩
    · rcases t with _ | t
      · exact hr
      · rw [← hs]
        exact i1 t (by omega)
    · obtain ⟨t', rfl⟩ : ∃ u, t' = u + 1 := ⟨t' - 1, by omega⟩
      rw [← hs]
      rcases t with _ | t
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have a1 := (hstep c' (p + 1) _ hw).2.1
        rcases t' with _ | t'
        · simpa using a1
        · have a2 := i2 0 (t' + 1) (by omega) (by omega)
          simp only [add_zero] at a1 a2 ⊢
          exact a1.trans a2
      · rw [← hs]
        exact i2 t t' (by omega) (by omega)

end Sweep5Decode

theorem sweep5Raw_of_checks {U L M LF : ℕ → ℕ} (htab : ∀ i < 5, tabs5OK U L M i = true)
    (hLM : ∀ j < 4, L j < 2 ^ (12 * 625) ∧ M j < 2 ^ (12 * 625))
    {s : ℕ} (hsw : sw5OK L M LF s = true) :
    Sweep5Raw (806 * s) (806 * s + 806) (fun p =>
      (v5 (Nat.land (prec5 LF p) 1023), v5 (Nat.land (Nat.shiftRight (prec5 LF p) 10) 1023))) := by
  classical
  simp only [sw5OK, Lane.andB_eq_true, Lane.beq_eq_true] at hsw
  obtain ⟨hnp, hwalk⟩ := hsw
  obtain ⟨hr, hmono⟩ := sw5Walk_spec L M LF s _ _ _ hwalk
  have hlt : ∀ {X c : ℕ}, X < 2 ^ (12 * 625) → lane1 X c = true → c < 625 := by
    intro X c hX h
    by_contra hc
    have := Lane.fld_eq_zero_of_lt 12 625 X hX (by omega : 625 ≤ c)
    simp only [lane1, Lane.beq_eq_true, this] at h
    exact absurd h (by norm_num)
  have hred : ∀ t < 806, rc1 LF (806 * s + t) < 625 ∧ rc2 LF (806 * s + t) < 625 ∧
      IsReduced (v5 (rc1 LF (806 * s + t))) (v5 (rc2 LF (806 * s + t))) := by
    intro t ht
    obtain ⟨j, hj, hL, hM⟩ := hr t ht
    have h2 := hlt (hLM j hj).1 hL
    have h1 := hlt (hLM j hj).2 hM
    refine ⟨h1, h2, ?_⟩
    simp only [lane1, Lane.beq_eq_true] at hL hM
    rw [(tab5_lanes htab h2 hj).2.1, b2n_eq_one] at hL
    rw [(tab5_lanes htab h1 hj).2.2, b2n_eq_one] at hM
    obtain ⟨⟨i, hji, hli⟩, h0⟩ := (m5Pred_iff h1 ⟨j, hj⟩).1 hM
    exact ⟨i, ⟨j, hj⟩, hji, hli, (isLead5_iff h2 ⟨j, hj⟩).1 hL, h0⟩
  refine ⟨fun p hap hpe => ?_, fun p hap hpe p' hap' hpe' hpp => ?_, ?_⟩
  · have := (hred (p - 806 * s) (by omega)).2.2
    rwa [show 806 * s + (p - 806 * s) = p by omega] at this
  · obtain ⟨a1, a2, -⟩ := hred (p - 806 * s) (by omega)
    obtain ⟨b1, b2, -⟩ := hred (p' - 806 * s) (by omega)
    rw [show 806 * s + (p - 806 * s) = p by omega] at a1 a2
    rw [show 806 * s + (p' - 806 * s) = p' by omega] at b1 b2
    simp only [Prod.mk.injEq] at hpp
    have e1 := v5_inj a1 b1 hpp.1
    have e2 := v5_inj a2 b2 hpp.2
    have hk : 625 * rc1 LF (806 * s + (p - 806 * s)) + rc2 LF (806 * s + (p - 806 * s)) =
        625 * rc1 LF (806 * s + (p' - 806 * s)) + rc2 LF (806 * s + (p' - 806 * s)) := by
      rw [show 806 * s + (p - 806 * s) = p by omega,
        show 806 * s + (p' - 806 * s) = p' by omega]
      exact congrArg₂ (fun a b => 625 * a + b) e1 e2
    rcases lt_trichotomy (p - 806 * s) (p' - 806 * s) with h | h | h
    · exact absurd hk (ne_of_lt (hmono _ _ h (by omega)))
    · omega
    · exact absurd hk (ne_of_gt (hmono _ _ h (by omega)))
  · rw [card_red5, show 806 * s + 806 - 806 * s = 806 by omega, ← hnp, Lane.sumLt_eq]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [pop625_tab (B := fun c => ld5OK c j) (hLM j hj).1 (fun c hc => (tab5_lanes htab hc hj).2.1),
      pop625_tab (B := fun c => m5Pred c j) (hLM j hj).2 (fun c hc => (tab5_lanes htab hc hj).2.2)]
    exact Nat.mul_comm _ _

theorem Sweep5Raw.surj {a e : ℕ} {pr : ℕ → (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5)}
    (h : Sweep5Raw a e pr) {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5)} (hx : IsReduced x.1 x.2) :
    ∃ p, a ≤ p ∧ p < e ∧ pr p = x := by
  classical
  let f : Fin (e - a) → {x : (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5) // IsReduced x.1 x.2} :=
    fun i => ⟨pr (a + i), h.mem _ (by omega) (by omega)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have := h.inj _ (by omega) (by omega) _ (by omega) (by omega) (congrArg Subtype.val hij)
    exact Fin.ext (by omega)
  obtain ⟨i, hi⟩ := surjective_of_injective_card h.card f hinj ⟨x, hx⟩
  exact ⟨a + i, by omega, by omega, congrArg Subtype.val hi⟩

theorem lam_add (B : ℕ) (c d : Fin 4 → ZMod 5) : lam B (c + d) = lam B c + lam B d := by
  simp only [lam, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem lam_smul (B : ℕ) (t : ZMod 5) (c : Fin 4 → ZMod 5) : lam B (t • c) = t • lam B c := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[expose] noncomputable def lamL (B : ℕ) : (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 8 → ZMod 5) where
  toFun := lam B
  map_add' := lam_add B
  map_smul' := lam_smul B

theorem exists_c2_record {vec : ℕ → Fin Tag.E8.rank → ℤ} {T0 B PV MW r a e : ℕ}
    {pr : ℕ → (Fin 4 → ZMod 5) × (Fin 4 → ZMod 5)} (hK : KerRaw vec T0 B PV MW r)
    (hsw : Sweep5Raw a e pr) {P : Submodule (ZMod 5) (Fin 8 → ZMod 5)}
    (hP : Module.finrank (ZMod 5) P = 2) (hPK : ∀ v ∈ P, v ᵥ* amat vec T0 r = 0) :
    ∃ p, a ≤ p ∧ p < e ∧ IsReduced (pr p).1 (pr p).2 ∧
      ∀ v, v ∈ P ↔ ∃ s t : ZMod 5, v = s • lam B (pr p).1 + t • lam B (pr p).2 := by
  have hpiv : ∀ (c : Fin 4 → ZMod 5) (k : Fin 4),
      lam B c (⟨fld PV 3 k % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = c k := by
    intro c k
    simp only [lam, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hK.piv, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinj : Function.Injective (lamL B) := by
    intro c d hcd
    funext k
    rw [← hpiv c k, ← hpiv d k]
    exact congrFun hcd _
  have hrange : P ≤ LinearMap.range (lamL B) := by
    intro v hv
    obtain ⟨c, hc⟩ := hK.mem_span (hPK v hv)
    exact ⟨c, hc.symm⟩
  let Q := P.comap (lamL B)
  have hQ : Q.map (lamL B) = P := Submodule.map_comap_eq_of_le hrange
  have hQ2 : Module.finrank (ZMod 5) Q = 2 := by
    rw [← hP, ← hQ]
    exact (Submodule.equivMapOfInjective (lamL B) hinj Q).finrank_eq
  obtain ⟨u1, hu1, u2, hu2, hu⟩ := exists_reduced hQ2
  obtain ⟨p, hap, hpe, hp⟩ := hsw.surj (x := (u1, u2)) hu
  refine ⟨p, hap, hpe, by rw [hp]; exact hu, fun v => ?_⟩
  rw [hp]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := hrange hv
    have hcQ : c ∈ Q := by
      change lamL B c ∈ P
      rw [hc]
      exact hv
    obtain ⟨s, t, hst⟩ := (hu.mem_iff hQ2 hu1 hu2 c).1 hcQ
    refine ⟨s, t, ?_⟩
    rw [← hc, hst]
    change lam B (s • u1 + t • u2) = _
    rw [lam_add, lam_smul, lam_smul]
  · rintro ⟨s, t, rfl⟩
    exact P.add_mem (P.smul_mem _ hu1) (P.smul_mem _ hu2)

@[expose] def PhiP5 (vec : ℕ → Fin Tag.E8.rank → ℤ) (u1 u2 : Fin 8 → ZMod 5) : Set ℕ :=
  {g | g < 240 ∧ ∑ m : Fin 8, u1 m * ((vec g m : ℤ) : ZMod 5) = 0 ∧
    ∑ m : Fin 8, u2 m * ((vec g m : ℤ) : ZMod 5) = 0}

end CFSG.KC.TcRes

end
