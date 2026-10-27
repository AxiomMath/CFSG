module

public import Certificates.Data.Kernel.RouteP.Mono
public import CFSG.Certificates.Kernel.Spor.Fi24NetSound

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def fibF (NW : Nat → Nat → Nat) : Int → Nat → Nat
  | Int.ofNat m => if m = 0 then fun q => q else pF (NW (m - 1))
  | Int.negSucc n => pR (NW n)

@[expose] def WNV (NW : Nat → Nat → Nat) (w : List Int) : Prop := ∀ z ∈ w, NV (NW (z.natAbs - 1))

theorem WNV.tail {NW : Nat → Nat → Nat} {z : Int} {w : List Int} (h : WNV NW (z :: w)) : WNV NW w :=
  fun z' hz' => h z' (List.mem_cons_of_mem z hz')

theorem testBit_appP {NW : Nat → Nat → Nat} (z : Int) (hz : NV (NW (z.natAbs - 1))) (v q : Nat) :
    (appP NW z v).testBit q = v.testBit (fibF NW z q) := by
  cases z with
  | ofNat m =>
    have e : appP NW (Int.ofNat m) v =
        Bool.rec (motive := fun _ => Nat) (netF (NW (Nat.sub m 1)) v) v (Nat.beq m 0) := rfl
    rw [e]
    by_cases hm : m = 0
    · subst hm
      rfl
    · rw [beq_false hm]
      have e2 : fibF NW (Int.ofNat m) = pF (NW (m - 1)) := if_neg hm
      rw [e2]
      exact testBit_netF hz v q
  | negSucc n => exact testBit_netR hz v q

theorem testBit_walkP {NW : Nat → Nat → Nat} : ∀ (w : List Int), WNV NW w →
    ∀ v q, (walkP NW w v).testBit q = v.testBit (w.foldr (fibF NW) q)
  | [], _, _, _ => rfl
  | z :: w, h, v, q => by
    have e : walkP NW (z :: w) v = walkP NW w (appP NW z v) := strictN_eq' _ _
    rw [e, testBit_walkP w h.tail (appP NW z v) q, testBit_appP z (h z List.mem_cons_self) v]
    rfl

theorem fibF_lt {NW : Nat → Nat → Nat} (z : Int) (hz : NV (NW (z.natAbs - 1))) {q : Nat}
    (hq : q < 524288) : fibF NW z q < 524288 := by
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      exact hq
    · have e2 : fibF NW (Int.ofNat m) = pF (NW (m - 1)) := if_neg hm
      rw [e2]
      exact pF_lt hz hq
  | negSucc n => exact pR_lt hz hq

theorem foldrF_lt {NW : Nat → Nat → Nat} : ∀ (w : List Int), WNV NW w →
    ∀ q < 524288, w.foldr (fibF NW) q < 524288
  | [], _, _, hq => hq
  | z :: w, h, q, hq => fibF_lt z (h z List.mem_cons_self) (foldrF_lt w h.tail q hq)

theorem wordP_spec {NW : Nat → Nat → Nat} {w : List Int} {j : Nat} (hj : NV (NW j))
    (hw : WNV NW w) (h : ∀ k < 19, CFSG.KC.RouteP.wordOK NW w j k = true) :
    ∀ q < 524288, pF (NW j) q = w.foldr (fibF NW) q := by
  refine perm_of_tpl (fun q hq => pF_lt hj hq) (fun q hq => foldrF_lt w hw q hq) ?_
  intro k hk q _
  have e := h k hk
  unfold CFSG.KC.RouteP.wordOK at e
  rw [letB_eq'] at e
  have e2 : (walkP NW w (tpl k)).testBit q = (netF (NW j) (tpl k)).testBit q := by
    rw [Nat.eq_of_beq_eq_true e]
  rw [testBit_walkP w hw, testBit_netF hj] at e2
  exact e2.symm

theorem idP_spec {NW : Nat → Nat → Nat} {w : List Int} (hw : WNV NW w)
    (h : ∀ k < 19, idOK NW w k = true) : ∀ q < 524288, w.foldr (fibF NW) q = q := by
  refine perm_of_tpl (fun q hq => foldrF_lt w hw q hq) (fun q hq => hq) ?_
  intro k hk q _
  have e := h k hk
  unfold idOK at e
  rw [letB_eq'] at e
  have e2 : (walkP NW w (tpl k)).testBit q = (tpl k).testBit q := by
    rw [Nat.eq_of_beq_eq_true e]
  rwa [testBit_walkP w hw] at e2

theorem swp_ge {S d m : Nat} (h : ValidIn S d m) {q : Nat} (hq : S ≤ q) : swp d m q = q := by
  unfold swp
  have h1 : m.testBit q = false := by
    cases e : m.testBit q
    · rfl
    · exact absurd (h q e).1 (by omega)
  rw [if_neg (by rw [h1]; decide)]
  rw [if_neg]
  rintro ⟨hdq, e⟩
  have := (h (q - d) e).1
  omega

theorem pF_ge {M : Nat → Nat} (h : NV M) {q : Nat} (hq : 524288 ≤ q) : pF M q = q :=
  compF_fix (τ := fun l => swp (ldist l) (M l)) (c := 37) (fun i hi => swp_ge (h i hi) hq) 0 37
    (Nat.le_refl _)

theorem pR_ge {M : Nat → Nat} (h : NV M) {q : Nat} (hq : 524288 ≤ q) : pR M q = q :=
  compF_fix (τ := fun l => swp (ldist (36 - l)) (M (36 - l))) (c := 37)
    (fun i hi => swp_ge (h (36 - i) (by omega)) hq) 0 37 (Nat.le_refl _)

theorem lt_of_testBit {x n : Nat} (h : ∀ q, n ≤ q → x.testBit q = false) : x < 2 ^ n :=
  Nat.lt_pow_two_of_testBit x h

theorem netR_small {M : Nat → Nat} (h : NV M) {v : Nat} (hv : ∀ q, 524288 ≤ q → v.testBit q = false) :
    ∀ q, 524288 ≤ q → (netR M v).testBit q = false := by
  intro q hq
  rw [testBit_netR h, pR_ge h hq]
  exact hv q hq

@[expose] def kv (a b p : Nat) : Nat := (if a.testBit p then 1 else 0) + (if b.testBit p then 2 else 0)

@[expose] noncomputable def cv (c p : Nat) : Nat := kv (lo c) (hi c) p

@[expose] def KV (a b : Nat) : Prop := ∀ p < 524288, ¬ (a.testBit p = true ∧ b.testBit p = true)

theorem testBit_onesW (W q : Nat) : (ones W).testBit q = decide (q < W) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_full (p : Nat) : full.testBit p = decide (p < 524288) := testBit_onesW 524288 p

theorem testBit_lo (c p : Nat) : (lo c).testBit p = (decide (p < 524288) && c.testBit p) := by
  unfold lo
  rw [nland, Nat.testBit_and, testBit_full, Bool.and_comm]

theorem testBit_hi (c p : Nat) : (hi c).testBit p = c.testBit (p + 524288) := by
  unfold hi
  rw [nshr, Nat.testBit_shiftRight, Nat.add_comm]

theorem testBit_mk (a b p : Nat) :
    (mk a b).testBit p = (a.testBit p || (decide (524288 ≤ p) && b.testBit (p - 524288))) := by
  unfold mk
  rw [nlor, nshl, Nat.testBit_or, Nat.testBit_shiftLeft]

theorem lo_mk_bit (a b : Nat) {p : Nat} (hp : p < 524288) : (lo (mk a b)).testBit p = a.testBit p := by
  rw [testBit_lo, testBit_mk, decide_eq_true hp, decide_eq_false (by omega)]
  simp

theorem hi_mk_bit {a b : Nat} (ha : ∀ q, 524288 ≤ q → a.testBit q = false) (p : Nat) :
    (hi (mk a b)).testBit p = b.testBit p := by
  rw [testBit_hi, testBit_mk, ha _ (by omega), decide_eq_true (by omega)]
  simp

theorem testBit_zer (a b p : Nat) :
    (zer a b).testBit p = (decide (p < 524288) && !(a.testBit p || b.testBit p)) := by
  unfold zer
  rw [nxor, nland, nlor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, testBit_full]
  cases decide (p < 524288) <;> cases a.testBit p <;> cases b.testBit p <;> rfl

theorem testBit_add3a (a0 a1 b0 b1 p : Nat) :
    (add3a a0 a1 b0 b1).testBit p =
      (((decide (p < 524288) && !(a0.testBit p || a1.testBit p)) && b0.testBit p) ||
        (a0.testBit p && (decide (p < 524288) && !(b0.testBit p || b1.testBit p))) ||
          (a1.testBit p && b1.testBit p)) := by
  unfold add3a
  rw [nlor, nlor, nland, nland, nland, Nat.testBit_or, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_and, testBit_zer, testBit_zer]

theorem testBit_add3b (a0 a1 b0 b1 p : Nat) :
    (add3b a0 a1 b0 b1).testBit p =
      (((decide (p < 524288) && !(a0.testBit p || a1.testBit p)) && b1.testBit p) ||
        (a0.testBit p && b0.testBit p) ||
          (a1.testBit p && (decide (p < 524288) && !(b0.testBit p || b1.testBit p)))) := by
  unfold add3b
  rw [nlor, nlor, nland, nland, nland, Nat.testBit_or, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_and, testBit_zer, testBit_zer]

theorem add3_at {a0 a1 b0 b1 p : Nat} (hp : p < 524288)
    (ha : ¬ (a0.testBit p = true ∧ a1.testBit p = true))
    (hb : ¬ (b0.testBit p = true ∧ b1.testBit p = true)) :
    kv (add3a a0 a1 b0 b1) (add3b a0 a1 b0 b1) p = (kv a0 a1 p + kv b0 b1 p) % 3 ∧
      ¬ ((add3a a0 a1 b0 b1).testBit p = true ∧ (add3b a0 a1 b0 b1).testBit p = true) := by
  unfold kv
  rw [testBit_add3a, testBit_add3b, decide_eq_true hp]
  revert ha hb
  cases a0.testBit p <;> cases a1.testBit p <;> cases b0.testBit p <;> cases b1.testBit p <;> decide

theorem add3a_small {a0 a1 b0 b1 : Nat} (hb : ∀ q, 524288 ≤ q → b1.testBit q = false) :
    ∀ q, 524288 ≤ q → (add3a a0 a1 b0 b1).testBit q = false := by
  intro q hq
  rw [testBit_add3a, decide_eq_false (by omega), hb q hq]
  simp

theorem add3b_small {a0 a1 b0 b1 : Nat} (hb : ∀ q, 524288 ≤ q → b0.testBit q = false) :
    ∀ q, 524288 ≤ q → (add3b a0 a1 b0 b1).testBit q = false := by
  intro q hq
  rw [testBit_add3b, decide_eq_false (by omega), hb q hq]
  simp

theorem kapOK_spec {KA KB : Nat → Nat} {j : Nat} (h : kapOK KA KB j = true) :
    (∀ p, ¬ ((KA j).testBit p = true ∧ (KB j).testBit p = true)) ∧
      (∀ q, 306936 ≤ q → (KA j).testBit q = false) ∧ (∀ q, 306936 ≤ q → (KB j).testBit q = false) := by
  unfold kapOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h2
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  refine ⟨fun p hp => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have := congrArg (fun x => x.testBit p) e1
    simp only [nland, Nat.testBit_and, Nat.zero_testBit, hp.1, hp.2] at this
    exact absurd this (by decide)
  · have := congrArg (fun x => x.testBit (q - 306936)) e2
    simp only [nshr, Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rwa [show 306936 + (q - 306936) = q by omega] at this
  · have := congrArg (fun x => x.testBit (q - 306936)) e3
    simp only [nshr, Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rwa [show 306936 + (q - 306936) = q by omega] at this

@[expose] noncomputable def lK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) : Int → Nat → Nat
  | Int.ofNat m, p => if m = 0 then 0 else kv (KA (m - 1)) (KB (m - 1)) p
  | Int.negSucc n, p => (2 * kv (KA n) (KB n) (pR (NW n) p)) % 3

@[expose] noncomputable def kW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) : List Int → Nat → Nat
  | [], _ => 0
  | z :: w, p => (kW NW KA KB w p + lK NW KA KB z (w.foldr (fibF NW) p)) % 3

@[expose] def WOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) : Prop :=
  ∀ z ∈ w, netOK (NW (z.natAbs - 1)) = true ∧ kapOK KA KB (z.natAbs - 1) = true

theorem WOK.tail {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} {w : List Int}
    (h : WOK NW KA KB (z :: w)) : WOK NW KA KB w :=
  fun z' hz' => h z' (List.mem_cons_of_mem z hz')

theorem WOK.wnv {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} (h : WOK NW KA KB w) :
    WNV NW w := fun z hz => (net_spec (h z hz).1).1

theorem kv_lt (a b p : Nat) (h : ¬ (a.testBit p = true ∧ b.testBit p = true)) : kv a b p < 3 := by
  unfold kv
  revert h
  cases a.testBit p <;> cases b.testBit p <;> decide

theorem kv_swap (a b p : Nat) (h : ¬ (a.testBit p = true ∧ b.testBit p = true)) :
    kv b a p = (2 * kv a b p) % 3 := by
  unfold kv
  revert h
  cases a.testBit p <;> cases b.testBit p <;> decide

@[expose] def Good (c : Nat) : Prop :=
  (∀ q, 524288 ≤ q → (lo c).testBit q = false) ∧ (∀ q, 524288 ≤ q → (hi c).testBit q = false) ∧
    ∀ p < 524288, ¬ ((lo c).testBit p = true ∧ (hi c).testBit p = true)

theorem good_zero : Good 0 := by
  refine ⟨fun q _ => ?_, fun q _ => ?_, fun p _ h => ?_⟩
  · rw [testBit_lo]
    simp
  · rw [testBit_hi]
    simp
  · rw [testBit_lo] at h
    simp at h

theorem lo_small (c : Nat) : ∀ q, 524288 ≤ q → (lo c).testBit q = false := by
  intro q hq
  rw [testBit_lo, decide_eq_false (by omega)]
  rfl

theorem good_mk {a b : Nat} (ha : ∀ q, 524288 ≤ q → a.testBit q = false)
    (hb : ∀ q, 524288 ≤ q → b.testBit q = false)
    (hab : ∀ p < 524288, ¬ (a.testBit p = true ∧ b.testBit p = true)) : Good (mk a b) := by
  refine ⟨lo_small _, fun q hq => ?_, fun p hp => ?_⟩
  · rw [hi_mk_bit ha]
    exact hb q hq
  · rw [lo_mk_bit a b hp, hi_mk_bit ha]
    exact hab p hp

theorem cv_mk {a b : Nat} (ha : ∀ q, 524288 ≤ q → a.testBit q = false) {p : Nat} (hp : p < 524288) :
    cv (mk a b) p = kv a b p := by
  unfold cv kv
  rw [lo_mk_bit a b hp, hi_mk_bit ha]

theorem stepK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int}
    (hz : NV (NW (z.natAbs - 1)) ∧ kapOK KA KB (z.natAbs - 1) = true) {c : Nat} (hc : Good c) :
    Good (stepK NW KA KB z c) ∧
      ∀ p < 524288, cv (stepK NW KA KB z c) p = (lK NW KA KB z p + cv c (fibF NW z p)) % 3 := by
  obtain ⟨hv, hk⟩ := hz
  obtain ⟨hcl, hch, hcv⟩ := hc
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      have e : stepK NW KA KB (Int.ofNat 0) c = c := rfl
      rw [e]
      refine ⟨⟨hcl, hch, hcv⟩, fun p hp => ?_⟩
      have e1 : lK NW KA KB (Int.ofNat 0) p = 0 := rfl
      have e2 : fibF NW (Int.ofNat 0) p = p := rfl
      rw [e1, e2, Nat.zero_add]
      exact (Nat.mod_eq_of_lt (kv_lt (lo c) (hi c) p (hcv p hp))).symm
    · have hv' : NV (NW (m - 1)) := hv
      have hk' : kapOK KA KB (m - 1) = true := hk
      obtain ⟨hkd, hka, hkb⟩ := kapOK_spec hk'
      have e : stepK NW KA KB (Int.ofNat m) c =
          add3 (netF (NW (m - 1)) (lo c)) (netF (NW (m - 1)) (hi c)) (KA (m - 1)) (KB (m - 1)) := by
        change Bool.rec (motive := fun _ => Nat) _ c (Nat.beq m 0) = _
        rw [beq_false hm]
        rfl
      have eF : fibF NW (Int.ofNat m) = pF (NW (m - 1)) := if_neg hm
      have eK : ∀ p, lK NW KA KB (Int.ofNat m) p = kv (KA (m - 1)) (KB (m - 1)) p := fun p => if_neg hm
      rw [e, eF]
      have hka' : ∀ q, 524288 ≤ q → (KA (m - 1)).testBit q = false := fun q hq => hka q (by omega)
      have hkb' : ∀ q, 524288 ≤ q → (KB (m - 1)).testBit q = false := fun q hq => hkb q (by omega)
      have hat : ∀ p < 524288,
          ¬ ((netF (NW (m - 1)) (lo c)).testBit p = true ∧ (netF (NW (m - 1)) (hi c)).testBit p = true) := by
        intro p hp
        rw [testBit_netF hv', testBit_netF hv']
        exact hcv _ (pF_lt hv' hp)
      refine ⟨good_mk (add3a_small hkb') (add3b_small hka') fun p hp => (add3_at hp (hat p hp) (hkd p)).2,
        fun p hp => ?_⟩
      unfold add3
      rw [cv_mk (add3a_small hkb') hp, (add3_at hp (hat p hp) (hkd p)).1, eK]
      have hX : kv (netF (NW (m - 1)) (lo c)) (netF (NW (m - 1)) (hi c)) p =
          cv c (pF (NW (m - 1)) p) := by
        unfold cv
        unfold kv
        rw [testBit_netF hv', testBit_netF hv']
      rw [hX, Nat.add_comm]
  | negSucc n =>
    have hv' : NV (NW n) := hv
    have hk' : kapOK KA KB n = true := hk
    obtain ⟨hkd, hka, hkb⟩ := kapOK_spec hk'
    have e : stepK NW KA KB (Int.negSucc n) c =
        mk (netR (NW n) (add3a (lo c) (hi c) (KB n) (KA n)))
          (netR (NW n) (add3b (lo c) (hi c) (KB n) (KA n))) := rfl
    have hka' : ∀ q, 524288 ≤ q → (KA n).testBit q = false := fun q hq => hka q (by omega)
    have hkb' : ∀ q, 524288 ≤ q → (KB n).testBit q = false := fun q hq => hkb q (by omega)
    have hkd' : ∀ p, ¬ ((KB n).testBit p = true ∧ (KA n).testBit p = true) :=
      fun p h => hkd p ⟨h.2, h.1⟩
    rw [e]
    have hs1 := netR_small hv' (add3a_small (a0 := lo c) (a1 := hi c) (b0 := KB n) hka')
    have hs2 := netR_small hv' (add3b_small (a0 := lo c) (a1 := hi c) (b1 := KA n) hkb')
    refine ⟨good_mk hs1 hs2 fun p hp => ?_, fun p hp => ?_⟩
    · rw [testBit_netR hv', testBit_netR hv']
      exact (add3_at (pR_lt hv' hp) (hcv _ (pR_lt hv' hp)) (hkd' _)).2
    · rw [cv_mk hs1 hp]
      have hx := pR_lt hv' hp
      have key := (add3_at hx (hcv _ hx) (hkd' _)).1
      have e3 : kv (netR (NW n) (add3a (lo c) (hi c) (KB n) (KA n)))
          (netR (NW n) (add3b (lo c) (hi c) (KB n) (KA n))) p =
          kv (add3a (lo c) (hi c) (KB n) (KA n)) (add3b (lo c) (hi c) (KB n) (KA n)) (pR (NW n) p) := by
        unfold kv
        rw [testBit_netR hv', testBit_netR hv']
      rw [e3, key, kv_swap _ _ _ (hkd _)]
      change _ = ((2 * kv (KA n) (KB n) (pR (NW n) p)) % 3 + cv c (pR (NW n) p)) % 3
      unfold cv
      omega

theorem walkK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} :
    ∀ (w : List Int), WOK NW KA KB w → ∀ c, Good c →
      Good (walkK NW KA KB w c) ∧ ∀ p < 524288,
        cv (walkK NW KA KB w c) p = (kW NW KA KB w p + cv c (w.foldr (fibF NW) p)) % 3
  | [], _, c, hc => by
    refine ⟨hc, fun p hp => ?_⟩
    change cv c p = (0 + cv c p) % 3
    rw [Nat.zero_add]
    exact (Nat.mod_eq_of_lt (kv_lt (lo c) (hi c) p (hc.2.2 p hp))).symm
  | z :: w, h, c, hc => by
    have e : walkK NW KA KB (z :: w) c = walkK NW KA KB w (stepK NW KA KB z c) := strictN_eq' _ _
    obtain ⟨hg, hs⟩ := stepK_spec ⟨(net_spec (h z List.mem_cons_self).1).1, (h z List.mem_cons_self).2⟩ hc
    obtain ⟨hg2, hs2⟩ := walkK_spec w h.tail _ hg
    rw [e]
    refine ⟨hg2, fun p hp => ?_⟩
    have hq := foldrF_lt w h.tail.wnv p hp
    rw [hs2 p hp, hs _ hq]
    change _ = ((kW NW KA KB w p + lK NW KA KB z (w.foldr (fibF NW) p)) % 3 +
      cv c (fibF NW z (w.foldr (fibF NW) p))) % 3
    omega

theorem kW_lt (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) : ∀ (w : List Int) (p : Nat), kW NW KA KB w p < 3
  | [], _ => Nat.zero_lt_succ 2
  | _ :: _, _ => Nat.mod_lt _ (by decide)

theorem cv_zero (p : Nat) : cv 0 p = 0 := by
  unfold cv kv
  rw [testBit_lo, testBit_hi]
  simp

theorem wordK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} {j : Nat}
    (hkj : kapOK KA KB j = true) (hw : WOK NW KA KB w) (h : wordKOK NW KA KB w j = true) :
    ∀ p < 524288, kv (KA j) (KB j) p = kW NW KA KB w p := by
  intro p hp
  have hka : ∀ q, 524288 ≤ q → (KA j).testBit q = false := fun q hq => (kapOK_spec hkj).2.1 q (by omega)
  have e := Nat.eq_of_beq_eq_true h
  have h2 := (walkK_spec w hw 0 good_zero).2 p hp
  rw [e, cv_mk hka hp, cv_zero, Nat.add_zero, Nat.mod_eq_of_lt (kW_lt NW KA KB w p)] at h2
  exact h2

theorem idK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} (hw : WOK NW KA KB w)
    (h : idKOK NW KA KB w = true) : ∀ p < 524288, kW NW KA KB w p = 0 := by
  intro p hp
  have e := Nat.eq_of_beq_eq_true h
  have h2 := (walkK_spec w hw 0 good_zero).2 p hp
  rw [e, cv_zero, cv_zero, Nat.add_zero, Nat.mod_eq_of_lt (kW_lt NW KA KB w p)] at h2
  exact h2.symm

@[expose] noncomputable def eL (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (N : Nat) : Nat :=
  if N < 920808 then 3 * fibF NW z (N / 3) + (N % 3 + lK NW KA KB z (N / 3)) % 3 else N

@[expose] noncomputable def eW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) : Nat → Nat :=
  w.foldr (fun z f N => eL NW KA KB z (f N)) (fun N => N)

theorem eW_cons (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (w : List Int) (N : Nat) :
    eW NW KA KB (z :: w) N = eL NW KA KB z (eW NW KA KB w N) := rfl

theorem fibF_fib {NW : Nat → Nat → Nat} {z : Int} (hz : netOK (NW (z.natAbs - 1)) = true) {p : Nat}
    (hp : p < 306936) : fibF NW z p < 306936 := by
  obtain ⟨hv, hpt⟩ := net_spec hz
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      exact hp
    · have e2 : fibF NW (Int.ofNat m) = pF (NW (m - 1)) := if_neg hm
      rw [e2]
      exact (hpt p (by omega)).2 hp
  | negSucc n =>
    have hv' : NV (NW n) := hv
    have hpt' : ∀ q < 524288, (pF (NW n) q < 306936 ↔ q < 306936) := hpt
    change pR (NW n) p < 306936
    have := (hpt' _ (pR_lt hv' (by omega : p < 524288))).1
    rw [pF_pR hv'] at this
    exact this hp

theorem lK_lt {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int}
    (hz : kapOK KA KB (z.natAbs - 1) = true) (p : Nat) : lK NW KA KB z p < 3 := by
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      change 0 < 3
      decide
    · have e : lK NW KA KB (Int.ofNat m) p = kv (KA (m - 1)) (KB (m - 1)) p := if_neg hm
      rw [e]
      exact kv_lt _ _ _ ((kapOK_spec hz).1 p)
  | negSucc n => exact Nat.mod_lt _ (by decide)

theorem eW_eq {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} :
    ∀ (w : List Int), WOK NW KA KB w → ∀ N < 920808,
      eW NW KA KB w N = 3 * w.foldr (fibF NW) (N / 3) + (N % 3 + kW NW KA KB w (N / 3)) % 3 ∧
        w.foldr (fibF NW) (N / 3) < 306936
  | [], _, N, hN => by
    refine ⟨?_, by change N / 3 < 306936; omega⟩
    change N = 3 * (N / 3) + (N % 3 + 0) % 3
    omega
  | z :: w, h, N, hN => by
    obtain ⟨e, ha⟩ := eW_eq w h.tail N hN
    rw [eW_cons, e]
    have hlt : 3 * w.foldr (fibF NW) (N / 3) + (N % 3 + kW NW KA KB w (N / 3)) % 3 < 920808 := by
      have := Nat.mod_lt (N % 3 + kW NW KA KB w (N / 3)) (by decide : 3 > 0)
      omega
    have hd : (3 * w.foldr (fibF NW) (N / 3) + (N % 3 + kW NW KA KB w (N / 3)) % 3) / 3 =
        w.foldr (fibF NW) (N / 3) := by omega
    have hm : (3 * w.foldr (fibF NW) (N / 3) + (N % 3 + kW NW KA KB w (N / 3)) % 3) % 3 =
        (N % 3 + kW NW KA KB w (N / 3)) % 3 := by omega
    unfold eL
    rw [if_pos hlt, hd, hm]
    refine ⟨?_, fibF_fib (h z List.mem_cons_self).1 ha⟩
    change _ = 3 * fibF NW z (w.foldr (fibF NW) (N / 3)) +
      (N % 3 + (kW NW KA KB w (N / 3) + lK NW KA KB z (w.foldr (fibF NW) (N / 3))) % 3) % 3
    omega

@[expose] noncomputable def eE (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (j : Nat) : Nat → Nat :=
  eL NW KA KB (Int.ofNat (j + 1))

theorem eE_eq {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {j N : Nat} (hN : N < 920808) :
    eE NW KA KB j N = 3 * pF (NW j) (N / 3) + (N % 3 + kv (KA j) (KB j) (N / 3)) % 3 := by
  unfold eE eL
  rw [if_pos hN]
  rfl

theorem word_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} {j : Nat}
    (hj : netOK (NW j) = true) (hkj : kapOK KA KB j = true) (hw : WOK NW KA KB w)
    (h : ∀ k < 19, CFSG.KC.RouteP.wordOK NW w j k = true) (hk : wordKOK NW KA KB w j = true) :
    ∀ N < 920808, eE NW KA KB j N = eW NW KA KB w N := by
  intro N hN
  have hp : N / 3 < 524288 := by omega
  rw [eE_eq hN, (eW_eq w hw N hN).1, wordP_spec (net_spec hj).1 hw.wnv h _ hp,
    wordK_spec hkj hw hk _ hp]

theorem id_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} (hw : WOK NW KA KB w)
    (h : ∀ k < 19, idOK NW w k = true) (hk : idKOK NW KA KB w = true) :
    ∀ N < 920808, eW NW KA KB w N = N := by
  intro N hN
  have hp : N / 3 < 524288 := by omega
  rw [(eW_eq w hw N hN).1, idP_spec hw.wnv h _ hp, idK_spec hw hk _ hp]
  omega

end CFSG.KS.RouteP

end
