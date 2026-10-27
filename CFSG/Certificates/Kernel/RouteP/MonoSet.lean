module

public import CFSG.Certificates.Kernel.RouteP.MonoSound
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net

@[expose] def memS (s N : Nat) : Bool := s.testBit (N % 3 * 524288 + N / 3)

@[expose] def Clean (s : Nat) : Prop :=
  ∀ q, s.testBit q = true → q / 524288 < 3 ∧ q % 524288 < 306936

@[expose] def Small (v : Nat) : Prop := ∀ q, 524288 ≤ q → v.testBit q = false

theorem testBit_sh (s i p : Nat) :
    (sh s i).testBit p = (decide (p < 524288) && s.testBit (i * 524288 + p)) := by
  unfold sh
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, testBit_full, Bool.and_comm]

theorem sh_small (s i : Nat) : Small (sh s i) := by
  intro q hq
  rw [testBit_sh, decide_eq_false (by omega)]
  rfl

theorem testBit_mk3 {a b : Nat} (ha : Small a) (hb : Small b) (c q : Nat) :
    (mk3 a b c).testBit q =
      if q < 524288 then a.testBit q else if q < 1048576 then b.testBit (q - 524288)
      else c.testBit (q - 1048576) := by
  unfold mk3
  have r1 : (nat_lit 524288 : Nat) = 524288 := rfl
  have r2 : (nat_lit 1048576 : Nat) = 1048576 := rfl
  rw [nlor, nlor, nshl, nshl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, r1, r2]
  by_cases h1 : q < 524288
  · rw [if_pos h1, decide_eq_false (by omega), decide_eq_false (by omega)]
    simp
  · rw [if_neg h1, ha q (by omega), decide_eq_true (by omega)]
    by_cases h2 : q < 1048576
    · rw [if_pos h2, decide_eq_false (by omega)]
      simp
    · rw [if_neg h2, hb _ (by omega), decide_eq_true (by omega)]
      simp

theorem sh_mk3 {a b c : Nat} (ha : Small a) (hb : Small b) (hc : Small c) {p : Nat} (hp : p < 524288) :
    (sh (mk3 a b c) 0).testBit p = a.testBit p ∧ (sh (mk3 a b c) 1).testBit p = b.testBit p ∧
      (sh (mk3 a b c) 2).testBit p = c.testBit p := by
  rw [testBit_sh, testBit_sh, testBit_sh, decide_eq_true hp, testBit_mk3 ha hb, testBit_mk3 ha hb,
    testBit_mk3 ha hb]
  refine ⟨?_, ?_, ?_⟩
  · rw [if_pos (by omega), Nat.zero_mul, Nat.zero_add, Bool.true_and]
  · rw [if_neg (by omega), if_pos (by omega), Bool.true_and,
      show 1 * 524288 + p - 524288 = p by omega]
  · rw [if_neg (by omega), if_neg (by omega), Bool.true_and,
      show 2 * 524288 + p - 1048576 = p by omega]

theorem small_and_left {a b : Nat} (ha : Small a) : Small (Nat.land a b) := by
  intro q hq
  rw [nland, Nat.testBit_and, ha q hq]
  rfl

theorem small_and_right {a b : Nat} (hb : Small b) : Small (Nat.land a b) := by
  intro q hq
  rw [nland, Nat.testBit_and, hb q hq]
  simp

theorem small_or {a b : Nat} (ha : Small a) (hb : Small b) : Small (Nat.lor a b) := by
  intro q hq
  rw [nlor, Nat.testBit_or, ha q hq, hb q hq]
  rfl

theorem zer_small (a b : Nat) : Small (zer a b) := by
  intro q hq
  rw [testBit_zer, decide_eq_false (by omega)]
  rfl

theorem rotS_eq (a b s0 s1 s2 : Nat) : rotS a b s0 s1 s2 =
    mk3 (Nat.lor (Nat.lor (Nat.land (zer a b) s0) (Nat.land a s2)) (Nat.land b s1))
      (Nat.lor (Nat.lor (Nat.land (zer a b) s1) (Nat.land a s0)) (Nat.land b s2))
      (Nat.lor (Nat.lor (Nat.land (zer a b) s2) (Nat.land a s1)) (Nat.land b s0)) := rfl

theorem rotS_bit {a b s0 s1 s2 : Nat} (ha : Small a) (hb : Small b) {p : Nat} (hp : p < 524288)
    (hab : ¬ (a.testBit p = true ∧ b.testBit p = true)) (i : Nat) (hi : i < 3) :
    (sh (rotS a b s0 s1 s2) i).testBit p =
      (if (i + 2 * kv a b p) % 3 = 0 then s0 else if (i + 2 * kv a b p) % 3 = 1 then s1 else s2).testBit p := by
  have hs : ∀ x y z : Nat, Small (Nat.lor (Nat.lor (Nat.land (zer a b) x) (Nat.land a y)) (Nat.land b z)) :=
    fun x y z => small_or (small_or (small_and_left (zer_small a b)) (small_and_left ha)) (small_and_left hb)
  obtain ⟨e0, e1, e2⟩ := sh_mk3 (hs s0 s2 s1) (hs s1 s0 s2) (hs s2 s1 s0) hp
  rw [rotS_eq]
  have hz : (zer a b).testBit p = !(a.testBit p || b.testBit p) := by
    rw [testBit_zer, decide_eq_true hp, Bool.true_and]
  unfold kv
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [e0]
    simp only [nlor, nland, Nat.testBit_or, Nat.testBit_and, hz]
    revert hab
    cases a.testBit p <;> cases b.testBit p <;> simp
  · rw [e1]
    simp only [nlor, nland, Nat.testBit_or, Nat.testBit_and, hz]
    revert hab
    cases a.testBit p <;> cases b.testBit p <;> simp
  · rw [e2]
    simp only [nlor, nland, Nat.testBit_or, Nat.testBit_and, hz]
    revert hab
    cases a.testBit p <;> cases b.testBit p <;> simp

theorem sel3 (f : Nat → Nat) {i : Nat} (hi : i < 3) :
    (if i = 0 then f 0 else if i = 1 then f 1 else f 2) = f i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

@[expose] def LOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) : Prop :=
  netOK (NW (z.natAbs - 1)) = true ∧ kapOK KA KB (z.natAbs - 1) = true

theorem memS_imgS {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} (hz : LOK NW KA KB z) (s : Nat)
    {M : Nat} (hM : M < 920808) : memS (imgS NW KA KB z s) (eL NW KA KB z M) = memS s M := by
  have hp3 : M / 3 < 306936 := by omega
  have hp : M / 3 < 524288 := by omega
  have hi : M % 3 < 3 := Nat.mod_lt _ (by decide)
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      have e : eL NW KA KB (Int.ofNat 0) M = M := by
        unfold eL
        rw [if_pos hM]
        change 3 * (M / 3) + (M % 3 + 0) % 3 = M
        omega
      rw [e]
      rfl
    · obtain ⟨hn, hk⟩ := hz
      have hn' : netOK (NW (m - 1)) = true := hn
      have hk' : kapOK KA KB (m - 1) = true := hk
      obtain ⟨hv, hpt⟩ := net_spec hn'
      obtain ⟨hkd, hka, hkb⟩ := kapOK_spec hk'
      have hka' : Small (KA (m - 1)) := fun q hq => hka q (by omega)
      have hkb' : Small (KB (m - 1)) := fun q hq => hkb q (by omega)
      have eF : fibF NW (Int.ofNat m) = pF (NW (m - 1)) := if_neg hm
      have eK : lK NW KA KB (Int.ofNat m) (M / 3) = kv (KA (m - 1)) (KB (m - 1)) (M / 3) := if_neg hm
      have hπ := (hpt _ hp).2 hp3
      set κ := kv (KA (m - 1)) (KB (m - 1)) (M / 3) with hκ
      have hκ3 : κ < 3 := kv_lt _ _ _ (hkd _)
      have e : eL NW KA KB (Int.ofNat m) M = 3 * pF (NW (m - 1)) (M / 3) + (M % 3 + κ) % 3 := by
        unfold eL
        rw [if_pos hM, eF, eK]
      rw [e]
      have hd : (3 * pF (NW (m - 1)) (M / 3) + (M % 3 + κ) % 3) / 3 = pF (NW (m - 1)) (M / 3) := by
        omega
      have hmd : (3 * pF (NW (m - 1)) (M / 3) + (M % 3 + κ) % 3) % 3 = (M % 3 + κ) % 3 := by omega
      unfold memS
      rw [hd, hmd]
      have himg : imgS NW KA KB (Int.ofNat m) s =
          (fun r => mk3 (netR (NW (m - 1)) (sh r 0)) (netR (NW (m - 1)) (sh r 1))
            (netR (NW (m - 1)) (sh r 2)))
            (rotS (KA (m - 1)) (KB (m - 1)) (sh s 0) (sh s 1) (sh s 2)) := by
        change Bool.rec (motive := fun _ => Nat) _ s (Nat.beq m 0) = _
        rw [beq_false hm]
        rfl
      rw [himg]
      simp only
      set r := rotS (KA (m - 1)) (KB (m - 1)) (sh s 0) (sh s 1) (sh s 2)
      have hs : ∀ i, Small (netR (NW (m - 1)) (sh r i)) := fun i => netR_small hv (sh_small r i)
      have hpt3 : (pF (NW (m - 1)) (M / 3)) < 524288 := by omega
      have key : ∀ i < 3, (mk3 (netR (NW (m - 1)) (sh r 0)) (netR (NW (m - 1)) (sh r 1))
          (netR (NW (m - 1)) (sh r 2))).testBit (i * 524288 + pF (NW (m - 1)) (M / 3)) =
          (sh r i).testBit (M / 3) := by
        intro i hi3
        rw [testBit_mk3 (hs 0) (hs 1)]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · rw [if_pos (by omega), Nat.zero_mul, Nat.zero_add, testBit_netR hv, pR_pF hv]
        · rw [if_neg (by omega), if_pos (by omega), testBit_netR hv,
            show 1 * 524288 + pF (NW (m - 1)) (M / 3) - 524288 = pF (NW (m - 1)) (M / 3) by omega,
            pR_pF hv]
        · rw [if_neg (by omega), if_neg (by omega), testBit_netR hv,
            show 2 * 524288 + pF (NW (m - 1)) (M / 3) - 1048576 = pF (NW (m - 1)) (M / 3) by omega,
            pR_pF hv]
      rw [key _ (Nat.mod_lt _ (by decide)),
        rotS_bit hka' hkb' hp (hkd _) _ (Nat.mod_lt _ (by decide)),
        sel3 (sh s) (Nat.mod_lt _ (by decide))]
      have hsel : ((M % 3 + κ) % 3 + 2 * κ) % 3 = M % 3 := by omega
      rw [← hκ, hsel, testBit_sh, decide_eq_true hp, Bool.true_and]
  | negSucc n =>
    obtain ⟨hn, hk⟩ := hz
    have hn' : netOK (NW n) = true := hn
    have hk' : kapOK KA KB n = true := hk
    obtain ⟨hv, hpt⟩ := net_spec hn'
    obtain ⟨hkd, hka, hkb⟩ := kapOK_spec hk'
    have hka' : Small (KA n) := fun q hq => hka q (by omega)
    have hkb' : Small (KB n) := fun q hq => hkb q (by omega)
    have hq : pR (NW n) (M / 3) < 306936 := fibF_fib (z := Int.negSucc n) hn hp3
    have hq' : pR (NW n) (M / 3) < 524288 := by omega
    set κ := kv (KA n) (KB n) (pR (NW n) (M / 3)) with hκ
    have hκ3 : κ < 3 := kv_lt _ _ _ (hkd _)
    have e : eL NW KA KB (Int.negSucc n) M = 3 * pR (NW n) (M / 3) + (M % 3 + (2 * κ) % 3) % 3 := by
      unfold eL
      rw [if_pos hM]
      rfl
    rw [e]
    have hd : (3 * pR (NW n) (M / 3) + (M % 3 + (2 * κ) % 3) % 3) / 3 = pR (NW n) (M / 3) := by omega
    have hmd : (3 * pR (NW n) (M / 3) + (M % 3 + (2 * κ) % 3) % 3) % 3 = (M % 3 + (2 * κ) % 3) % 3 := by
      omega
    unfold memS
    rw [hd, hmd]
    have himg : imgS NW KA KB (Int.negSucc n) s =
        (fun r => rotS (KB n) (KA n) (sh r 0) (sh r 1) (sh r 2))
          (mk3 (netF (NW n) (sh s 0)) (netF (NW n) (sh s 1)) (netF (NW n) (sh s 2))) := rfl
    rw [himg]
    simp only
    set t := mk3 (netF (NW n) (sh s 0)) (netF (NW n) (sh s 1)) (netF (NW n) (sh s 2))
    have hsF : ∀ i, Small (netF (NW n) (sh s i)) := by
      intro i q hq
      rw [testBit_netF hv, pF_ge hv hq]
      exact sh_small s i q hq
    have hkd' : ¬ ((KB n).testBit (pR (NW n) (M / 3)) = true ∧ (KA n).testBit (pR (NW n) (M / 3)) = true) :=
      fun h => hkd _ ⟨h.2, h.1⟩
    have hrot := rotS_bit (s0 := sh t 0) (s1 := sh t 1) (s2 := sh t 2) hkb' hka' hq' hkd'
      ((M % 3 + (2 * κ) % 3) % 3) (Nat.mod_lt _ (by decide))
    have hpos : ((M % 3 + (2 * κ) % 3) % 3) * 524288 + pR (NW n) (M / 3) =
        ((M % 3 + (2 * κ) % 3) % 3) * 524288 + pR (NW n) (M / 3) := rfl
    have hshr : (sh (rotS (KB n) (KA n) (sh t 0) (sh t 1) (sh t 2)) ((M % 3 + (2 * κ) % 3) % 3)).testBit
        (pR (NW n) (M / 3)) = (rotS (KB n) (KA n) (sh t 0) (sh t 1) (sh t 2)).testBit
          (((M % 3 + (2 * κ) % 3) % 3) * 524288 + pR (NW n) (M / 3)) := by
      rw [testBit_sh, decide_eq_true hq', Bool.true_and]
    rw [← hshr, hrot, kv_swap _ _ _ (hkd _), sel3 (sh t) (Nat.mod_lt _ (by decide))]
    have hsel : ((M % 3 + (2 * κ) % 3) % 3 + 2 * ((2 * κ) % 3)) % 3 = M % 3 := by omega
    rw [← hκ, hsel]
    obtain ⟨t0, t1, t2⟩ := sh_mk3 (hsF 0) (hsF 1) (hsF 2) hq'
    have hF : ∀ i < 3, (netF (NW n) (sh s i)).testBit (pR (NW n) (M / 3)) = s.testBit (i * 524288 + M / 3) := by
      intro i _
      rw [testBit_netF hv, pF_pR hv, testBit_sh, decide_eq_true hp, Bool.true_and]
    rcases (by omega : M % 3 = 0 ∨ M % 3 = 1 ∨ M % 3 = 2) with h | h | h
    · rw [h, t0, hF 0 (by decide)]
    · rw [h, t1, hF 1 (by decide)]
    · rw [h, t2, hF 2 (by decide)]

theorem eL_zero (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) {N : Nat} (hN : N < 920808) :
    eL NW KA KB (Int.ofNat 0) N = N := by
  unfold eL
  rw [if_pos hN]
  change 3 * (N / 3) + (N % 3 + 0) % 3 = N
  omega

theorem eL_pos_neg {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {n : Nat} (hn : netOK (NW n) = true)
    (hk : kapOK KA KB n = true) {N : Nat} (hN : N < 920808) :
    eL NW KA KB (Int.negSucc n) N < 920808 ∧
      eL NW KA KB (Int.ofNat (n + 1)) (eL NW KA KB (Int.negSucc n) N) = N ∧
      eL NW KA KB (Int.ofNat (n + 1)) N < 920808 ∧
      eL NW KA KB (Int.negSucc n) (eL NW KA KB (Int.ofNat (n + 1)) N) = N := by
  obtain ⟨hv, -⟩ := net_spec hn
  have hp3 : N / 3 < 306936 := by omega
  have hq : pR (NW n) (N / 3) < 306936 := fibF_fib (z := Int.negSucc n) hn hp3
  have hf : pF (NW n) (N / 3) < 306936 := fibF_fib (z := Int.ofNat (n + 1)) hn hp3
  have hkd := (kapOK_spec hk).1
  have k1 := kv_lt (KA n) (KB n) (pR (NW n) (N / 3)) (hkd _)
  have k2 := kv_lt (KA n) (KB n) (N / 3) (hkd _)
  have e1 : eL NW KA KB (Int.negSucc n) N =
      3 * pR (NW n) (N / 3) + (N % 3 + (2 * kv (KA n) (KB n) (pR (NW n) (N / 3))) % 3) % 3 := by
    unfold eL
    rw [if_pos hN]
    rfl
  have e2 : ∀ M, M < 920808 → eL NW KA KB (Int.ofNat (n + 1)) M =
      3 * pF (NW n) (M / 3) + (M % 3 + kv (KA n) (KB n) (M / 3)) % 3 := by
    intro M hM
    unfold eL
    rw [if_pos hM]
    rfl
  have e3 : ∀ M, M < 920808 → eL NW KA KB (Int.negSucc n) M =
      3 * pR (NW n) (M / 3) + (M % 3 + (2 * kv (KA n) (KB n) (pR (NW n) (M / 3))) % 3) % 3 := by
    intro M hM
    unfold eL
    rw [if_pos hM]
    rfl
  have l1 : eL NW KA KB (Int.negSucc n) N < 920808 := by rw [e1]; omega
  have l2 : eL NW KA KB (Int.ofNat (n + 1)) N < 920808 := by rw [e2 N hN]; omega
  refine ⟨l1, ?_, l2, ?_⟩
  · rw [e2 _ l1, e1]
    have hd : (3 * pR (NW n) (N / 3) + (N % 3 + (2 * kv (KA n) (KB n) (pR (NW n) (N / 3))) % 3) % 3) / 3 =
        pR (NW n) (N / 3) := by omega
    have hm : (3 * pR (NW n) (N / 3) + (N % 3 + (2 * kv (KA n) (KB n) (pR (NW n) (N / 3))) % 3) % 3) % 3 =
        (N % 3 + (2 * kv (KA n) (KB n) (pR (NW n) (N / 3))) % 3) % 3 := by omega
    rw [hd, hm, pF_pR hv]
    omega
  · rw [e3 _ l2, e2 N hN]
    have hd : (3 * pF (NW n) (N / 3) + (N % 3 + kv (KA n) (KB n) (N / 3)) % 3) / 3 = pF (NW n) (N / 3) := by
      omega
    have hm : (3 * pF (NW n) (N / 3) + (N % 3 + kv (KA n) (KB n) (N / 3)) % 3) % 3 =
        (N % 3 + kv (KA n) (KB n) (N / 3)) % 3 := by omega
    rw [hd, hm, pR_pF hv]
    omega

theorem eL_surj {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} (hz : LOK NW KA KB z) {N : Nat}
    (hN : N < 920808) : ∃ M < 920808, eL NW KA KB z M = N := by
  cases z with
  | ofNat m =>
    rcases m with _ | n
    · exact ⟨N, hN, eL_zero NW KA KB hN⟩
    · obtain ⟨l1, e, -, -⟩ := eL_pos_neg (n := n) hz.1 hz.2 hN
      exact ⟨_, l1, e⟩
  | negSucc n =>
    obtain ⟨-, -, l2, e⟩ := eL_pos_neg (n := n) hz.1 hz.2 hN
    exact ⟨_, l2, e⟩

theorem memS_imgS_iff {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} (hz : LOK NW KA KB z) (s : Nat)
    {N : Nat} (hN : N < 920808) (h : memS (imgS NW KA KB z s) N = true) :
    ∃ M < 920808, memS s M = true ∧ eL NW KA KB z M = N := by
  obtain ⟨M, hM, rfl⟩ := eL_surj hz hN
  exact ⟨M, hM, by rwa [memS_imgS hz s hM] at h, rfl⟩

theorem memS_lor (a b N : Nat) : memS (Nat.lor a b) N = (memS a N || memS b N) := by
  unfold memS
  rw [nlor, Nat.testBit_or]

theorem roundS_cons (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (gens : List Int) (s : Nat) :
    roundS NW KA KB (z :: gens) s = Nat.lor (roundS NW KA KB gens s) (imgS NW KA KB z s) := by
  change strictN (roundS NW KA KB gens s) (fun t => Nat.lor t (imgS NW KA KB z s)) = _
  exact strictN_eq' _ _

theorem memS_roundS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (s N : Nat) :
    ∀ gens : List Int, memS (roundS NW KA KB gens s) N = true →
      memS s N = true ∨ ∃ z ∈ gens, memS (imgS NW KA KB z s) N = true
  | [], h => Or.inl h
  | z :: gens, h => by
    rw [roundS_cons, memS_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases memS_roundS NW KA KB s N gens h with h | ⟨z', hz', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨z', List.mem_cons_of_mem z hz', h⟩
    · exact Or.inr ⟨z, List.mem_cons_self, h⟩

theorem memS_roundS_of (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) {s N : Nat} (h : memS s N = true) :
    ∀ gens : List Int, memS (roundS NW KA KB gens s) N = true
  | [] => h
  | z :: gens => by
    rw [roundS_cons, memS_lor, memS_roundS_of NW KA KB h gens]
    rfl

theorem closeS_succ (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (n s : Nat) :
    closeS NW KA KB gens (n + 1) s = closeS NW KA KB gens n (roundS NW KA KB gens s) :=
  strictN_eq' _ _

theorem memS_closeS_of (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) :
    ∀ n s N, memS s N = true → memS (closeS NW KA KB gens n s) N = true
  | 0, _, _, h => h
  | n + 1, s, N, h => by
    rw [closeS_succ]
    exact memS_closeS_of NW KA KB gens n _ N (memS_roundS_of NW KA KB h gens)

theorem closeS_min {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int}
    (hg : ∀ z ∈ gens, LOK NW KA KB z) (P : Nat → Prop)
    (hP : ∀ N, P N → ∀ z ∈ gens, P (eL NW KA KB z N)) :
    ∀ n s, (∀ N < 920808, memS s N = true → P N) →
      ∀ N < 920808, memS (closeS NW KA KB gens n s) N = true → P N
  | 0, _, h => h
  | n + 1, s, h => by
    rw [closeS_succ]
    refine closeS_min hg P hP n _ fun N hN hm => ?_
    rcases memS_roundS NW KA KB s N gens hm with hm | ⟨z, hz, hm⟩
    · exact h N hN hm
    · obtain ⟨M, hM, hMs, rfl⟩ := memS_imgS_iff (hg z hz) s hN hm
      exact hP M (h M hM hMs) z hz

theorem closedS_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {s : Nat} :
    ∀ gens : List Int, closedS NW KA KB gens s = true → ∀ z ∈ gens, imgS NW KA KB z s = s
  | [], _, _, hz => absurd hz List.not_mem_nil
  | z :: gens, h, z', hz' => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hz' with rfl | hz'
    · exact Nat.eq_of_beq_eq_true h1
    · exact closedS_spec gens h2 z' hz'

theorem memS_single {x N : Nat} (hx : x < 920808) (hN : N < 920808) : memS (single x) N = decide (N = x) := by
  unfold memS single
  have r1 : (nat_lit 524288 : Nat) = 524288 := rfl
  have r3 : (nat_lit 3 : Nat) = 3 := rfl
  rw [nshl, nadd, nmul, r1, Nat.one_shiftLeft]
  change (2 ^ (x % 3 * 524288 + x / 3)).testBit (N % 3 * 524288 + N / 3) = _
  rw [Nat.testBit_two_pow]
  by_cases h : N = x
  · subst h
    simp
  · rw [decide_eq_false h, decide_eq_false]
    omega

@[expose] def cnt (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f n + f n

theorem cnt_add (f : Nat → Nat) (a : Nat) : ∀ b, cnt f (a + b) = cnt f a + cnt (fun x => f (a + x)) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, cnt, cnt, cnt_add f a b, Nat.add_assoc]

theorem cnt_congr {f g : Nat → Nat} : ∀ n, (∀ i < n, f i = g i) → cnt f n = cnt g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [cnt, cnt, cnt_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem cnt_zero_fun {f : Nat → Nat} : ∀ n, (∀ i < n, f i = 0) → cnt f n = 0
  | 0, _ => rfl
  | n + 1, h => by rw [cnt, cnt_zero_fun n (fun i hi => h i (by omega)), h n (by omega)]

theorem cnt_add_fun (f g : Nat → Nat) : ∀ n, cnt (fun i => f i + g i) n = cnt f n + cnt g n
  | 0 => rfl
  | n + 1 => by
    rw [cnt, cnt, cnt, cnt_add_fun f g n]
    omega

theorem cnt_mul (f : Nat → Nat) (k : Nat) : ∀ n, cnt f (k * n) = cnt (fun c => cnt (fun i => f (k * c + i)) k) n
  | 0 => by rw [Nat.mul_zero]; rfl
  | n + 1 => by
    rw [Nat.mul_succ, cnt_add, cnt_mul f k n, cnt]

theorem length_filter_range (p : Nat → Bool) : ∀ n,
    ((List.range n).filter p).length = cnt (fun i => if p i then 1 else 0) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p n, cnt]
    cases h : p n <;> simp [List.filter, h]

theorem pc64_eq (x : Nat) : pc64 x = cnt (fun i => if x.testBit i then 1 else 0) 64 := by
  have key : ∀ k, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight x i) (nat_lit 1))) k : Nat) =
      cnt (fun i => if x.testBit i then 1 else 0) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change Nat.add _ _ = _
      rw [ih, cnt, nadd]
      congr 1
      have e : Nat.land (Nat.shiftRight x k) 1 = (x >>> k) % 2 := Nat.and_one_is_mod _
      have hb : x.testBit k = decide ((x >>> k) % 2 = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
      rw [e, hb]
      rcases Nat.mod_two_eq_zero_or_one (x >>> k) with h | h <;> rw [h] <;> rfl
  exact key 64

theorem sumBelow_eq (m hi : Nat) (f : Nat → Nat) (h : m ≤ 64 * hi) : sumBelow m hi f = cnt f m := by
  have inner : ∀ h' n, (Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h' 6) l)) ih2) n : Nat) =
      cnt (fun l => if 64 * h' + l < m then f (64 * h' + l) else 0) n := by
    intro h' n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.add _ _ = _
      rw [ih, cnt, nadd, Nat.add_comm]
      congr 1
      have e : Nat.add (Nat.shiftLeft h' 6) n = 64 * h' + n := by
        rw [nadd, nshl, Nat.shiftLeft_eq]
        omega
      rw [e]
      by_cases hl : 64 * h' + n < m
      · rw [if_pos hl]
        change Bool.rec (motive := fun _ => Nat) 0 (f (64 * h' + n)) (Nat.blt (64 * h' + n) m) = _
        rw [Nat.blt_eq.mpr hl]
      · rw [if_neg hl]
        change Bool.rec (motive := fun _ => Nat) 0 (f (64 * h' + n)) (Nat.blt (64 * h' + n) m) = _
        rw [show Nat.blt (64 * h' + n) m = false from
          Bool.eq_false_iff.mpr fun e => hl (Nat.blt_eq.mp e)]
  have outer : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun h' ih => Nat.add (
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h' 6) l)) ih2) 64) ih) n : Nat) =
      cnt (fun i => if i < m then f i else 0) (64 * n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.add _ _ = _
      rw [ih, inner, Nat.mul_succ, cnt_add, nadd, Nat.add_comm]
  change (Nat.rec (motive := fun _ => Nat) 0 (fun h' ih => Nat.add (
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h' 6) l)) ih2) 64) ih) hi : Nat) = _
  rw [outer, show 64 * hi = m + (64 * hi - m) by omega, cnt_add,
    cnt_zero_fun (64 * hi - m) (fun i _ => by rw [if_neg (by omega)]), Nat.add_zero]
  exact cnt_congr m fun i hi => if_pos hi

theorem pcount_eq (v : Nat) : pcount v = cnt (fun q => if v.testBit q then 1 else 0) 1572864 := by
  unfold pcount
  rw [sumBelow_eq _ _ _ (by decide), show (1572864 : Nat) = 64 * 24576 from rfl, cnt_mul]
  refine cnt_congr _ fun c _ => ?_
  rw [pc64_eq]
  refine cnt_congr _ fun i hi => ?_
  have r : (nat_lit 18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
  rw [nland, nshr, nmul, r, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hi,
    Bool.and_true, Nat.testBit_shiftRight, Nat.mul_comm c 64]

theorem testBit_ptsS (q : Nat) :
    ptsS.testBit q = (decide (q < 1572864) && decide (q % 524288 < 306936)) := by
  have key : ∀ W, W ≤ 524288 → ∀ q, (mk3 (ones W) (ones W) (ones W)).testBit q =
      (decide (q < 1572864) && decide (q % 524288 < W)) := by
    intro W hW q
    have hs : Small (ones W) := by
      intro q hq
      rw [testBit_onesW, decide_eq_false (by omega)]
    rw [testBit_mk3 hs hs, testBit_onesW, testBit_onesW, testBit_onesW, Bool.eq_iff_iff, Bool.and_eq_true,
      decide_eq_true_eq, decide_eq_true_eq]
    split_ifs with h1 h2 <;> rw [decide_eq_true_eq] <;> constructor <;> intro h <;> omega
  exact key _ (by decide) q

theorem pcount_pts (S : Nat) :
    pcount (Nat.land S ptsS) = ((List.range 920808).filter (memS S)).length := by
  rw [pcount_eq, length_filter_range]
  have hb : ∀ q, (Nat.land S ptsS).testBit q =
      (S.testBit q && (decide (q < 1572864) && decide (q % 524288 < 306936))) := by
    intro q
    rw [nland, Nat.testBit_and, testBit_ptsS]
  rw [show (1572864 : Nat) = 524288 + (524288 + 524288) from rfl, cnt_add, cnt_add]
  have sheet : ∀ i < 3, cnt (fun x => if (Nat.land S ptsS).testBit (i * 524288 + x) then 1 else 0) 524288 =
      cnt (fun f => if S.testBit (i * 524288 + f) then 1 else 0) 306936 := by
    intro i hi
    rw [show (524288 : Nat) = 306936 + 217352 from rfl, cnt_add,
      cnt_zero_fun 217352 (fun x hx => by rw [hb, if_neg (by simp; omega)]), Nat.add_zero]
    refine cnt_congr _ fun f hf => ?_
    rw [hb, decide_eq_true (by omega), decide_eq_true (by omega), Bool.and_true, Bool.and_true]
  have e0 := sheet 0 (by decide)
  have e1 := sheet 1 (by decide)
  have e2 := sheet 2 (by decide)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul] at e0 e1
  have e1' : cnt (fun x => if (Nat.land S ptsS).testBit (524288 + x) then 1 else 0) 524288 =
      cnt (fun f => if S.testBit (524288 + f) then 1 else 0) 306936 := e1
  have e2' : cnt (fun x => if (Nat.land S ptsS).testBit (524288 + (524288 + x)) then 1 else 0) 524288 =
      cnt (fun f => if S.testBit (2 * 524288 + f) then 1 else 0) 306936 := by
    rw [← e2]
    refine cnt_congr _ fun x _ => ?_
    rw [show 524288 + (524288 + x) = 2 * 524288 + x by omega]
  rw [e0, e1', e2', show (920808 : Nat) = 3 * 306936 from rfl, cnt_mul]
  rw [← cnt_add_fun, ← cnt_add_fun]
  refine cnt_congr _ fun f hf => ?_
  have m0 : memS S (3 * f + 0) = S.testBit f := by
    unfold memS
    rw [show (3 * f + 0) % 3 * 524288 + (3 * f + 0) / 3 = f by omega]
  have m1 : memS S (3 * f + 1) = S.testBit (524288 + f) := by
    unfold memS
    rw [show (3 * f + 1) % 3 * 524288 + (3 * f + 1) / 3 = 524288 + f by omega]
  have m2 : memS S (3 * f + 2) = S.testBit (2 * 524288 + f) := by
    unfold memS
    rw [show (3 * f + 2) % 3 * 524288 + (3 * f + 2) / 3 = 2 * 524288 + f by omega]
  simp only [cnt, m0, m1, m2]
  omega

theorem eL_lt {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} (hz : LOK NW KA KB z) {N : Nat}
    (hN : N < 920808) : eL NW KA KB z N < 920808 := by
  cases z with
  | ofNat m =>
    rcases m with _ | n
    · rw [eL_zero NW KA KB hN]
      exact hN
    · exact (eL_pos_neg (n := n) hz.1 hz.2 hN).2.2.1
  | negSucc n => exact (eL_pos_neg (n := n) hz.1 hz.2 hN).1

theorem eW_lt {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} :
    ∀ (w : List Int), (∀ z ∈ w, LOK NW KA KB z) → ∀ {N : Nat}, N < 920808 → eW NW KA KB w N < 920808
  | [], _, _, hN => hN
  | z :: w, h, N, hN => by
    rw [eW_cons]
    exact eL_lt (h z List.mem_cons_self) (eW_lt w (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) hN)

theorem imgW_cons (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (w : List Int) (s : Nat) :
    imgW NW KA KB (z :: w) s = imgS NW KA KB z (imgW NW KA KB w s) := by
  change strictN (imgW NW KA KB w s) (imgS NW KA KB z) = _
  exact strictN_eq' _ _

theorem memS_imgW {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} :
    ∀ (w : List Int), (∀ z ∈ w, LOK NW KA KB z) → ∀ (s : Nat) {M : Nat}, M < 920808 →
      memS (imgW NW KA KB w s) (eW NW KA KB w M) = memS s M
  | [], _, _, _, _ => rfl
  | z :: w, h, s, M, hM => by
    have h' : ∀ z ∈ w, LOK NW KA KB z := fun z' hz' => h z' (List.mem_cons_of_mem z hz')
    rw [imgW_cons, eW_cons, memS_imgS (h z List.mem_cons_self) _ (eW_lt w h' hM), memS_imgW w h' s hM]

theorem ptOK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int} {x y : Nat}
    (hw : ∀ z ∈ w, LOK NW KA KB z) (hx : x < 920808) (hy : y < 920808)
    (h : ptOK NW KA KB w x y = true) : eW NW KA KB w x = y := by
  have e := Nat.eq_of_beq_eq_true h
  have h1 := memS_imgW w hw (single x) hx
  rw [e, memS_single hy (eW_lt w hw hx), memS_single hx hx] at h1
  simpa using h1

theorem orb_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int} {x n m : Nat}
    (hx : x < 920808) (hg : ∀ z ∈ gens, LOK NW KA KB z) (h : orbOK NW KA KB gens x n m = true) :
    memS (closeS NW KA KB gens n (single x)) x = true ∧
      (∀ N < 920808, memS (closeS NW KA KB gens n (single x)) N = true →
        ∀ z ∈ gens, memS (closeS NW KA KB gens n (single x)) (eL NW KA KB z N) = true) ∧
      (∀ P : Nat → Prop, P x → (∀ N, P N → ∀ z ∈ gens, P (eL NW KA KB z N)) →
        ∀ N < 920808, memS (closeS NW KA KB gens n (single x)) N = true → P N) ∧
      ((List.range 920808).filter (memS (closeS NW KA KB gens n (single x)))).length = m := by
  unfold orbOK at h
  rw [letB_eq'] at h
  obtain ⟨h1, h2⟩ := andB_true h
  set S := closeS NW KA KB gens n (single x)
  refine ⟨memS_closeS_of NW KA KB gens n _ x (by rw [memS_single hx hx]; simp), ?_, ?_, ?_⟩
  · intro N hN hS z hz
    rw [← closedS_spec gens h1 z hz, memS_imgS (hg z hz) S hN]
    exact hS
  · intro P hPx hP
    refine closeS_min hg P hP n (single x) fun N hN hs => ?_
    rw [memS_single hx hN] at hs
    rw [of_decide_eq_true hs]
    exact hPx
  · rw [← pcount_pts]
    exact Nat.eq_of_beq_eq_true h2

end CFSG.KS.RouteP

end
