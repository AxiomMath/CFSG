
module

public import CFSG.Certificates.Kernel.SporSch.SetReplaySound
public import CFSG.Certificates.Kernel.SporSch.HashSearch
public import CFSG.Certificates.Kernel.SporSch.SetTreeSound
public import CFSG.Certificates.Kernel.Spor.NKeyBfs
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.SporSch.SRP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.KeySearch
open CFSG.KS.SporSch.SetTree CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def StepB (key : Nat → Nat) (img pos : Nat → Nat → Nat) (P L : Nat → Nat)
    (c B h l cur v : Nat) : Prop :=
  (h < cur ∧ pos h l < cur ∧ v = cur ∧ img h l = key (pos h l)) ∨
    (h < cur ∧ pos h l = cur ∧ v = cur + 1 ∧ img h l = key cur ∧ P cur = h ∧ L cur = l) ∨
    (cur ≤ h ∧ cur = c ∧ v = cur) ∨ (B ≤ cur ∧ v = cur)

theorem runC_tree {f : Nat → Nat → Nat → Nat} {k c M H fl B : Nat} {C : Nat → Nat}
    {key : Nat → Nat} {img pos : Nat → Nat → Nat} {P L : Nat → Nat}
    (hc0 : 0 < c) (hcM : c ≤ M * H) (hfl : c < fl) (hC0 : C 0 = 1) (hCM : C M = c)
    (hrun : ∀ t < M, NKey.runC f k H (t * H) (C t) = C (t + 1))
    (hup : ∀ h l cur, l < k → fl ≤ cur → fl ≤ f h l cur)
    (hstep : ∀ h l cur, l < k → cur < fl → f h l cur < fl →
      StepB key img pos P L c B h l cur (f h l cur)) :
    (∀ i, 0 < i → i < c → P i < i ∧ L i < k ∧ img (P i) (L i) = key i) ∧
      (c < B → ∀ h < c, ∀ j < k, pos h j < c ∧ img h j = key (pos h j)) ∧
      (0 < k → c ≤ B → ∀ h < c, ∃ cur, h < cur ∧ cur < fl ∧ f h 0 cur < fl) := by
  have hs0 : NKey.curE f k 1 0 = 1 := rfl
  have hsS : ∀ e, NKey.curE f k 1 (e + 1) = f (e / k) (e % k) (NKey.curE f k 1 e) :=
    NKey.curE_succ f k 1
  have hslice : ∀ t ≤ M, NKey.curE f k 1 (k * (t * H)) = C t := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Nat.zero_mul, Nat.mul_zero, hC0]
      rfl
    | succ t ih =>
      intro ht
      rw [← hrun t (by omega), ← ih (by omega), NKey.runC_curE]
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
  have hE : NKey.curE f k 1 (k * (M * H)) = c := by rw [hslice M (Nat.le_refl M), hCM]
  clear hslice hrun
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rw [Nat.zero_mul] at hE
    have hc1 : c = 1 := by rw [← hE]; rfl
    subst hc1
    exact ⟨fun i hi0 hic => by omega, fun _ h hh j hj => by omega, fun hk => absurd hk (lt_irrefl 0)⟩
  have hEc : k * c ≤ k * (M * H) := Nat.mul_le_mul_left k hcM
  generalize k * (M * H) = E at hE hEc
  generalize NKey.curE f k 1 = s at hs0 hsS hE
  have hmod : ∀ e, e % k < k := fun e => Nat.mod_lt _ hk
  have hnf : ∀ e ≤ E, s e < fl := by
    intro e he
    refine Nat.lt_of_not_le fun hse => ?_
    have : ∀ d, e + d ≤ E → fl ≤ s (e + d) := by
      intro d
      induction d with
      | zero => intro _; exact hse
      | succ d ih =>
        intro hd
        rw [← Nat.add_assoc, hsS]
        exact hup _ _ _ (hmod _) (ih (by omega))
    have := this (E - e) (by omega)
    rw [Nat.add_sub_cancel' he, hE] at this
    omega
  have hok : ∀ e < E, StepB key img pos P L c B (e / k) (e % k) (s e) (s (e + 1)) := by
    intro e he
    rw [hsS]
    exact hstep _ _ _ (hmod e) (hnf e (by omega)) (by rw [← hsS]; exact hnf (e + 1) (by omega))
  have hstep1 : ∀ e < E, s e ≤ s (e + 1) ∧ s (e + 1) ≤ s e + 1 := by
    intro e he
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> rw [h3] <;> omega
  have hmono : ∀ e e', e ≤ e' → e' ≤ E → s e ≤ s e' := fun e e' h h' =>
    NKey.mono_le (fun e he => (hstep1 e he).1) h h'
  have hle : ∀ e ≤ E, s e ≤ c := fun e he => hE ▸ hmono e E he (Nat.le_refl E)
  refine ⟨fun i hi0 hic => ?_, fun hcB h hh j hj => ?_, fun _ hcB h hh => ?_⟩
  rotate_left 2
  · have hd := NKey.divmod_eq (k := k) h hk
    rw [Nat.add_zero] at hd
    have he : k * h < E := by
      have : k * (h + 1) ≤ k * c := Nat.mul_le_mul_left k hh
      rw [Nat.mul_succ] at this
      omega
    have hO := hok _ he
    rw [hd.1, hd.2] at hO
    have hn1 := hnf (k * h + 1) he
    rw [hsS, hd.1, hd.2] at hn1
    refine ⟨s (k * h), ?_, hnf _ (Nat.le_of_lt he), hn1⟩
    have hsc := hle (k * h) (Nat.le_of_lt he)
    rcases hO with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, a2, -⟩ | ⟨a1, -⟩
    · exact a1
    · exact a1
    · omega
    · omega
  · obtain ⟨e, he, h1, h2⟩ := NKey.ivt (s := s) (i := i) E hstep1 (by rw [hs0]; omega)
      (by rw [hE]; exact hic)
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨hh, -, -, a4, a5, a6⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩
    · omega
    · rw [h1] at hh a4 a5 a6
      rw [a5, a6]
      exact ⟨hh, hmod e, a4⟩
    · omega
    · omega
  · have hd := NKey.divmod_eq h hj
    have he : k * h + j < E := by
      have : k * (h + 1) ≤ k * c := Nat.mul_le_mul_left k hh
      rw [Nat.mul_succ] at this
      omega
    have hsc := hle (k * h + j) (Nat.le_of_lt he)
    have hsc1 := hle (k * h + j + 1) he
    have hO := hok _ he
    rw [hd.1, hd.2] at hO
    rcases hO with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, -⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
    · exact ⟨by omega, a4⟩
    · exact ⟨by omega, by rw [a2]; exact a4⟩
    · omega
    · omega

@[expose] noncomputable def posR (W : Nat → Nat) (h l : Nat) : Nat :=
  fld(W h, Nat.mul (nat_lit 20) l, nat_lit 1048575)

theorem nIf_v (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_v (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem stepRKF_eq (w s : Nat) (X W KT : Nat → Nat) (c bound h l cur t : Nat) :
    stepRKF w s X W KT c bound h l cur t =
      if cur = bound then cur else if h < cur then
        (if posR W h l < cur ∧ KT (posR W h l) = t then cur
        else if posR W h l = cur ∧ KT (posR W h l) = t ∧
          parX w s (X (posR W h l)) = h ∧ labX w s (X (posR W h l)) = l then cur + 1 else failC)
      else if cur = c then cur else failC := by
  unfold stepRKF posR
  simp only [strictN_eq', strictB_eq', nIf_v, bAnd_v, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq]

theorem stepRKF_up {w s c bound h l cur t : Nat} {X W KT : Nat → Nat} (hc : failC ≤ cur) :
    failC ≤ stepRKF w s X W KT c bound h l cur t := by
  rw [stepRKF_eq]
  split_ifs <;> omega

theorem stepRKF_step {w s c bound h l cur t : Nat} {X W KT : Nat → Nat} {img : Nat → Nat → Nat}
    (ht : img h l = t) (hf : stepRKF w s X W KT c bound h l cur t < failC) :
    StepB KT img (posR W)
      (fun j => parX w s (X j)) (fun j => labX w s (X j)) c bound h l cur
      (stepRKF w s X W KT c bound h l cur t) := by
  subst ht
  generalize hv : stepRKF w s X W KT c bound h l cur (img h l) = v at hf ⊢
  rw [stepRKF_eq] at hv
  unfold StepB
  split_ifs at hv with h1 h2 h3 h4 h5
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, hv.symm⟩))
  · exact Or.inl ⟨h2, h3.1, hv.symm, h3.2.symm⟩
  · obtain ⟨a, b, c', d⟩ := h4
    refine Or.inr (Or.inl ⟨h2, a, hv.symm, ?_, ?_, ?_⟩)
    · rw [← a]
      exact b.symm
    · rw [← a]
      exact c'
    · rw [← a]
      exact d
  · omega
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h5, hv.symm⟩))
  · omega

theorem stepFK_eq (w s L ML : Nat) (X W KT : Nat → Nat) (kg c bound h F k cur : Nat) :
    stepFK w s L ML X W KT kg c bound h F k cur =
      if k = 0 ∧ h < cur then
        (if Nat.shiftRight F (Nat.mul kg L) = KT h then
          stepRKF w s X W KT c bound h k cur fld(F, Nat.mul k L, ML) else failC)
      else stepRKF w s X W KT c bound h k cur fld(F, Nat.mul k L, ML) := by
  unfold stepFK
  simp only [nIf_v, bAnd_v, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq]

theorem stepFK_up {w s L ML kg c bound h F k cur : Nat} {X W KT : Nat → Nat}
    (hc : failC ≤ cur) : failC ≤ stepFK w s L ML X W KT kg c bound h F k cur := by
  rw [stepFK_eq]
  split_ifs
  · exact stepRKF_up hc
  · exact le_refl _
  · exact stepRKF_up hc

theorem stepFK_step {w s L ML kg c bound h F k cur : Nat} {X W KT : Nat → Nat}
    {img : Nat → Nat → Nat} (hf : stepFK w s L ML X W KT kg c bound h F k cur < failC)
    (ht : img h k = fld(F, Nat.mul k L, ML)) :
    StepB KT img (posR W) (fun j => parX w s (X j)) (fun j => labX w s (X j)) c bound h k cur
      (stepFK w s L ML X W KT kg c bound h F k cur) ∧
      (k = 0 → h < cur → Nat.shiftRight F (Nat.mul kg L) = KT h) := by
  rw [stepFK_eq] at hf ⊢
  split_ifs at hf ⊢ with h1 h2
  · exact ⟨stepRKF_step ht hf, fun _ _ => h2⟩
  · exact absurd hf (lt_irrefl _)
  · exact ⟨stepRKF_step ht hf, fun a b => absurd ⟨a, b⟩ h1⟩

theorem runFromF_eq (n w s : Nat) (G X W KT : Nat → Nat) (kg c bound : Nat) :
    ∀ len h cur, runFromF n w s G X W KT kg c bound len h cur =
      NKey.runC (fun h k cur => stepFK w s (Nat.add 64 n) (mask (Nat.add 64 n)) X W KT kg c bound h
        (fusedK n w s kg (Nat.add 64 n) G (X h)) k cur) kg len h cur := by
  intro len
  induction len with
  | zero => intro h cur; rfl
  | succ len ih =>
    intro h cur
    rw [NKey.runC_succ, ← ih]
    change strictN (headRF n w s G X W KT kg c bound h cur) (fun c' =>
      strictN (Nat.succ h) (fun h' => runFromF n w s G X W KT kg c bound len h' c')) = _
    unfold headRF
    simp only [strictN_eq', Nat.succ_eq_add_one] <;> rfl

theorem one_shl (k : Nat) : Nat.shiftLeft (nat_lit 1) k = 2 ^ k := by
  change 1 <<< k = _
  rw [Nat.one_shiftLeft]

theorem lorT_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl

theorem xorT_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

theorem salt_lt (t : Nat) :
    Nat.land (Nat.mul (Nat.succ t) (nat_lit 11400714819323198485)) (nat_lit 18446744073709551615) <
      2 ^ 64 := by
  change _ &&& 18446744073709551615 < 2 ^ 64
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem ptBitsT_bit (t b : Nat) : (ptBitsT t).testBit (64 + b) = decide (b = t) := by
  unfold ptBitsT
  rw [lorT_eq, one_shl, Nat.testBit_or, Nat.testBit_two_pow, tag_bit (salt_lt t), Bool.or_false]
  exact decide_eq_decide.2 ⟨fun e => by change 64 + t = 64 + b at e; omega,
    fun e => by change 64 + t = 64 + b; omega⟩

theorem ptBitsT_lt {t n : Nat} (h : t < n) : ptBitsT t < 2 ^ (64 + n) := by
  unfold ptBitsT
  rw [lorT_eq, one_shl]
  refine Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (by change 64 + t < 64 + n; omega))
    (lt_of_lt_of_le (salt_lt t) (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem testBit_foldrX (g : Nat → Nat) (b : Nat) :
    ∀ (l : List Nat) (a : Nat), (l.map g).Nodup → a.testBit (64 + b) = false →
      (l.foldr (fun q acc => Nat.xor acc (ptBitsT (g q))) a).testBit (64 + b) =
        decide (b ∈ l.map g)
  | [], a, _, ha => by simpa using ha
  | q :: l, a, hnd, ha => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldr_cons, xorT_eq, Nat.testBit_xor, testBit_foldrX g b l a hnd.2 ha, ptBitsT_bit,
      List.map_cons]
    by_cases h : b = g q
    · subst h
      simp [hnd.1]
    · simp [h]

theorem zero_tb (b : Nat) : Nat.testBit (nat_lit 0) (64 + b) = false := Nat.zero_testBit _

theorem keyK1_bit {w s x : Nat} (hnd : (ptsOf w s x).Nodup) (b : Nat) :
    (keyK1 w s x).testBit (64 + b) = decide (b ∈ ptsOf w s x) := by
  unfold keyK1
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  exact testBit_foldrX (pg w (mask w) x) b _ _ hnd (zero_tb b)

theorem imgK1_bit {w s G x : Nat} (hnd : ((ptsOf w s x).map (pg w (mask w) G)).Nodup) (b : Nat) :
    (imgK1 w s G x).testBit (64 + b) = decide (b ∈ (ptsOf w s x).map (pg w (mask w) G)) := by
  unfold imgK1
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  unfold ptsOf at hnd ⊢
  rw [List.map_map] at hnd ⊢
  exact testBit_foldrX (fun q => pg w (mask w) G (pg w (mask w) x q)) b _ _ hnd (zero_tb b)

theorem foldr_congr2 {f g : Nat → Nat → Nat} :
    ∀ (l : List Nat) {a b : Nat}, (∀ q ∈ l, ∀ acc, f q acc = g q acc) → a = b →
      l.foldr f a = l.foldr g b
  | [], _, _, _, e => e
  | q :: l, a, b, h, e => by
    rw [List.foldr_cons, List.foldr_cons,
      foldr_congr2 l (fun r hr => h r (List.mem_cons_of_mem q hr)) e, h q List.mem_cons_self]

theorem keyK1_congr {w s x y : Nat} (h : ptsOf w s x = ptsOf w s y) :
    keyK1 w s x = keyK1 w s y := by
  have hq : ∀ q < s, pg w (mask w) x q = pg w (mask w) y q := by
    intro q hq
    have := congrArg (fun l => l[q]?) h
    simpa [ptsOf, hq] using this
  unfold keyK1
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  refine foldr_congr2 _ (fun q hq' acc => ?_) rfl
  rw [hq q (List.mem_range.1 hq')]

theorem permA_of_permOK {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PermA n (unpack n w P) := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_⟩
  · rw [CFSG.KC.Misc.PairCount.unpack_get hx]
    exact (h3 x hx).1
  · rw [CFSG.KC.Misc.PairCount.unpack_get hx, CFSG.KC.Misc.PairCount.unpack_get hy] at e
    rw [← (h3 x hx).2, ← (h3 y hy).2, e]

theorem pts_of_key1 {n w s kg : Nat} {G : Nat → Nat} {gens : Array (Array Nat)}
    (hg : ∀ k < kg, gens[k]! = unpack n w (G k)) (hperm : ∀ k < kg, PermA n gens[k]!) {k x y : Nat}
    (hk : k < kg) (hx : Good n (ptsOf w s x)) (hy : Good n (ptsOf w s y))
    (he : imgK1 w s (G k) y = keyK1 w s x) :
    ptsOf w s x = imgSorted gens[k]! (ptsOf w s y) := by
  refine eq_of_mem_iff hx (imgSorted_good (hperm k hk) hy) fun q => ?_
  have hmap : (ptsOf w s y).map (pg w (mask w) (G k)) = (ptsOf w s y).map fun r => (gens[k]!)[r]! :=
    List.map_congr_left fun r hr => by
      rw [hg k hk, CFSG.KC.Misc.PairCount.unpack_get (hy.2 r hr)]
  have hndy : ((ptsOf w s y).map (pg w (mask w) (G k))).Nodup := by
    rw [hmap]
    exact List.Nodup.map_on (fun a ha b hb e => (hperm k hk).2 a (hy.2 a ha) b (hy.2 b hb) e)
      (hy.1.imp fun h => Nat.ne_of_lt h)
  have hb := keyK1_bit (hx.1.imp fun h => Nat.ne_of_lt h) q
  rw [← he, imgK1_bit hndy] at hb
  have e1 : q ∈ ptsOf w s x ↔ q ∈ (ptsOf w s y).map (pg w (mask w) (G k)) :=
    (decide_eq_decide.1 hb).symm
  rw [e1, hmap, imgSorted, (List.mergeSort_perm _ _).mem_iff]

theorem foldr_fail {ok : Nat → Bool} {f : Nat → Nat} {m : Nat}
    (hf : ∀ q, ok q = true → f q < 2 ^ m) :
    ∀ (l : List Nat) (a : Nat),
      l.foldr (fun q acc => if ok q = true then Nat.xor acc (f q) else Nat.lor acc (2 ^ m)) a <
        2 ^ m →
      (∀ q ∈ l, ok q = true) ∧
        l.foldr (fun q acc => if ok q = true then Nat.xor acc (f q) else Nat.lor acc (2 ^ m)) a =
          l.foldr (fun q acc => Nat.xor acc (f q)) a
  | [], _, _ => ⟨by simp, rfl⟩
  | q :: l, a, h => by
    rw [List.foldr_cons] at h
    by_cases hq : ok q = true
    · rw [if_pos hq, xorT_eq] at h
      have hr := Nat.xor_lt_two_pow h (hf q hq)
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hr
      obtain ⟨h1, h2⟩ := foldr_fail hf l a hr
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact hq
        · exact h1 r hr
      · rw [List.foldr_cons, List.foldr_cons, if_pos hq, h2]
    · rw [if_neg hq, lorT_eq] at h
      exact absurd (lt_of_le_of_lt Nat.right_le_or h) (lt_irrefl _)

theorem good_of_pts {n w s x : Nat}
    (hq : ∀ q < s, pg w (mask w) x q < n ∧ (0 < q → pg w (mask w) x (q - 1) < pg w (mask w) x q)) :
    Good n (ptsOf w s x) := by
  have mono : ∀ a b, a < b → b < s → pg w (mask w) x a < pg w (mask w) x b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := (hq (b + 1) hb).2 (by omega)
      rw [Nat.add_sub_cancel] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact lt_trans (ih h' (by omega)) hs
      · rw [h']
        exact hs
  refine ⟨?_, fun p hp => ?_⟩
  · unfold ptsOf
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range).imp_of_mem fun {a b} ha hb hab =>
      mono a b hab (List.mem_range.1 hb)
  · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hp
    exact (hq q (List.mem_range.1 hq')).1

theorem packF_spec {L b : Nat} {v : Nat → Nat} : ∀ (kg base : Nat), (∀ k < kg, v k < 2 ^ L) →
    (List.range kg).foldr (fun k a => Nat.lor (Nat.shiftLeft a L) (v k)) base >>> (kg * L) = base ∧
      (∀ k < kg, ((List.range kg).foldr (fun k a => Nat.lor (Nat.shiftLeft a L) (v k)) base >>>
        (k * L)) % 2 ^ L = v k) ∧
      (base < 2 ^ b →
        (List.range kg).foldr (fun k a => Nat.lor (Nat.shiftLeft a L) (v k)) base < 2 ^ (kg * L + b))
  | 0, base, _ => ⟨by simp, fun k hk => absurd hk (Nat.not_lt_zero k), fun hb => by simpa using hb⟩
  | kg + 1, base, hv => by
    have hvk := hv kg (Nat.lt_succ_self kg)
    have e1 : Nat.lor (Nat.shiftLeft base L) (v kg) = base * 2 ^ L + v kg := by
      change base <<< L ||| v kg = _
      rw [← Nat.shiftLeft_add_eq_or_of_lt hvk, Nat.shiftLeft_eq]
    simp only [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    rw [e1]
    obtain ⟨i1, i2, i3⟩ := packF_spec (L := L) (b := L + b) (v := v) kg (base * 2 ^ L + v kg)
      (fun k hk => hv k (by omega))
    have hd : (base * 2 ^ L + v kg) / 2 ^ L = base := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos L), Nat.div_eq_of_lt hvk,
        Nat.zero_add]
    have hm : (base * 2 ^ L + v kg) % 2 ^ L = v kg := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvk]
    refine ⟨?_, fun k hk => ?_, fun hb => ?_⟩
    · rw [Nat.add_one_mul, Nat.shiftRight_add, i1, Nat.shiftRight_eq_div_pow, hd]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact i2 k hk
      · rw [hk, i1, hm]
    · have hb' : base * 2 ^ L + v kg < 2 ^ (L + b) := by
        rw [Nat.pow_add]
        calc base * 2 ^ L + v kg < base * 2 ^ L + 2 ^ L := Nat.add_lt_add_left hvk _
          _ = (base + 1) * 2 ^ L := by ring
          _ ≤ 2 ^ b * 2 ^ L := Nat.mul_le_mul_right _ hb
          _ = 2 ^ L * 2 ^ b := Nat.mul_comm _ _
      have e2 : kg * L + (L + b) = (kg + 1) * L + b := by ring
      have := i3 hb'
      rwa [e2] at this

theorem foldr_xor_proj {π : Nat → Nat} (h0 : π 0 = 0) (hx : ∀ a b, π (a ^^^ b) = π a ^^^ π b)
    (g : Nat → Nat) : ∀ l : List Nat,
      π (l.foldr (fun q acc => Nat.xor acc (g q)) 0) = l.foldr (fun q acc => Nat.xor acc (π (g q))) 0
  | [] => h0
  | q :: l => by
    simp only [List.foldr_cons]
    rw [← foldr_xor_proj h0 hx g l]
    exact hx _ _

theorem shrF_xor (a b o : Nat) : (a ^^^ b) >>> o = (a >>> o) ^^^ (b >>> o) :=
  Nat.eq_of_testBit_eq fun i => by simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

theorem fldF_xor (L o a b : Nat) :
    ((a ^^^ b) >>> o) % 2 ^ L = ((a >>> o) % 2 ^ L) ^^^ ((b >>> o) % 2 ^ L) :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor]
    by_cases hi : i < L <;> simp [hi]

theorem fldF_eq (F o L : Nat) : (F >>> o) % 2 ^ L = Nat.land (Nat.shiftRight F o) (mask L) := by
  rw [CFSG.KC.Pack.mask_eq]
  change _ = (F >>> o) &&& (2 ^ L - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem ltF_of_shr {a o b : Nat} (h : a >>> o < 2 ^ b) : a < 2 ^ (o + b) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos o)] at h
  rwa [Nat.pow_add, Nat.mul_comm]

theorem fusedK_spec {n w s kg : Nat} {G : Nat → Nat} {x : Nat}
    (hG : ∀ k < kg, ∀ t < n, pg w (mask w) (G k) t < n)
    (h : fusedK n w s kg (64 + n) G x >>> (kg * (64 + n)) < 2 ^ (64 + n)) :
    Good n (ptsOf w s x) ∧ fusedK n w s kg (64 + n) G x >>> (kg * (64 + n)) = keyK1 w s x ∧
      ∀ k < kg, (fusedK n w s kg (64 + n) G x >>> (k * (64 + n))) % 2 ^ (64 + n) =
        imgK1 w s (G k) x := by
  have hX := ltF_of_shr h
  unfold fusedK at hX ⊢
  unfold keyK1 imgK1
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq, nIf_v, one_shl] at hX ⊢
  have hf : ∀ q, Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool)
        (Nat.blt (pg w (mask w) x (Nat.sub q (nat_lit 1))) (pg w (mask w) x q)) true
        (Nat.beq q (nat_lit 0)))
      (Nat.blt (pg w (mask w) x q) n) = true →
      (List.range kg).foldr (fun k a => Nat.lor (Nat.shiftLeft a (64 + n))
        (ptBitsT (pg w (mask w) (G k) (pg w (mask w) x q)))) (ptBitsT (pg w (mask w) x q)) <
        2 ^ (Nat.add (Nat.mul kg (64 + n)) (Nat.add (nat_lit 64) n)) := fun q hq => by
    have ht : pg w (mask w) x q < n := by
      have h1 := ((bAnd_iff _ _).1 hq).1
      rwa [Nat.blt_eq] at h1
    exact (packF_spec (L := 64 + n) (b := 64 + n)
      (v := fun k => ptBitsT (pg w (mask w) (G k) (pg w (mask w) x q))) kg _
      (fun k hk => ptBitsT_lt (hG k hk _ ht))).2.2 (ptBitsT_lt ht)
  obtain ⟨hok, heq⟩ := foldr_fail hf _ _ hX
  have hpt : ∀ q ∈ List.range s, pg w (mask w) x q < n := fun q hq => by
    have h1 := ((bAnd_iff _ _).1 (hok q hq)).1
    rwa [Nat.blt_eq] at h1
  rw [heq]
  refine ⟨good_of_pts fun q hq => ?_, ?_, fun k hk => ?_⟩
  rotate_left
  · refine (foldr_xor_proj (π := fun a => a >>> (kg * (64 + n))) (Nat.zero_shiftRight _)
      (fun a b => shrF_xor a b _) _ _).trans (foldr_congr2 _ (fun q hq acc => ?_) rfl)
    exact congrArg (Nat.xor acc) (packF_spec (L := 64 + n) (b := 64 + n)
      (v := fun k => ptBitsT (pg w (mask w) (G k) (pg w (mask w) x q))) kg _
      (fun k hk => ptBitsT_lt (hG k hk _ (hpt q hq)))).1
  · refine (foldr_xor_proj (π := fun a => (a >>> (k * (64 + n))) % 2 ^ (64 + n)) (by simp)
      (fun a b => fldF_xor _ _ a b) _ _).trans (foldr_congr2 _ (fun q hq acc => ?_) rfl)
    exact congrArg (Nat.xor acc) ((packF_spec (L := 64 + n) (b := 64 + n)
      (v := fun k => ptBitsT (pg w (mask w) (G k) (pg w (mask w) x q))) kg _
      (fun k hk => ptBitsT_lt (hG k hk _ (hpt q hq)))).2.1 k hk)
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (hok q (List.mem_range.2 hq))
  refine ⟨by rwa [Nat.blt_eq] at a, fun h0 => ?_⟩
  have hb : Nat.beq q 0 = false := Bool.eq_false_iff.2 fun e => by
    have := Nat.eq_of_beq_eq_true e
    omega
  rw [hb] at b
  change Nat.blt _ _ = true at b
  rwa [Nat.blt_eq] at b

theorem rowGet_lt {T : Nat → Nat} {rw m : Nat} (e : rw = m) (i : Nat) : rowGet T rw i < 2 ^ m := by
  subst e
  unfold rowGet
  rw [CFSG.KC.Pack.mask_eq]
  change (T (Nat.shiftRight i 6) >>> (rw * (i &&& 63))) &&& (2 ^ rw - 1) < 2 ^ rw
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos rw)


theorem sortAtKT_spec {c i : Nat} {KT SO SOI : Nat → Nat} (hi : i < c)
    (h : sortAtKT KT SO SOI c i = true) :
    SO i < c ∧ (i + 1 < c → KT (SO i) < KT (SO (i + 1))) := by
  unfold sortAtKT at h
  have hb : Nat.blt i c = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  change sortKT KT SO SOI c i = true at h
  unfold sortKT at h
  rw [strictB_eq'] at h
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, b⟩ := (bAnd_iff _ _).1 b
  refine ⟨by rwa [Nat.blt_eq] at a, fun hi1 => ?_⟩
  have hb1 : Nat.blt (Nat.succ i) c = true := by rwa [Nat.blt_eq]
  rw [hb1] at b
  change Nat.blt _ _ = true at b
  rwa [Nat.blt_eq] at b

theorem replay_facts {n w s kg c bound nS H nB B R : Nat} {G GI X W KT SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W KT SO SOI C start) :
    0 < c ∧ c ≤ bound ∧ (∀ k < gens.size, PermA n gens[k]!) ∧
      (∀ i < c, Good n (ptsOf w s (X i))) ∧ ptsOf w s (X 0) = start ∧
      (∀ i, 0 < i → i < c → parX w s (X i) < i ∧ labX w s (X i) < gens.size ∧
        ptsOf w s (X i) = imgSorted gens[labX w s (X i)]! (ptsOf w s (X (parX w s (X i))))) ∧
      (∀ a < c, ∀ b < c, ptsOf w s (X a) = ptsOf w s (X b) → a = b) ∧
      (c < bound → ∀ i < c, ∀ k < gens.size, ∃ j < c,
        imgSorted gens[k]! (ptsOf w s (X i)) = ptsOf w s (X j)) := by
  obtain ⟨hgs, hgu⟩ := hg
  obtain ⟨-, -, -, hc0, hcb, hcS, hcB, hc20, -, hperm, hst, hKT, hkg, hsrt, hC0, hCM, hrun⟩ := h
  have hpA : ∀ k < kg, PermA n gens[k]! := fun k hk => by
    rw [hgu k hk]
    exact permA_of_permOK (hperm k hk)
  have hG : ∀ k < kg, ∀ t < n, pg w (mask w) (G k) t < n := fun k hk t ht =>
    ((CFSG.KS.Raw.Orb.permOK_facts (hperm k hk)).2.2 t ht).1
  have hrun' : ∀ t < nS * R, NKey.runC (fun h k cur => stepFK w s (Nat.add 64 n)
      (mask (Nat.add 64 n)) X W KT kg c bound h (fusedK n w s kg (Nat.add 64 n) G (X h)) k cur) kg H
      (t * H) (C t) = C (t + 1) := fun t ht =>
    (runFromF_eq n w s G X W KT kg c bound H (t * H) (C t)).symm.trans
      (NKey.slices_of_groups hrun t ht)
  have hfl : c < failC := by
    have e : failC = 1099511627776 := rfl
    rw [e]
    omega
  obtain ⟨htree, hclose, hchk⟩ := runC_tree (B := bound)
    (img := fun h l => Nat.land (Nat.shiftRight (fusedK n w s kg (Nat.add 64 n) G (X h))
      (Nat.mul l (Nat.add 64 n))) (mask (Nat.add 64 n)))
    hc0 hcS hfl hC0 hCM hrun'
    (fun h l cur _ hc => stepFK_up hc) (fun h l cur _ _ hf => (stepFK_step hf rfl).1)
  have helt' : ∀ i < c, Good n (ptsOf w s (X i)) ∧ KT i = keyK1 w s (X i) ∧
      ∀ l < kg, Nat.land (Nat.shiftRight (fusedK n w s kg (Nat.add 64 n) G (X i))
        (Nat.mul l (Nat.add 64 n))) (mask (Nat.add 64 n)) = imgK1 w s (G l) (X i) := by
    intro i hi
    obtain ⟨cur, h1, -, h3⟩ := hchk hkg hcb i hi
    have e := (stepFK_step (img := fun h l => Nat.land (Nat.shiftRight
      (fusedK n w s kg (Nat.add 64 n) G (X h)) (Nat.mul l (Nat.add 64 n))) (mask (Nat.add 64 n)))
      h3 rfl).2 rfl h1
    obtain ⟨g1, g2, g3⟩ := fusedK_spec (x := X i) hG (lt_of_eq_of_lt e (hKT i))
    exact ⟨g1, e.symm.trans g2, fun l hl =>
      (fldF_eq (fusedK n w s kg (64 + n) G (X i)) (l * (64 + n)) (64 + n)).symm.trans (g3 l hl)⟩
  have hgood : ∀ i < c, Good n (ptsOf w s (X i)) := fun i hi => (helt' i hi).1
  have hsrt' := fun i hi => sortAtKT_spec hi (NKey.all_of_blocks hcB hsrt i hi)
  have hinjK := CFSG.KC.Co2InvS.sorted_inj (f := KT)
    (fun i hi => (hsrt' i hi).1) (fun i hi => (hsrt' i (by omega)).2 hi)
  refine ⟨hc0, hcb, fun k hk => hpA k (hgs ▸ hk), hgood, startK_spec hst, fun i hi0 hic => ?_,
    fun a ha b hb e => hinjK a ha b hb (by rw [(helt' a ha).2.1, (helt' b hb).2.1, keyK1_congr e]),
    fun hcb' i hi k hk => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := htree i hi0 hic
    exact ⟨a1, hgs ▸ a2, pts_of_key1 hgu hpA a2 (hgood i hic) (hgood _ (by omega))
      (((helt' _ (by omega)).2.2 _ a2).symm.trans (a3.trans (helt' i hic).2.1))⟩
  · rw [hgs] at hk
    obtain ⟨a1, a2⟩ := hclose hcb' i hi k hk
    exact ⟨_, a1, (pts_of_key1 hgu hpA hk (hgood _ a1) (hgood i hi)
      (((helt' i hi).2.2 k hk).symm.trans (a2.trans (helt' _ a1).2.1))).symm⟩

theorem assemble {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound c : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {hd : Nat} {T : Nat → List Nat} {P L : Nat → Nat}
    (h0 : 0 < S.size) (hbd : S.size ≤ bound)
    (hz : S[0]! = start)
    (hrec : ∀ k, 0 < k → k < S.size →
      PA[k]! < k ∧ LA[k]! < gens.size ∧ S[k]! = imgSorted gens[LA[k]!]! S[PA[k]!]!)
    (hgood : ∀ i < S.size, Good n S[i]!)
    (hdist : ∀ i < S.size, ∀ j < S.size, S[i]! = S[j]! → i = j)
    (hle : hd ≤ S.size) (hor : S.size = bound ∨ hd = bound ∨ hd = S.size)
    (hcl : S.size < bound → ∀ i < hd, ∀ k < gens.size,
      ∃ i' < S.size, S[i']! = imgSorted gens[k]! S[i]!)
    (hc0 : 0 < c) (hcb : c ≤ bound) (hT0 : T 0 = start)
    (htree : ∀ i, 0 < i → i < c → P i < i ∧ L i < gens.size ∧ T i = imgSorted gens[L i]! (T (P i)))
    (hinj : ∀ a < c, ∀ b < c, T a = T b → a = b)
    (hclose : c < bound → ∀ h < c, ∀ k < gens.size, ∃ j < c, imgSorted gens[k]! (T h) = T j) :
    translatesOK gens start S PA LA = true ∧ keysSortedOK S = true ∧ S.size = c := by
  have hget : ∀ i (hi : i < S.toList.length), S.toList[i] = S[i]! := fun i hi => by
    rw [Array.getElem_toList, getElem!_pos S i (by simpa using hi)]
  have hnd : S.toList.Nodup := by
    refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
    rw [hget i hi, hget j hj] at e
    have := hdist i (by simpa using hi) j (by simpa using hj) e
    omega
  have hmem : ∀ x ∈ S.toList, ∃ i < S.size, S[i]! = x := fun x hx => by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
    exact ⟨i, by simpa using hi, by rw [← hget i hi, e]⟩
  have hmemS : ∀ i < S.size, S[i]! ∈ S.toList := fun i hi => by
    rw [← hget i (by simpa using hi)]
    exact List.getElem_mem _
  have hcard : S.toList.toFinset.card = S.size := by
    rw [List.toFinset_card_of_nodup hnd, Array.length_toList]
  refine ⟨?_, ?_, ?_⟩
  · unfold translatesOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨h0, hz⟩, allLt_true fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with e | e
    · simp [e]
    · obtain ⟨a, b, c'⟩ := hrec k e hk
      simp [a, b, c']
  · unfold keysSortedOK sortedKeys
    apply strictlyIncreasing_of
    have hle' := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (S.toList.map setKey)
    have hnd' : (S.toList.map setKey).Nodup := by
      refine List.Nodup.map_on (fun x hx y hy e => ?_) hnd
      obtain ⟨i, hi, rfl⟩ := hmem x hx
      obtain ⟨j, hj, rfl⟩ := hmem y hy
      exact eq_of_setKey (hgood i hi) (hgood j hj) e
    have hp := List.mergeSort_perm (S.toList.map setKey) (fun a b : Nat => decide (a ≤ b))
    exact (hle'.and (hp.nodup_iff.2 hnd')).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (by simpa using h1) h2
  ·
    have hlow : ∀ F : Finset (List Nat), start ∈ F →
        (∀ t ∈ F, ∀ k < gens.size, imgSorted gens[k]! t ∈ F) → c ≤ F.card := by
      intro F h0F hF
      have hTF : ∀ i < c, T i ∈ F := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ih =>
          intro hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · rw [hT0]
            exact h0F
          · obtain ⟨a, b, e⟩ := htree i hi0 hi
            rw [e]
            exact hF _ (ih _ a (by omega)) _ b
      have := Finset.card_le_card_of_injOn (s := Finset.range c) (t := F) T
        (fun i hi => hTF i (Finset.mem_range.1 hi))
        (fun a ha b hb e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)
      rwa [Finset.card_range] at this
    have hup : c < bound → S.size ≤ c := by
      intro hcb'
      have hin : ∀ i < S.size, ∃ j < c, S[i]! = T j := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ih =>
          intro hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · exact ⟨0, hc0, by rw [hz, hT0]⟩
          · obtain ⟨a, b, e⟩ := hrec i hi0 hi
            obtain ⟨j, hj, ej⟩ := ih _ a (by omega)
            obtain ⟨j', hj', ej'⟩ := hclose hcb' j hj _ b
            exact ⟨j', hj', by rw [e, ej, ej']⟩
      have hsub : S.toList.toFinset ⊆ (Finset.range c).image T := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
        obtain ⟨j, hj, e⟩ := hin i hi
        exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, e.symm⟩
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      rwa [hcard, Finset.card_range] at this
    by_cases hlt : S.size < bound
    · have hhd : hd = S.size := by rcases hor with e | e | e <;> omega
      have hge : c ≤ S.size := by
        rw [← hcard]
        refine hlow _ (by rw [List.mem_toFinset, ← hz]; exact hmemS 0 h0) fun x hx k hk => ?_
        obtain ⟨i, hi, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
        obtain ⟨i', hi', e⟩ := hcl hlt i (by omega) k hk
        rw [List.mem_toFinset, ← e]
        exact hmemS i' hi'
      rcases Nat.lt_or_ge c bound with h1 | h1
      · have := hup h1
        omega
      · omega
    · rcases Nat.lt_or_ge c bound with h1 | h1
      · have := hup h1
        omega
      · omega

theorem setReplay_proved {n w s kg c bound nS H nB B R : Nat} {G GI X W KT SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W KT SO SOI C start) :
    translatesOK gens start (hashSearch gens start bound).1 (hashSearch gens start bound).2.1
        (hashSearch gens start bound).2.2 = true ∧
      keysSortedOK (hashSearch gens start bound).1 = true ∧
      (hashSearch gens start bound).1.size = c := by
  obtain ⟨hc0, hcb, hpA, hgood, hT0, htree, hinj, hclose⟩ := replay_facts hg h
  have hs : Good n start := hT0 ▸ hgood 0 hc0
  rw [HashSearch.search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := HashSearch.outer_spec (bound := bound) (by omega) hpA hs
  generalize Id.run (forIn (List.range' 0 bound) (HashSearch.oinit start)
    (HashSearch.outerBody gens bound)) = st at hI hle hor hcl ⊢
  obtain ⟨-, -, h0, hbd, hz, hrec, -, hgd, hdist⟩ := hI
  exact assemble h0 hbd hz hrec hgd hdist hle hor hcl hc0 hcb hT0 htree hinj hclose

theorem setReplay_key_proved {n w s kg c bound nS H nB B R : Nat} {G GI X W KT SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W KT SO SOI C start) :
    translatesOK gens start (co3KeySearch gens start bound).1 (co3KeySearch gens start bound).2.1
        (co3KeySearch gens start bound).2.2 = true ∧
      keysSortedOK (co3KeySearch gens start bound).1 = true ∧
      (co3KeySearch gens start bound).1.size = c := by
  obtain ⟨hc0, hcb, hpA, hgood, hT0, htree, hinj, hclose⟩ := replay_facts hg h
  have hs : Good n start := hT0 ▸ hgood 0 hc0
  rw [KeySearch.search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := KeySearch.outer_spec (bound := bound) (by omega) hpA hs
  generalize Id.run (forIn (List.range' 0 bound) (KeySearch.oinit start)
    (KeySearch.outerBody gens bound)) = st at hI hle hor hcl ⊢
  obtain ⟨-, -, h0, hbd, hz, hrec, -, hgd, hdist⟩ := hI
  exact assemble h0 hbd hz hrec hgd hdist hle hor hcl hc0 hcb hT0 htree hinj hclose

end CFSG.KS.SporSch.SRP

end
