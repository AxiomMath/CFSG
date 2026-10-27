
module

public import Certificates.Data.Kernel.O8.SA
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowBase
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.LocalCompAglSound
public import Certificates.Data.Kernel.O8.Ord
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.EvenSmallLie.OmegaEight

theorem colK_eq (M c : Nat) : colK M c = M / 256 ^ c % 256 := by
  change (M >>> (8 * c)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem bit_eq (v c : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight v c) 1) 1 = v.testBit c := by
  change ((v >>> c) &&& 1 == 1) = _
  rw [Nat.testBit, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (v >>> c) with h | h <;> simp [h]

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

theorem xor_def (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem matAppK_eq (M v : Nat) : matAppK M v = matApp M v := by
  rw [matApp_eq, range8]
  simp only [matAppK, List.range'_succ, List.range'_zero, List.foldr_cons, List.foldr_nil,
    bit_eq, nIf_eq, colK_eq, xor_def, Nat.zero_add, Nat.reduceAdd, Nat.zero_xor, Nat.xor_zero]
  ac_rfl

@[expose] def horner (d : Nat → Nat) (s n : Nat) : Nat :=
  (List.range' s n).foldr (fun c acc => d c + 256 * acc) 0

theorem horner_succ (d : Nat → Nat) (s n : Nat) :
    horner d s (n + 1) = d s + 256 * horner d (s + 1) n := by
  rw [horner, List.range'_succ, List.foldr_cons]
  rfl

theorem horner_testBit (d : Nat → Nat) (hd : ∀ c, d c < 256) :
    ∀ (n s i : Nat), (horner d s n).testBit i =
      (decide (i < 8 * n) && (d (s + i / 8)).testBit (i % 8))
  | 0, s, i => by simp [horner]
  | n + 1, s, i => by
    rw [horner_succ, Nat.add_comm, show (256 : Nat) = 2 ^ 8 by norm_num,
      Nat.testBit_two_pow_mul_add _ (by simpa using hd s)]
    split
    · next h =>
      have h1 : i / 8 = 0 := Nat.div_eq_of_lt h
      have h2 : i % 8 = i := Nat.mod_eq_of_lt h
      rw [h1, h2, Nat.add_zero]
      simp [show i < 8 * (n + 1) by omega]
    · next h =>
      rw [horner_testBit d hd n (s + 1) (i - 8)]
      have h1 : (i - 8) / 8 + 1 = i / 8 := by omega
      have h2 : (i - 8) % 8 = i % 8 := by omega
      rw [h2, Nat.add_assoc, Nat.add_comm 1, h1]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem horner_lt8 (d : Nat → Nat) (hd : ∀ c, d c < 256) (s : Nat) : horner d s 8 < 2 ^ 64 := by
  have h := horner_lt d hd 8 s
  rw [horner]
  norm_num at h ⊢
  exact h

theorem eq_of_horner_testBit {x : Nat} (d : Nat → Nat) (hd : ∀ c, d c < 256) (hx : x < 2 ^ 64)
    (h : ∀ k < 8, ∀ r < 8, x.testBit (8 * k + r) = (d k).testBit r) : x = horner d 0 8 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [horner_testBit d hd, Nat.zero_add]
  by_cases hi : i < 64
  · have := h (i / 8) (by omega) (i % 8) (Nat.mod_lt _ (by norm_num))
    rw [show 8 * (i / 8) + i % 8 = i by omega] at this
    rw [this]
    simp [show i < 8 * 8 by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [show ¬ i < 8 * 8 by omega]

theorem matMulM_horner (A B : Nat) : matMulM A B = horner (fun c => matApp A (B / 256 ^ c % 256)) 0 8 := by
  rw [matMulM, range8]
  rfl

theorem lmask_testBit (i : Nat) :
    (72340172838076673 : Nat).testBit i = (decide (i < 64) && i % 8 == 0) := by
  have e : (72340172838076673 : Nat) = horner (fun _ => 1) 0 8 := by decide
  rw [e, horner_testBit _ (fun _ => by norm_num)]
  rcases Nat.lt_or_ge i 64 with h | h
  · simp only [show i < 8 * 8 by omega, decide_true, Bool.true_and]
    rcases Nat.lt_or_ge (i % 8) 1 with h1 | h1
    · simp [show i % 8 = 0 by omega]
    · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (i % 8) from Nat.one_lt_two_pow (by omega))]
      simp [show i % 8 ≠ 0 by omega]
  · simp [show ¬ i < 8 * 8 by omega]

theorem maskMul_eq (A B : Nat) {c : Nat} (hc : c < 8) :
    Nat.land (Nat.shiftRight B c) 72340172838076673 * colK A c =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) 0 8 := by
  have hd : ∀ k, (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) < 256 := by
    intro k
    split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  have hm : Nat.land (Nat.shiftRight B c) 72340172838076673 =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then 1 else 0) 0 8 := by
    refine eq_of_horner_testBit _ (fun k => by split <;> norm_num)
      (lt_of_le_of_lt Nat.and_le_right (by norm_num)) fun k hk r hr => ?_
    change ((B >>> c) &&& 72340172838076673).testBit (8 * k + r) = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, lmask_testBit]
    have e1 : (B / 256 ^ k % 256).testBit c = B.testBit (8 * k + c) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow]
      simp [hc, Nat.add_comm]
    rw [e1]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have h1 : decide (8 * k + 0 < 64) = true := by simp; omega
      have h2 : ((8 * k + 0) % 8 == 0) = true := by simp
      rw [h1, h2, Bool.true_and, Bool.and_true, Nat.add_zero, Nat.add_comm c]
      split <;> simp_all
    · have hne : ((8 * k + r) % 8 == 0) = false := by simp; omega
      have h1 : (1 : Nat).testBit r = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      rw [hne, Bool.and_false, Bool.and_false]
      split <;> simp [h1]
  rw [hm, colK_eq]
  generalize A / 256 ^ c % 256 = a at hd ⊢
  have : ∀ s n, horner (fun k => if (B / 256 ^ k % 256).testBit c then 1 else 0) s n * a =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then a else 0) s n := by
    intro s n
    induction n generalizing s with
    | zero => simp [horner]
    | succ n ih =>
      rw [horner_succ, horner_succ, Nat.add_mul, Nat.mul_assoc, ih]
      congr 1
      split <;> simp
  exact this 0 8

theorem horner_xor (d e : Nat → Nat) (hd : ∀ c, d c < 256) (he : ∀ c, e c < 256) :
    horner d 0 8 ^^^ horner e 0 8 = horner (fun k => d k ^^^ e k) 0 8 := by
  refine eq_of_horner_testBit _ (fun c => Nat.xor_lt_two_pow (n := 8) (hd c) (he c))
    (Nat.xor_lt_two_pow (horner_lt8 d hd 0) (horner_lt8 e he 0)) fun k hk r hr => ?_
  rw [Nat.testBit_xor, horner_testBit d hd, horner_testBit e he, Nat.testBit_xor]
  have h1 : (8 * k + r) / 8 = k := by omega
  have h2 : (8 * k + r) % 8 = r := by omega
  rw [h1, h2, Nat.zero_add]
  simp [show 8 * k + r < 8 * 8 by omega]

theorem matMulK_eq (A B : Nat) : matMulK A B = matMulM A B := by
  have hd : ∀ c < 8, ∀ k, (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) < 256 :=
    fun c _ k => by split <;> [exact Nat.mod_lt _ (by norm_num); norm_num]
  have key : ∀ n ≤ 8, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight B c) (nat_lit 72340172838076673))
        (colK A c))) n =
      horner (fun k => (List.range n).foldr (fun c acc =>
        (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) 0) 0 8 := by
    intro n hn
    induction n with
    | zero =>
      change 0 = _
      rw [horner]
      simp [List.range'_succ]
    | succ n ih =>
      change Nat.xor (Nat.rec (motive := fun _ => Nat) (nat_lit 0) _ n) _ = _
      rw [ih (by omega), Nat.mul_eq, maskMul_eq A B (by omega), xor_def]
      rw [horner_xor _ _ (fun k => foldr_xor_lt _ _ fun c => by
          split <;> [exact Nat.mod_lt _ (by norm_num); norm_num]) (hd n (by omega))]
      congr 1
      funext k
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.xor_zero]
      have : ∀ (L : List Nat) (x : Nat), L.foldr (fun c acc =>
          (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) x =
          L.foldr (fun c acc =>
            (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) 0 ^^^ x := by
        intro L x
        induction L with
        | nil => simp
        | cons a L ihL => rw [List.foldr_cons, List.foldr_cons, ihL, Nat.xor_assoc]
      conv_rhs => rw [this]
  rw [matMulM_horner, show matMulK A B = Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight B c) (nat_lit 72340172838076673))
        (colK A c))) 8 from rfl, key 8 le_rfl]
  congr 1
  funext k
  rw [matApp_eq]

theorem conjK_cons (G Gi : Nat → Nat) (l : Nat) (w : List Nat) (b : Nat) :
    conjK G Gi (l :: w) b = matMulK (matMulK (G l) (conjK G Gi w b)) (Gi l) := rfl

theorem conjW_cons (G Gi : Nat → Nat) (l : Nat) (w : List Nat) (b : Nat) :
    conjW G Gi (l :: w) b = matMulM (matMulM (G l) (conjW G Gi w b)) (Gi l) := by
  simp only [conjW, List.foldr_cons]

theorem conjK_eq (G Gi : Nat → Nat) (w : List Nat) (b : Nat) : conjK G Gi w b = conjW G Gi w b := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [conjK_cons, conjW_cons, matMulK_eq, matMulK_eq, ih]

theorem memK_cons (x a : Nat) (found : List Nat) :
    memK x (a :: found) = Bool.rec (motive := fun _ => Bool) (memK x found) true (Nat.beq a x) :=
  rfl

theorem memK_spec (x : Nat) : ∀ found : List Nat, memK x found = true ↔ x ∈ found
  | [] => by simp [memK]
  | a :: found => by
    rw [memK_cons, List.mem_cons, ← memK_spec x found]
    cases h : Nat.beq a x
    · have : a ≠ x := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
      simp [Ne.symm this]
    · simp [Nat.eq_of_beq_eq_true h]

theorem greedyK_nil (G Gi : Nat → Nat) (b : Nat) (found : List Nat) :
    greedyK G Gi b [] found = Nat.ble 5 found.length := rfl

theorem greedyK_cons (G Gi : Nat → Nat) (b : Nat) (w : List Nat) (ws : List (List Nat))
    (found : List Nat) :
    greedyK G Gi b (w :: ws) found = Bool.rec (motive := fun _ => Bool)
      (strictB (conjK G Gi w b) fun c => Bool.rec (motive := fun _ => Bool)
        (greedyK G Gi b ws (c :: found)) (greedyK G Gi b ws found) (memK c found))
      true (Nat.ble 5 found.length) := rfl

theorem greedyK_sound (G Gi : Nat → Nat) (b : Nat) :
    ∀ (ws : List (List Nat)) (us : List (List Nat)) (found : List Nat),
      found = us.map (fun u => conjW G Gi u b) →
      us.Pairwise (fun u u' => conjW G Gi u b ≠ conjW G Gi u' b) →
      greedyK G Gi b ws found = true →
      ∃ vs : List (List Nat), vs.length = 5 ∧ (∀ v ∈ vs, v ∈ us ∨ v ∈ ws) ∧
        vs.Pairwise fun v v' => conjW G Gi v b ≠ conjW G Gi v' b
  | [], us, found, hf, hus, h => by
    rw [greedyK_nil, Nat.ble_eq, hf, List.length_map] at h
    exact ⟨us.take 5, by simp; omega, fun v hv => Or.inl (List.mem_of_mem_take hv),
      hus.sublist (List.take_sublist _ _)⟩
  | w :: ws, us, found, hf, hus, h => by
    rw [greedyK_cons] at h
    cases h5 : Nat.ble 5 found.length
    · rw [h5, CFSG.KLC.E8.strictB_eq', conjK_eq] at h
      change Bool.rec (motive := fun _ => Bool) _ _ (memK (conjW G Gi w b) found) = true at h
      cases hm : memK (conjW G Gi w b) found
      · rw [hm] at h
        have hw : ∀ u ∈ us, conjW G Gi w b ≠ conjW G Gi u b := fun u hu e => by
          have := (memK_spec _ _).2 (hf ▸ List.mem_map.2 ⟨u, hu, e.symm⟩)
          rw [hm] at this
          exact absurd this (by decide)
        obtain ⟨vs, hl, hm', hp⟩ := greedyK_sound G Gi b ws (w :: us) _
          (by rw [hf, List.map_cons]) (List.pairwise_cons.2 ⟨hw, hus⟩) h
        refine ⟨vs, hl, fun v hv => ?_, hp⟩
        rcases hm' v hv with h' | h'
        · rcases List.mem_cons.1 h' with rfl | h'
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h')
      · rw [hm] at h
        obtain ⟨vs, hl, hm', hp⟩ := greedyK_sound G Gi b ws us found hf hus h
        exact ⟨vs, hl, fun v hv => (hm' v hv).imp_right (List.mem_cons_of_mem _), hp⟩
    · rw [Nat.ble_eq, hf, List.length_map] at h5
      exact ⟨us.take 5, by simp; omega, fun v hv => Or.inl (List.mem_of_mem_take hv),
        hus.sublist (List.take_sublist _ _)⟩

theorem actsK_sound {NS NI P M : Nat}
    (hNS : ∀ p < 120, nsArr[p]! = pg 8 255 NS p) (hNI : ∀ v < 256, nsIdx[v]! = pg 8 255 NI v)
    (h : actsK NS NI P M = true) : ActsOn0 (CFSG.KS.Raw.unpack 360 9 P) M := fun p hp => by
  have h1 := CFSG.KS.allN_spec h p hp
  rw [CFSG.KLC.E8.strictB_eq', CFSG.KS.bAnd_iff] at h1
  obtain ⟨h1, h2⟩ := h1
  have hm : CFSG.KS.mask 9 = 511 := rfl
  rw [matAppK_eq] at h2
  rw [CFSG.KC.Misc.PairCount.unpack_get (by omega), hm, hNS p hp, hNI _ (matApp_lt _ _)]
  exact ⟨by simpa using h1, Nat.eq_of_beq_eq_true h2⟩

theorem allIn_zero_iff {n : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, by omega⟩ (List.mem_finRange _)
  · intro h k _
    simpa using h k.val (by have := k.isLt; omega)

theorem ordK_sound {n w R k : Nat}
    (hR : CFSG.KS.Prim.canonK n w (CFSG.KS.mask w) (n * w) R = true)
    (h : ordK n w (CFSG.KS.mask w) (pidn n w) R k = true) :
    CFSG.Sporadic.Schreier.Native.ordTest n k
      (CFSG.ComponentClassification.J2Cover.arrTable n (CFSG.KS.Raw.unpack n w R)) = true := by
  obtain ⟨hn, hw, -, hRr⟩ := CFSG.KS.PF.canon_facts hR
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := CFSG.KS.PF.w_pos hw
  let T := CFSG.ComponentClassification.J2Cover.arrTable n (CFSG.KS.Raw.unpack n w R)
  let P : Nat → Nat := CFSG.KS.ppow n w (CFSG.KS.mask w) (pidn n w) R
  have hP0 : P 0 = pidn n w := rfl
  have hPs : ∀ e, P (e + 1) = pcomp n w (CFSG.KS.mask w) R (P e) := fun e =>
    CFSG.KS.PF.strictN_eqP (P e) (fun q => pcomp n w (CFSG.KS.mask w) R q)
  have hap : ∀ j < n, CFSG.Sporadic.Th.Native.ap T j = pg w (CFSG.KS.mask w) R j := by
    intro j hj
    simp only [CFSG.Sporadic.Th.Native.ap, T, CFSG.ComponentClassification.J2Cover.arrTable]
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
      CFSG.KC.Misc.PairCount.unpack_get hj, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by have := hRr j hj; omega)]
  have hpow : ∀ e, P e >>> (n * w) = 0 ∧ ∀ i < n,
      CFSG.Sporadic.Schreier.Native.apPowW [T] e i = pg w (CFSG.KS.mask w) (P e) i ∧
        pg w (CFSG.KS.mask w) (P e) i < n := by
    intro e
    induction e with
    | zero =>
      refine ⟨CFSG.KS.PF.pidn_shr hn hw, fun i hi => ?_⟩
      rw [hP0, CFSG.KS.PF.pg_pidn hn hw hi]
      exact ⟨rfl, hi⟩
    | succ e ih =>
      refine ⟨by rw [hPs]; exact CFSG.KS.PF.pcomp_shr _ _ hn32 hw0, fun i hi => ?_⟩
      obtain ⟨e1, e2⟩ := ih.2 i hi
      rw [hPs, CFSG.KS.PF.pg_pcomp hn32 hi]
      refine ⟨?_, hRr _ e2⟩
      change CFSG.Sporadic.Schreier.Native.apW [T]
        (CFSG.Sporadic.Schreier.Native.apPowW [T] e i) = _
      rw [e1]
      exact hap _ e2
  have hfix : ∀ e, CFSG.Sporadic.Schreier.Native.powFixW n [T] e = Nat.beq (P e) (pidn n w) := by
    intro e
    apply Bool.eq_iff_iff.2
    rw [CFSG.Sporadic.Schreier.Native.powFixW, allIn_zero_iff, Nat.beq_eq]
    constructor
    · intro H
      refine CFSG.KS.PF.eq_of_fields hw0 (hpow e).1 (CFSG.KS.PF.pidn_shr hn hw) fun i hi => ?_
      have := H i hi
      rw [beq_iff_eq, ((hpow e).2 i hi).1] at this
      rw [this, CFSG.KS.PF.pg_pidn hn hw hi]
    · intro H i hi
      rw [beq_iff_eq, ((hpow e).2 i hi).1, H, CFSG.KS.PF.pg_pidn hn hw hi]
  unfold ordK at h
  rw [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  unfold CFSG.Sporadic.Schreier.Native.ordTest CFSG.Sporadic.Schreier.Native.ordW
  rw [hfix k, h1, Bool.true_and, List.all_eq_true]
  intro e he
  have h3 := List.all_eq_true.1 h2 e he
  rw [hfix e]
  cases hb : Nat.beq (P e) (pidn n w)
  · rfl
  · change Bool.rec (motive := fun _ => Bool) true false (Nat.beq (P e) (pidn n w)) = true at h3
    rw [hb] at h3
    exact absurd h3 Bool.false_ne_true

end CFSG.KC.O8

end
