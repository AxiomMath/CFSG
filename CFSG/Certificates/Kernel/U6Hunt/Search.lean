module

public import Certificates.Data.Kernel.U6.HuntK
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.U6.HuntPf

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.Sporadic.Th.Native CFSG.KC.U6

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

private theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

private theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

private theorem beq_eq' (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

private theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

private theorem sumN_succ (n : Nat) (f : Nat → Nat) : sumN (n + 1) f = f n + sumN n f := rfl

private theorem sumN_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumN_succ, sumN_succ, h n (by omega), sumN_congr (fun i hi => h i (by omega))]

private theorem sumN_mul (c : Nat) (f : Nat → Nat) : ∀ n, sumN n f * c = sumN n (fun i => f i * c)
  | 0 => Nat.zero_mul c
  | n + 1 => by rw [sumN_succ, sumN_succ, Nat.add_mul, sumN_mul c f n]

theorem fget_eq (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  show Nat.land (Nat.shiftRight X (i * w)) (Nat.sub (Nat.shiftLeft 1 w) 1) = _
  rw [CFSG.KS.PackFld.shl_eq, Nat.one_mul, CFSG.KS.PackFld.shr_eq]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem fget5 (X i : Nat) : fget X i 5 = X / 32 ^ i % 32 := by
  rw [fget_eq, Nat.mul_comm, Nat.pow_mul]
  rfl

theorem fget5_lt (X i : Nat) : fget X i 5 < 32 := by
  rw [fget5]; exact Nat.mod_lt _ (by norm_num)

private theorem pg_eq (x i : Nat) : CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) x i = fget x i 5 := by
  rw [fget_eq, Nat.mul_comm i 5]
  show Nat.land (Nat.shiftRight x (5 * i)) (Nat.sub (Nat.shiftLeft 1 5) 1) = _
  rw [CFSG.KS.PackFld.shl_eq, Nat.one_mul, CFSG.KS.PackFld.shr_eq]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem eq_of_fget {x y : Nat} (hx : x < 2 ^ 110) (hy : y < 2 ^ 110)
    (h : ∀ i < 22, fget x i 5 = fget y i 5) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 110
  · have e : 5 * (b / 5) + b % 5 = b := Nat.div_add_mod b 5
    have h5 : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have t1 := CFSG.KS.PackFld.testBit_pgM 5 x (b / 5) (b % 5)
    have t2 := CFSG.KS.PackFld.testBit_pgM 5 y (b / 5) (b % 5)
    rw [pg_eq, e] at t1 t2
    simp only [h5, decide_true, Bool.true_and] at t1 t2
    rw [← t1, ← t2, h _ (by omega)]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

private theorem pack_spec (d : Nat → Nat) : ∀ n, (∀ i < n, d i < 32) →
    sumN n (fun i => Nat.shiftLeft (d i) (5 * i)) < 32 ^ n ∧
      ∀ j < n, sumN n (fun i => Nat.shiftLeft (d i) (5 * i)) / 32 ^ j % 32 = d j
  | 0, _ => ⟨by show 0 < 1; omega, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, hd => by
    obtain ⟨hlt, hdig⟩ := pack_spec d n (fun i hi => hd i (by omega))
    have hdn := hd n (by omega)
    have e0 : Nat.shiftLeft (d n) (5 * n) = d n * 32 ^ n := by
      rw [CFSG.KS.PackFld.shl_eq, Nat.pow_mul]
    rw [sumN_succ, e0]
    generalize sumN n (fun i => Nat.shiftLeft (d i) (5 * i)) = S at hlt hdig
    refine ⟨?_, ?_⟩
    · have : (d n + 1) * 32 ^ n ≤ 32 * 32 ^ n := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.pow_succ]
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm (32 ^ n) 32]
      omega
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have e2 : 32 ^ n = 32 ^ j * (32 * 32 ^ (n - j - 1)) := by
          rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
        have e : d n * 32 ^ n = 32 ^ j * (32 * (d n * 32 ^ (n - j - 1))) := by
          rw [e2, Nat.mul_left_comm, Nat.mul_left_comm (d n)]
        rw [e, Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity),
          Nat.add_mul_mod_self_left, hdig j hj]
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
          Nat.zero_add, Nat.mod_eq_of_lt hdn]

@[expose] noncomputable def tab (x : Nat) : Table :=
  Array.ofFn (n := 22) fun i => UInt32.ofNat (fget x i.val 5)

private theorem getElem!_ofFn22 (f : Fin 22 → UInt32) {i : Nat} (h : i < 22) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using h)]
  simp

theorem ap_tab {x i : Nat} (h : i < 22) : ap (tab x) i = fget x i 5 := by
  unfold ap tab
  rw [getElem!_ofFn22 _ h, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans (fget5_lt x i) (by norm_num))

theorem ap_decodeT {k i : Nat} (h : i < 22) : ap (decodeT k) i = k / 32 ^ (21 - i) % 32 := by
  unfold ap decodeT
  rw [getElem!_ofFn22 _ h, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))

private def Good (x : Nat) : Prop := x < 2 ^ 110 ∧ ∀ i < 22, fget x i 5 < 22

private theorem tab_inj {x y : Nat} (hx : Good x) (hy : Good y) : tab x = tab y ↔ x = y := by
  refine ⟨fun h => eq_of_fget hx.1 hy.1 fun i hi => ?_, fun h => h ▸ rfl⟩
  rw [← ap_tab hi, ← ap_tab hi, h]

private theorem tab_beq {x y : Nat} (hx : Good x) (hy : Good y) : (tab x == tab y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, tab_inj hx hy]

private theorem pc22_eq (p q : Nat) :
    pc22 p q = CFSG.KC.Enum.pcomp 22 5 (CFSG.KS.mask 5) p q := by
  unfold pc22
  rw [strictN_eq, strictN_eq]
  rfl

private theorem fget_pc22 (p q : Nat) {i : Nat} (hi : i < 22) :
    fget (pc22 p q) i 5 = fget p (fget q i 5) 5 := by
  rw [pc22_eq, ← pg_eq, CFSG.KS.PackFld.pg_pcomp (by norm_num) hi, pg_eq, pg_eq]

private theorem pc22_lt (p q : Nat) : pc22 p q < 2 ^ 110 := by
  have h := CFSG.KS.PackFld.pcomp_shr (n := 22) (w := 5) (p := p) (q := q) (by norm_num)
    (by norm_num)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h
  rw [pc22_eq]
  exact h.resolve_left (by positivity)

private theorem good_pc22 {p q : Nat} (hp : Good p) (hq : Good q) : Good (pc22 p q) :=
  ⟨pc22_lt p q, fun i hi => by rw [fget_pc22 _ _ hi]; exact hp.2 _ (hq.2 i hi)⟩

private theorem tab_pc22 (p : Nat) {q : Nat} (hq : Good q) :
    tab (pc22 p q) = compT 22 (tab p) (tab q) := by
  unfold compT
  rw [show tab (pc22 p q) = Array.ofFn (n := 22) (fun i => UInt32.ofNat (fget (pc22 p q) i.val 5))
    from rfl]
  refine congrArg (Array.ofFn (n := 22)) (funext fun i => ?_)
  rw [show ((tab q)[i.val]!).toNat = fget q i.val 5 from ap_tab i.isLt, fget_pc22 _ _ i.isLt]
  unfold tab
  rw [getElem!_ofFn22 _ (hq.2 i i.isLt)]

private theorem foldl_key (f : Nat → Nat) : ∀ n,
    (List.range n).foldl (fun acc i => acc * 32 + f i) 0 = sumN n (fun i => f i * 32 ^ (n - 1 - i))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_key f n,
      sumN_succ, sumN_mul]
    have : sumN n (fun i => f i * 32 ^ (n - 1 - i) * 32) =
        sumN n (fun i => f i * 32 ^ (n + 1 - 1 - i)) :=
      sumN_congr fun i hi => by
        rw [Nat.mul_assoc, ← Nat.pow_succ]; congr 2; omega
    rw [this, show n + 1 - 1 - n = 0 by omega, Nat.pow_zero, Nat.mul_one, Nat.add_comm]

theorem keyK_eq_keyT_tab (x : Nat) : keyK x = keyT (tab x) := by
  show sumN 22 (fun i => Nat.shiftLeft (fget x i 5) (5 * (21 - i))) = _
  unfold keyT
  rw [foldl_key]
  refine sumN_congr fun i hi => ?_
  rw [ap_tab hi, CFSG.KS.PackFld.shl_eq, Nat.pow_mul, show 22 - 1 - i = 21 - i by omega]

private theorem foldl_dec {k : Nat} (hk : k < 2 ^ 110) : ∀ n ≤ 22,
    (List.range n).foldl (fun acc i => acc * 32 + ap (decodeT k) i) 0 = k / 32 ^ (22 - n)
  | 0, _ => by
    rw [Nat.div_eq_of_lt (by norm_num at hk ⊢; omega)]
    rfl
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_dec hk n (by omega), ap_decodeT (by omega)]
    have e : 32 ^ (22 - n) = 32 ^ (21 - n) * 32 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, show 22 - (n + 1) = 21 - n by omega]
    exact Nat.div_add_mod' _ _

theorem keyT_decodeT {k : Nat} (hk : k < 2 ^ 110) : keyT (decodeT k) = k := by
  unfold keyT
  rw [foldl_dec hk 22 le_rfl, Nat.sub_self, Nat.pow_zero, Nat.div_one]

private theorem unkey_eq (k : Nat) :
    unkey k = sumN 22 (fun i => Nat.shiftLeft (fget k (21 - i) 5) (5 * i)) := rfl

private theorem fget_unkey (k : Nat) {i : Nat} (hi : i < 22) :
    fget (unkey k) i 5 = k / 32 ^ (21 - i) % 32 := by
  rw [fget5, unkey_eq,
    (pack_spec (fun j => fget k (21 - j) 5) 22 (fun j _ => fget5_lt _ _)).2 i hi, fget5]

private theorem unkey_lt (k : Nat) : unkey k < 2 ^ 110 := by
  rw [unkey_eq]
  have := (pack_spec (fun j => fget k (21 - j) 5) 22 (fun j _ => fget5_lt k (21 - j))).1
  norm_num at this ⊢
  exact this

private theorem tab_unkey (k : Nat) : tab (unkey k) = decodeT k := by
  unfold tab decodeT
  refine congrArg (Array.ofFn (n := 22)) (funext fun i => ?_)
  rw [fget_unkey k i.isLt]

private theorem id22_eq : id22 = sumN 22 (fun i => Nat.shiftLeft i (5 * i)) := rfl

private theorem fget_id22 {i : Nat} (hi : i < 22) : fget id22 i 5 = i := by
  rw [fget5, id22_eq, (pack_spec (fun i => i) 22 (fun j hj => by omega)).2 i hi]

private theorem good_id22 : Good id22 := by
  refine ⟨?_, fun i hi => by rw [fget_id22 hi]; exact hi⟩
  rw [id22_eq]
  have := (pack_spec (fun i => i) 22 (fun j hj => by omega)).1
  norm_num at this ⊢
  exact this

private theorem tab_id22 : tab id22 = idT 22 := by
  unfold tab idT
  refine congrArg (Array.ofFn (n := 22)) (funext fun i => ?_)
  rw [fget_id22 i.isLt]

private theorem PV_spec : ∀ j < 32, fget PV j 10 = ptvArr.getD j 0 := by decide +kernel

private theorem testBit_beq (m n : Nat) :
    Nat.beq (fget m n (nat_lit 1)) (nat_lit 1) = m.testBit n := by
  rw [beq_eq', fget_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.mul_one, Nat.pow_one]

private theorem actK_rec (t m : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => CFSG.KC.Loop.strictN acc fun acc =>
        nIf(Nat.beq (fget m i (nat_lit 1)) (nat_lit 1), Nat.xor acc (fget PV (ap5 t i) (nat_lit 10)),
          acc)) n =
      (List.range n).foldl
        (fun acc i => if m.testBit i then acc ^^^ ptvArr.getD (fget t i 5) 0 else acc) 0
  | 0 => rfl
  | n + 1 => by
    show CFSG.KC.Loop.strictN (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => CFSG.KC.Loop.strictN acc fun acc =>
        nIf(Nat.beq (fget m i (nat_lit 1)) (nat_lit 1), Nat.xor acc (fget PV (ap5 t i) (nat_lit 10)),
          acc)) n) (fun acc =>
        nIf(Nat.beq (fget m n (nat_lit 1)) (nat_lit 1), Nat.xor acc (fget PV (ap5 t n) (nat_lit 10)),
          acc)) = _
    rw [strictN_eq, actK_rec t m n, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, testBit_beq]
    generalize List.foldl
      (fun acc i => if m.testBit i then acc ^^^ ptvArr.getD (fget t i 5) 0 else acc) 0
      (List.range n) = X
    cases m.testBit n
    · rfl
    · rw [if_pos rfl]
      show Nat.xor X (fget PV (fget t n 5) 10) = _
      rw [PV_spec _ (fget5_lt t n)]
      rfl

private theorem actK_eq (t m : Nat) : actK t m =
    (List.range 22).foldl
      (fun acc i => if m.testBit i then acc ^^^ ptvArr.getD (fget t i 5) 0 else acc) 0 := by
  unfold actK
  exact actK_rec t m (nat_lit 22)

private theorem actM_tab (t m : Nat) : actM (tab t) m = actK t m := by
  rw [actK_eq]
  unfold actM
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  refine congrArg (fun g => List.foldl g 0 (List.finRange 22))
    (funext fun acc => funext fun i => ?_)
  rw [ap_tab i.isLt]

private theorem inK_eq {y : Nat} (hy : Good y) : ∀ {span : List Nat}, (∀ x ∈ span, Good x) →
    inK span y = (span.map tab).contains (tab y)
  | [], _ => rfl
  | s :: ss, h => by
    show CFSG.KLie.CT.orB (Nat.beq s y) (inK ss y) = _
    rw [orB_eq, inK_eq hy (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.map_cons,
      List.contains_cons, tab_beq hy (h s List.mem_cons_self),
      show Nat.beq s y = (y == s) by rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, eq_comm]]

private theorem allKey_eq {y : Nat} (hy : Good y) : ∀ {span : List Nat}, (∀ x ∈ span, Good x) →
    List.rec (motive := fun _ => Bool) true
        (fun s _ ih => CFSG.KLie.CT.andB (Nat.ble (keyK y) (keyK (pc22 y s))) ih) span =
      (span.map tab).all (fun s => decide (keyT (tab y) ≤ keyT (compT 22 (tab y) s)))
  | [], _ => rfl
  | s :: ss, h => by
    show CFSG.KLie.CT.andB (Nat.ble (keyK y) (keyK (pc22 y s))) (List.rec (motive := fun _ => Bool)
      true (fun s _ ih => CFSG.KLie.CT.andB (Nat.ble (keyK y) (keyK (pc22 y s))) ih) ss) = _
    rw [andB_eq, allKey_eq hy (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.map_cons,
      List.all_cons, ble_eq, keyK_eq_keyT_tab, keyK_eq_keyT_tab, tab_pc22 _ (h s List.mem_cons_self)]

private theorem newGenK_eq {y : Nat} (hy : Good y) {span : List Nat} (h : ∀ x ∈ span, Good x) :
    newGenK span y = newGen (span.map tab) (tab y) := by
  unfold newGenK newGen
  rw [andB_eq, notB_eq, inK_eq hy h, strictB_eq, allKey_eq hy h]

private theorem mapComp_eq (y : Nat) : ∀ span, mapComp y span = span.map (pc22 y)
  | [] => rfl
  | s :: ss => by
    show pc22 y s :: mapComp y ss = _
    rw [mapComp_eq y ss]
    rfl

private theorem filtFix_eq (y : Nat) :
    ∀ fix, filtFix y fix = fix.filter fun m => actM (tab y) m == m
  | [] => rfl
  | m :: ms => by
    show Bool.rec (motive := fun _ => List Nat) (filtFix y ms) (m :: filtFix y ms)
      (Nat.beq (actK y m) m) = _
    rw [List.filter_cons, filtFix_eq y ms, actM_tab, beq_eq]
    cases (actK y m == m) <;> rfl

private theorem filtComm_eq (y : Nat) : ∀ ys,
    filtComm y ys = ys.filter fun z => pc22 y z == pc22 z y
  | [] => rfl
  | z :: zs => by
    show Bool.rec (motive := fun _ => List Nat) (filtComm y zs) (z :: filtComm y zs)
      (Nat.beq (pc22 y z) (pc22 z y)) = _
    rw [List.filter_cons, filtComm_eq y zs, beq_eq]
    cases (pc22 y z == pc22 z y) <;> rfl

private theorem filtComm_map {y : Nat} (hy : Good y) {ys : List Nat} (h : ∀ x ∈ ys, Good x) :
    (filtComm y ys).map tab =
      (ys.map tab).filter fun z => compT 22 (tab y) z == compT 22 z (tab y) := by
  rw [filtComm_eq, List.filter_map]
  refine congrArg (List.map tab) (List.filter_congr fun z hz => ?_)
  show _ = (compT 22 (tab y) (tab z) == compT 22 (tab z) (tab y))
  rw [← tab_pc22 _ (h z hz), ← tab_pc22 _ hy,
    tab_beq (good_pc22 hy (h z hz)) (good_pc22 (h z hz) hy)]

private theorem fixMK_rec (t : Nat) : ∀ n, n ≤ 1024 →
    Nat.rec (motive := fun _ => List Nat) []
        (fun j acc => (fun m => Bool.rec (motive := fun _ => List Nat) acc (m :: acc)
          (Nat.beq (actK t m) m)) (Nat.sub (nat_lit 1023) j)) n =
      (List.range' (1024 - n) n).filter fun m => Nat.beq (actK t m) m
  | 0, _ => rfl
  | n + 1, hn => by
    show Bool.rec (motive := fun _ => List Nat)
        (Nat.rec (motive := fun _ => List Nat) []
          (fun j acc => (fun m => Bool.rec (motive := fun _ => List Nat) acc (m :: acc)
            (Nat.beq (actK t m) m)) (Nat.sub (nat_lit 1023) j)) n)
        (Nat.sub (nat_lit 1023) n :: Nat.rec (motive := fun _ => List Nat) []
          (fun j acc => (fun m => Bool.rec (motive := fun _ => List Nat) acc (m :: acc)
            (Nat.beq (actK t m) m)) (Nat.sub (nat_lit 1023) j)) n)
        (Nat.beq (actK t (Nat.sub (nat_lit 1023) n)) (Nat.sub (nat_lit 1023) n)) = _
    rw [fixMK_rec t n (by omega), show Nat.sub (nat_lit 1023) n = 1023 - n from rfl,
      show 1024 - (n + 1) = 1023 - n by omega, List.range'_succ,
      show 1023 - n + 1 = 1024 - n by omega, List.filter_cons]
    cases h : Nat.beq (actK t (1023 - n)) (1023 - n)
    · rw [if_neg (by simp)]
    · rw [if_pos rfl]

private theorem fixMK_eq (t : Nat) :
    fixMK t = (List.range 1024).filter fun m => actM (tab t) m == m := by
  unfold fixMK
  refine (fixMK_rec t (nat_lit 1024) (Nat.le_refl _)).trans ?_
  rw [Nat.sub_self, ← List.range_eq_range']
  refine List.filter_congr fun m _ => ?_
  rw [actM_tab, beq_eq]

private theorem nodeK_succ (B f : Nat) (span fix rest : List Nat) : nodeK B (f + 1) span fix rest =
    CFSG.KLie.CT.andB (Nat.ble (Nat.mul (List.length span) (List.length fix)) B)
      (List.rec (motive := fun _ => Bool) true (fun y ys acc =>
        CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (newGenK span y))
          (nodeK B f (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys))) acc)
        rest) := rfl

private theorem tails_cons' (a : Table) (l : List Table) : (a :: l).tails = (a :: l) :: l.tails :=
  rfl

private theorem inner_eq (B f : Nat) (span fix : List Nat) (F : List Table → Bool)
    (hF0 : F [] = true)
    (hF : ∀ y ys, Good y → (∀ x ∈ ys, Good x) →
      (!(newGenK span y) ||
        nodeK B f (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys)) =
        F (tab y :: ys.map tab)) :
    ∀ rest : List Nat, (∀ x ∈ rest, Good x) →
      List.rec (motive := fun _ => Bool) true (fun y ys acc =>
        CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (newGenK span y))
          (nodeK B f (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys))) acc)
        rest = (rest.map tab).tails.all F
  | [], _ => by
    show true = ([[]] : List (List Table)).all F
    rw [List.all_cons, List.all_nil, hF0]
    rfl
  | y :: ys, hr => by
    show CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (newGenK span y))
        (nodeK B f (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys)))
      (List.rec (motive := fun _ => Bool) true (fun y ys acc =>
        CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (newGenK span y))
          (nodeK B f (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys))) acc)
        ys) = _
    have hys : ∀ x ∈ ys, Good x := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    rw [andB_eq, orB_eq, notB_eq, hF y ys (hr y List.mem_cons_self) hys,
      inner_eq B f span fix F hF0 hF ys hys, List.map_cons, tails_cons', List.all_cons]

private theorem nodeK_eq (B : Nat) : ∀ fuel span fix rest, (∀ x ∈ span, Good x) →
    (∀ x ∈ rest, Good x) →
    nodeK B fuel span fix rest = node B fuel (span.map tab) fix (rest.map tab)
  | 0, _, _, _, _, _ => rfl
  | f + 1, span, fix, rest, hs, hr => by
    rw [nodeK_succ, node, andB_eq, ble_eq, List.length_map]
    refine congrArg (fun b => decide (span.length * fix.length ≤ B) && b) ?_
    refine inner_eq B f span fix _ rfl ?_ rest hr
    intro y ys hy hys
    have hsp : ∀ x ∈ List.append span (mapComp y span), Good x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs x hx
      · rw [mapComp_eq, List.mem_map] at hx
        obtain ⟨s, hs', rfl⟩ := hx
        exact good_pc22 hy (hs s hs')
    have hfc : ∀ x ∈ filtComm y ys, Good x := by
      intro x hx
      rw [filtComm_eq, List.mem_filter] at hx
      exact hys x hx.1
    have e : (List.append span (mapComp y span)).map tab =
        span.map tab ++ (span.map tab).map (compT 22 (tab y)) := by
      rw [List.append_eq, List.map_append, mapComp_eq, List.map_map, List.map_map]
      exact congrArg (span.map tab ++ ·)
        (List.map_congr_left fun s hs' => tab_pc22 _ (hs s hs'))
    rw [newGenK_eq hy hs, nodeK_eq B f _ _ _ hsp hfc, e, filtComm_map hy hys, filtFix_eq]

private theorem rec_unkey : ∀ L : List Nat,
    List.rec (motive := fun _ => List Nat) [] (fun x _ ih => unkey x :: ih) L = L.map unkey
  | [] => rfl
  | x :: xs => by
    show unkey x :: List.rec (motive := fun _ => List Nat) [] (fun x _ ih => unkey x :: ih) xs = _
    rw [rec_unkey xs]
    rfl

private theorem rootK_eq (B k : Nat) (L : List Nat) : rootK B k L =
    nodeK B (nat_lit 8) [id22, unkey k] (fixMK (unkey k))
      (List.rec (motive := fun _ => List Nat) [] (fun x _ ih => unkey x :: ih) L) := by
  unfold rootK
  exact strictB_eq _ _

theorem sound3003R' {B k : Nat} {L : List Nat} (hd : ∀ i < 22, fget (unkey k) i 5 < 22)
    (hL : ∀ x ∈ L, x < 2 ^ 110 ∧ ∀ i < 22, fget (unkey x) i 5 < 22)
    (hk : rootK B k L = true) : rootCheck B (decodeT k) (L.map decodeT) = true := by
  have hg : Good (unkey k) := ⟨unkey_lt k, hd⟩
  have hspan : ∀ x ∈ [id22, unkey k], Good x := by
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]; exact good_id22
    · rw [List.mem_singleton.mp hx]; exact hg
  have hrest : ∀ x ∈ L.map unkey, Good x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨unkey_lt y, (hL y hy).2⟩
  rw [rootK_eq, rec_unkey, nodeK_eq B (nat_lit 8) _ _ _ hspan hrest, fixMK_eq, List.map_map,
    show tab ∘ unkey = decodeT from funext tab_unkey, List.map_cons, List.map_cons, List.map_nil,
    tab_id22, tab_unkey] at hk
  exact hk

theorem sound3003P' {L : List Nat} (hs : L.Pairwise (· < ·)) (hL : ∀ x ∈ L, x < 2 ^ 110) :
    (L.map decodeT).Pairwise (fun a b => keyT a < keyT b) := by
  rw [List.pairwise_map]
  refine hs.imp_of_mem fun {a b} ha hb hab => ?_
  rw [keyT_decodeT (hL a ha), keyT_decodeT (hL b hb)]
  exact hab

end CFSG.KC.U6.HuntPf

end
