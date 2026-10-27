module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFinK

@[expose] noncomputable def forceT {α : Type} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

theorem forceT_eq {α : Type} (y : ℕ) (k : ℕ → α) : forceT y k = k y := by
  cases y <;> rfl

@[expose] def colC (m i : Nat) : Nat := (m >>> (4 * i)) &&& 15

@[expose] def appC (m v : Nat) : Nat :=
  (if v &&& 1 != 0 then colC m 0 else 0) ^^^ (if v &&& 2 != 0 then colC m 1 else 0) ^^^
  (if v &&& 4 != 0 then colC m 2 else 0) ^^^ (if v &&& 8 != 0 then colC m 3 else 0)

@[expose] def mmulC (a b : Nat) : Nat :=
  appC a (colC b 0) ||| (appC a (colC b 1) <<< 4) ||| (appC a (colC b 2) <<< 8) |||
    (appC a (colC b 3) <<< 12)

@[expose] noncomputable def colF (m o : ℕ) : ℕ := Nat.land (Nat.shiftRight m o) (nat_lit 15)

@[expose] noncomputable def selF (v k c : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0) c (Nat.blt (nat_lit 0) (Nat.land v k))

@[expose] noncomputable def appF (m v : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (selF v (nat_lit 1) (colF m (nat_lit 0)))
    (selF v (nat_lit 2) (colF m (nat_lit 4)))) (selF v (nat_lit 4) (colF m (nat_lit 8))))
    (selF v (nat_lit 8) (colF m (nat_lit 12)))

@[expose] noncomputable def mmulF (a b : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.lor (appF a (colF b (nat_lit 0)))
    (Nat.shiftLeft (appF a (colF b (nat_lit 4))) (nat_lit 4)))
    (Nat.shiftLeft (appF a (colF b (nat_lit 8))) (nat_lit 8)))
    (Nat.shiftLeft (appF a (colF b (nat_lit 12))) (nat_lit 12))

theorem bne_zero_eq (z : ℕ) : (z != 0) = Nat.blt 0 z := by
  cases z <;> rfl

theorem ite_eq_selF (v k c : ℕ) : (if (v &&& k != 0) = true then c else 0) = selF v k c := by
  unfold selF
  have h : (v &&& k != 0) = Nat.blt 0 (Nat.land v k) := bne_zero_eq _
  rw [h]
  cases Nat.blt 0 (Nat.land v k) <;> rfl

theorem appC_eq (m v : ℕ) : appC m v = appF m v := by
  simp only [appC, ite_eq_selF]
  rfl

theorem mmulC_eq (a b : ℕ) : mmulC a b = mmulF a b := by
  simp only [mmulC, appC_eq]
  rfl

@[expose] def stepG (mm : Nat → Nat → Nat) (gens : List Nat) (x : Nat) (st : List Nat × Nat) :
    List Nat × Nat :=
  gens.foldl (fun (acc : List Nat × Nat) g =>
    let y := mm g x
    if acc.2.testBit y then acc else (y :: acc.1, acc.2 ||| (1 <<< y))) st

@[expose] noncomputable def oneF (x g : ℕ) (acc : List ℕ × ℕ) : List ℕ × ℕ :=
  Prod.rec (motive := fun _ => List ℕ × ℕ) (fun l s => forceT s (fun s => forceT (mmulF g x)
    (fun y => Bool.rec (motive := fun _ => List ℕ × ℕ)
      (y :: l, Nat.lor s (Nat.shiftLeft (nat_lit 1) y)) (l, s)
      (Nat.blt (nat_lit 0) (Nat.land (Nat.shiftRight s y) (nat_lit 1)))))) acc

@[expose] noncomputable def stepF (gens : List ℕ) (x : ℕ) (st : List ℕ × ℕ) : List ℕ × ℕ :=
  List.rec (motive := fun _ => List ℕ × ℕ → List ℕ × ℕ) (fun acc => acc)
    (fun g _ ih acc => ih (oneF x g acc)) gens st

theorem testBit_eq (s y : ℕ) :
    s.testBit y = Nat.blt 0 (Nat.land (Nat.shiftRight s y) 1) := by
  have h : (1 &&& s >>> y) = (s >>> y) &&& 1 := Nat.and_comm _ _
  unfold Nat.testBit
  rw [h]
  exact bne_zero_eq _

theorem stepG_eq (mm : ℕ → ℕ → ℕ) (hm : ∀ a b, mm a b = mmulF a b) :
    ∀ (gens : List ℕ) (x : ℕ) (st : List ℕ × ℕ), stepG mm gens x st = stepF gens x st
  | [], _, _ => rfl
  | g :: gs, x, (l, s) => by
    have e : stepG mm (g :: gs) x (l, s) = stepG mm gs x
        (if s.testBit (mm g x) then (l, s) else (mm g x :: l, s ||| (1 <<< mm g x))) := rfl
    have e2 : stepF (g :: gs) x (l, s) = stepF gs x (oneF x g (l, s)) := rfl
    rw [e, e2, stepG_eq mm hm gs x]
    congr 1
    dsimp only [oneF]
    simp only [forceT_eq]
    rw [hm, testBit_eq]
    cases Nat.blt 0 (Nat.land (Nat.shiftRight s (mmulF g x)) 1) <;> rfl

@[expose] noncomputable def frF (gens frontier : List ℕ) (st : List ℕ × ℕ) : List ℕ × ℕ :=
  List.rec (motive := fun _ => List ℕ × ℕ → List ℕ × ℕ) (fun st => st)
    (fun x _ ih st => ih (stepF gens x st)) frontier st

theorem frF_eq (gens : List ℕ) (f : List ℕ × ℕ → ℕ → List ℕ × ℕ)
    (hf : ∀ st x, f st x = stepF gens x st) :
    ∀ (fr : List ℕ) (st : List ℕ × ℕ), fr.foldl f st = frF gens fr st
  | [], _ => rfl
  | x :: xs, st => by
    rw [List.foldl_cons, hf, frF_eq gens f hf xs]
    rfl

@[expose] noncomputable def closAuxF (gens : List ℕ) (fuel : ℕ) :
    List ℕ → List ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ → ℕ → List ℕ) (fun _ all _ => all)
    (fun _ ih frontier all seen =>
      List.rec (motive := fun _ => List ℕ) all
        (fun _ _ _ => Prod.rec (motive := fun _ => List ℕ) (fun f s => ih f (f ++ all) s)
          (frF gens frontier ([], seen))) frontier) fuel

theorem closAuxF_zero (gens f a : List ℕ) (s : ℕ) : closAuxF gens 0 f a s = a := rfl

theorem closAuxF_nil (gens : List ℕ) (n : ℕ) (a : List ℕ) (s : ℕ) :
    closAuxF gens (n + 1) [] a s = a := rfl

theorem closAuxF_succ_cons (gens : List ℕ) (n x : ℕ) (xs a : List ℕ) (s : ℕ) :
    closAuxF gens (n + 1) (x :: xs) a s =
      closAuxF gens n (frF gens (x :: xs) ([], s)).1 ((frF gens (x :: xs) ([], s)).1 ++ a)
        (frF gens (x :: xs) ([], s)).2 := by
  change Prod.rec (motive := fun _ => List ℕ) (fun f s => closAuxF gens n f (f ++ a) s)
    (frF gens (x :: xs) ([], s)) = _
  cases frF gens (x :: xs) ([], s)
  rfl

@[expose] noncomputable def saltF (t y : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.mul (Nat.mod t (nat_lit 18446744073709551616))
    (nat_lit 11400714819323198485)) (Nat.succ y)) (nat_lit 18446744073709551616)

@[expose] noncomputable def oneS (x g : ℕ) (acc : List ℕ × ℕ) : List ℕ × ℕ :=
  Prod.rec (motive := fun _ => List ℕ × ℕ) (fun l t => forceT t (fun t => forceT (mmulF g x)
    (fun y => Bool.rec (motive := fun _ => List ℕ × ℕ)
      (y :: l, Nat.xor (Nat.lor t (Nat.shiftLeft (nat_lit 1) (Nat.add y (nat_lit 64))))
        (Nat.xor (Nat.mod t (nat_lit 18446744073709551616)) (saltF t y))) (l, t)
      (Nat.blt (nat_lit 0) (Nat.land (Nat.shiftRight t (Nat.add y (nat_lit 64))) (nat_lit 1))))))
    acc

@[expose] noncomputable def stepS (gens : List ℕ) (x : ℕ) (st : List ℕ × ℕ) : List ℕ × ℕ :=
  List.rec (motive := fun _ => List ℕ × ℕ → List ℕ × ℕ) (fun acc => acc)
    (fun g _ ih acc => ih (oneS x g acc)) gens st

@[expose] noncomputable def frS (gens frontier : List ℕ) (st : List ℕ × ℕ) : List ℕ × ℕ :=
  List.rec (motive := fun _ => List ℕ × ℕ → List ℕ × ℕ) (fun st => st)
    (fun x _ ih st => ih (stepS gens x st)) frontier st

@[expose] noncomputable def closAuxS (gens : List ℕ) (fuel : ℕ) :
    List ℕ → List ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ → ℕ → List ℕ) (fun _ all _ => all)
    (fun _ ih frontier all seen =>
      List.rec (motive := fun _ => List ℕ) all
        (fun _ _ _ => Prod.rec (motive := fun _ => List ℕ) (fun f s => ih f (f ++ all) s)
          (frS gens frontier ([], seen))) frontier) fuel

def unsalt (st : List ℕ × ℕ) : List ℕ × ℕ := (st.1, st.2 >>> 64)

theorem two_pow_64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by decide

theorem shr_xor_low (u c : ℕ) (hc : c < 18446744073709551616) :
    Nat.xor u c >>> 64 = u >>> 64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hc' : c < 2 ^ (64 + j) := by
    rw [← two_pow_64] at hc
    exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (Nat.le_add_right 64 j))
  have hx : (Nat.xor u c).testBit (64 + j) = (u ^^^ c).testBit (64 + j) := rfl
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, hx, Nat.testBit_xor,
    Nat.testBit_lt_two_pow hc', Bool.xor_false]

theorem shr_lor_bit (t y : ℕ) :
    Nat.lor t (Nat.shiftLeft 1 (Nat.add y 64)) >>> 64 = (t >>> 64) ||| (1 <<< y) := by
  have e : Nat.shiftLeft 1 (Nat.add y 64) = (1 <<< y) <<< 64 := Nat.shiftLeft_add 1 y 64
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro j
  have hx : (Nat.lor t ((1 <<< y) <<< 64)).testBit (64 + j) =
      (t ||| ((1 <<< y) <<< 64)).testBit (64 + j) := rfl
  rw [Nat.testBit_shiftRight, hx, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft]
  simp

theorem mod_salt_lt (t s : ℕ) :
    Nat.xor (Nat.mod t 18446744073709551616) (Nat.mod s 18446744073709551616) <
      18446744073709551616 := by
  rw [← two_pow_64]
  exact Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos 64)) (Nat.mod_lt _ (Nat.two_pow_pos 64))

theorem oneS_unsalt (x g : ℕ) (st : List ℕ × ℕ) : unsalt (oneS x g st) = oneF x g (unsalt st) := by
  obtain ⟨l, t⟩ := st
  have hb : Nat.shiftRight t (Nat.add (mmulF g x) (nat_lit 64)) =
      Nat.shiftRight (t >>> 64) (mmulF g x) := by
    have h := Nat.shiftRight_add t 64 (mmulF g x)
    rw [Nat.add_comm 64 (mmulF g x)] at h
    exact h
  dsimp only [oneS, oneF, unsalt]
  simp only [forceT_eq]
  rw [hb]
  cases Nat.blt (nat_lit 0) (Nat.land (Nat.shiftRight (t >>> 64) (mmulF g x)) (nat_lit 1))
  · have hc : Nat.xor (Nat.mod t 18446744073709551616) (saltF t (mmulF g x)) <
        18446744073709551616 := mod_salt_lt t _
    have h := shr_xor_low (Nat.lor t (Nat.shiftLeft 1 (Nat.add (mmulF g x) 64))) _ hc
    rw [shr_lor_bit] at h
    exact Prod.ext rfl h
  · rfl

theorem stepS_unsalt (gens : List ℕ) (x : ℕ) :
    ∀ st, unsalt (stepS gens x st) = stepF gens x (unsalt st) := by
  induction gens with
  | nil => intro st; rfl
  | cons g gs ih =>
    intro st
    have e : stepS (g :: gs) x st = stepS gs x (oneS x g st) := rfl
    have e2 : stepF (g :: gs) x (unsalt st) = stepF gs x (oneF x g (unsalt st)) := rfl
    rw [e, e2, ih, oneS_unsalt]

theorem frS_unsalt (gens : List ℕ) :
    ∀ (fr : List ℕ) (st : List ℕ × ℕ), unsalt (frS gens fr st) = frF gens fr (unsalt st)
  | [], _ => rfl
  | x :: xs, st => by
    have e : frS gens (x :: xs) st = frS gens xs (stepS gens x st) := rfl
    have e2 : frF gens (x :: xs) (unsalt st) = frF gens xs (stepF gens x (unsalt st)) := rfl
    rw [e, e2, frS_unsalt gens xs, stepS_unsalt]

theorem closAuxS_succ_cons (gens : List ℕ) (n x : ℕ) (xs a : List ℕ) (s : ℕ) :
    closAuxS gens (n + 1) (x :: xs) a s =
      closAuxS gens n (frS gens (x :: xs) ([], s)).1 ((frS gens (x :: xs) ([], s)).1 ++ a)
        (frS gens (x :: xs) ([], s)).2 := by
  change Prod.rec (motive := fun _ => List ℕ) (fun f s => closAuxS gens n f (f ++ a) s)
    (frS gens (x :: xs) ([], s)) = _
  cases frS gens (x :: xs) ([], s)
  rfl

theorem closAuxS_eq (gens : List ℕ) :
    ∀ (fuel : ℕ) (f a : List ℕ) (t : ℕ), closAuxS gens fuel f a t = closAuxF gens fuel f a (t >>> 64)
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, x :: xs, a, t => by
    have h := frS_unsalt gens (x :: xs) ([], t)
    have h1 : (frS gens (x :: xs) ([], t)).1 = (frF gens (x :: xs) ([], t >>> 64)).1 := by
      have h' := congrArg Prod.fst h
      exact h'
    have h2 : (frS gens (x :: xs) ([], t)).2 >>> 64 = (frF gens (x :: xs) ([], t >>> 64)).2 := by
      have h' := congrArg Prod.snd h
      exact h'
    rw [closAuxS_succ_cons, closAuxF_succ_cons, closAuxS_eq gens n, h1, h2]

@[expose] def isPC (x : Nat) : Bool :=
  x < 65536 && (1 ≤ colC x 0 && colC x 0 ≤ 3) && (1 ≤ colC x 1 && colC x 1 ≤ 3) &&
    colC x 0 != colC x 1 && 4 ≤ colC x 2 && 4 ≤ colC x 3 && 4 ≤ (colC x 2 ^^^ colC x 3)

@[expose] def plistK : List ℕ :=
  [18450, 18451, 18465, 18467, 18481, 18482, 18706, 18707, 18721, 18723, 18737, 18738,
    18962, 18963, 18977, 18979, 18993, 18994, 19218, 19219, 19233, 19235, 19249, 19250,
    19474, 19475, 19489, 19491, 19505, 19506, 19730, 19731, 19745, 19747, 19761, 19762,
    19986, 19987, 20001, 20003, 20017, 20018, 20242, 20243, 20257, 20259, 20273, 20274,
    22546, 22547, 22561, 22563, 22577, 22578, 22802, 22803, 22817, 22819, 22833, 22834,
    23058, 23059, 23073, 23075, 23089, 23090, 23314, 23315, 23329, 23331, 23345, 23346,
    23570, 23571, 23585, 23587, 23601, 23602, 23826, 23827, 23841, 23843, 23857, 23858,
    24082, 24083, 24097, 24099, 24113, 24114, 24338, 24339, 24353, 24355, 24369, 24370,
    26642, 26643, 26657, 26659, 26673, 26674, 26898, 26899, 26913, 26915, 26929, 26930,
    27154, 27155, 27169, 27171, 27185, 27186, 27410, 27411, 27425, 27427, 27441, 27442,
    27666, 27667, 27681, 27683, 27697, 27698, 27922, 27923, 27937, 27939, 27953, 27954,
    28178, 28179, 28193, 28195, 28209, 28210, 28434, 28435, 28449, 28451, 28465, 28466,
    30738, 30739, 30753, 30755, 30769, 30770, 30994, 30995, 31009, 31011, 31025, 31026,
    31250, 31251, 31265, 31267, 31281, 31282, 31506, 31507, 31521, 31523, 31537, 31538,
    31762, 31763, 31777, 31779, 31793, 31794, 32018, 32019, 32033, 32035, 32049, 32050,
    32274, 32275, 32289, 32291, 32305, 32306, 32530, 32531, 32545, 32547, 32561, 32562,
    33810, 33811, 33825, 33827, 33841, 33842, 34066, 34067, 34081, 34083, 34097, 34098,
    34322, 34323, 34337, 34339, 34353, 34354, 34578, 34579, 34593, 34595, 34609, 34610,
    35858, 35859, 35873, 35875, 35889, 35890, 36114, 36115, 36129, 36131, 36145, 36146,
    36370, 36371, 36385, 36387, 36401, 36402, 36626, 36627, 36641, 36643, 36657, 36658,
    37906, 37907, 37921, 37923, 37937, 37938, 38162, 38163, 38177, 38179, 38193, 38194,
    38418, 38419, 38433, 38435, 38449, 38450, 38674, 38675, 38689, 38691, 38705, 38706,
    39954, 39955, 39969, 39971, 39985, 39986, 40210, 40211, 40225, 40227, 40241, 40242,
    40466, 40467, 40481, 40483, 40497, 40498, 40722, 40723, 40737, 40739, 40753, 40754,
    42002, 42003, 42017, 42019, 42033, 42034, 42258, 42259, 42273, 42275, 42289, 42290,
    42514, 42515, 42529, 42531, 42545, 42546, 42770, 42771, 42785, 42787, 42801, 42802,
    44050, 44051, 44065, 44067, 44081, 44082, 44306, 44307, 44321, 44323, 44337, 44338,
    44562, 44563, 44577, 44579, 44593, 44594, 44818, 44819, 44833, 44835, 44849, 44850,
    46098, 46099, 46113, 46115, 46129, 46130, 46354, 46355, 46369, 46371, 46385, 46386,
    46610, 46611, 46625, 46627, 46641, 46642, 46866, 46867, 46881, 46883, 46897, 46898,
    48146, 48147, 48161, 48163, 48177, 48178, 48402, 48403, 48417, 48419, 48433, 48434,
    48658, 48659, 48673, 48675, 48689, 48690, 48914, 48915, 48929, 48931, 48945, 48946,
    50194, 50195, 50209, 50211, 50225, 50226, 50450, 50451, 50465, 50467, 50481, 50482,
    50706, 50707, 50721, 50723, 50737, 50738, 50962, 50963, 50977, 50979, 50993, 50994,
    51218, 51219, 51233, 51235, 51249, 51250, 51474, 51475, 51489, 51491, 51505, 51506,
    51730, 51731, 51745, 51747, 51761, 51762, 51986, 51987, 52001, 52003, 52017, 52018,
    54290, 54291, 54305, 54307, 54321, 54322, 54546, 54547, 54561, 54563, 54577, 54578,
    54802, 54803, 54817, 54819, 54833, 54834, 55058, 55059, 55073, 55075, 55089, 55090,
    55314, 55315, 55329, 55331, 55345, 55346, 55570, 55571, 55585, 55587, 55601, 55602,
    55826, 55827, 55841, 55843, 55857, 55858, 56082, 56083, 56097, 56099, 56113, 56114,
    58386, 58387, 58401, 58403, 58417, 58418, 58642, 58643, 58657, 58659, 58673, 58674,
    58898, 58899, 58913, 58915, 58929, 58930, 59154, 59155, 59169, 59171, 59185, 59186,
    59410, 59411, 59425, 59427, 59441, 59442, 59666, 59667, 59681, 59683, 59697, 59698,
    59922, 59923, 59937, 59939, 59953, 59954, 60178, 60179, 60193, 60195, 60209, 60210,
    62482, 62483, 62497, 62499, 62513, 62514, 62738, 62739, 62753, 62755, 62769, 62770,
    62994, 62995, 63009, 63011, 63025, 63026, 63250, 63251, 63265, 63267, 63281, 63282,
    63506, 63507, 63521, 63523, 63537, 63538, 63762, 63763, 63777, 63779, 63793, 63794,
    64018, 64019, 64033, 64035, 64049, 64050, 64274, 64275, 64289, 64291, 64305, 64306]

theorem plist_eq : (List.range 65536).filter isPC = plistK :=
  beq_iff_eq.1 (by decide +kernel)

@[expose] noncomputable def elemF (x : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x a)) L

@[expose] noncomputable def allF (L : List ℕ) (f : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) false ih (f a)) L

@[expose] noncomputable def anyF (L : List ℕ) (f : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (f a)) L

theorem elemF_iff (x : ℕ) : ∀ L : List ℕ, elemF x L = true ↔ x ∈ L
  | [] => by
    have e : elemF x [] = false := rfl
    simp [e]
  | a :: L => by
    have e : elemF x (a :: L) =
        Bool.rec (motive := fun _ => Bool) (elemF x L) true (Nat.beq x a) := rfl
    rw [e, List.mem_cons, ← elemF_iff x L]
    cases h : Nat.beq x a
    · simp [Nat.ne_of_beq_eq_false h]
    · simp [Nat.eq_of_beq_eq_true h]

theorem allF_iff (f : ℕ → Bool) : ∀ L : List ℕ, allF L f = true ↔ ∀ x ∈ L, f x = true
  | [] => by
    have e : allF [] f = true := rfl
    simp [e]
  | a :: L => by
    have e : allF (a :: L) f = Bool.rec (motive := fun _ => Bool) false (allF L f) (f a) := rfl
    rw [e, List.forall_mem_cons, ← allF_iff f L]
    cases f a <;> simp

theorem anyF_iff (f : ℕ → Bool) : ∀ L : List ℕ, anyF L f = true ↔ ∃ x ∈ L, f x = true
  | [] => by
    have e : anyF [] f = false := rfl
    simp [e]
  | a :: L => by
    have e : anyF (a :: L) f = Bool.rec (motive := fun _ => Bool) (anyF L f) true (f a) := rfl
    have ih := anyF_iff f L
    rw [e]
    cases h : f a <;> simp [h, ih]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFinK

end
