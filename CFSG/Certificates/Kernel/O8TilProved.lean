module

public import CFSG.Certificates.Kernel.O8TilDefs
public import CFSG.Certificates.Kernel.O8T0Proved

public section

namespace CFSG.KC.O8.TilPf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8 CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.KC.O8.S0Pf CFSG.KC.O8.Z4Pf CFSG.KC.O8.T0Pf CFSG.EvenSmallLie.UnitarySix.YamadaPar
  CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem fget2_eq (x j : ℕ) : fget x j 2 = x / 4 ^ j % 4 := by
  rw [fget_eq, Nat.shiftRight_eq_div_pow, show 2 ^ (j * 2) = 4 ^ j by rw [Nat.pow_mul'],
    show (2 : ℕ) ^ 2 = 4 by norm_num]

theorem dig4_getD (n : ℕ) {k : ℕ} (hk : k < 6) : (dig4 n).getD k 0 = fget n k 2 := by
  unfold dig4
  rw [getD_ofFn6 _ _ hk, fget2_eq]

theorem orN_lt {w : ℕ} {g : ℕ → ℕ} (hg : ∀ i, g i < 2 ^ w) :
    ∀ n, (orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)) < 2 ^ (w * n)
  | 0 => by
    change 0 < _
    exact Nat.two_pow_pos _
  | n + 1 => by
    change Nat.lor (Nat.shiftLeft (g n) (Nat.mul w n)) (orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)) < _
    apply Nat.or_lt_two_pow (shl_lt (hg n))
    exact Nat.lt_of_lt_of_le (orN_lt hg n) (Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ]; omega))

theorem land3_lt (x : ℕ) : Nat.land x 3 < 2 ^ 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem land3_eq (x : ℕ) : Nat.land x 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

theorem mv4K_lt (A n : ℕ) : mv4K A n < 4096 := by
  have h := orN_lt (w := 2) (g := fun i => Nat.land (sumN 6 fun k => Nat.mul (ent4 A i k) (fget n k 2)) 3)
    (fun i => land3_lt _) 6
  rw [show 2 ^ (2 * 6) = 4096 by norm_num] at h
  exact h

theorem fget_mv4K (A n : ℕ) {i : ℕ} (hi : i < 6) :
    fget (mv4K A n) i 2 = (∑ k ∈ Finset.range 6, ent4 A i k * fget n k 2) % 4 := by
  change fget (orN 6 fun i => Nat.shiftLeft (Nat.land (sumN 6 fun k => Nat.mul (ent4 A i k)
    (fget n k 2)) 3) (Nat.mul 2 i)) i 2 = _
  rw [fget_orN (fun i _ => land3_lt _) hi, land3_eq, sumN_eq]
  rfl

theorem dig4_ext {a b : Array ℕ} (ha : a.size = 6) (hb : b.size = 6)
    (h : ∀ k < 6, a.getD k 0 = b.getD k 0) : a = b := arr6_ext ha hb h

theorem dig4_size (n : ℕ) : (dig4 n).size = 6 := by
  unfold dig4
  exact Array.size_ofFn

theorem mv4_size (A : Array (Array ℕ)) (v : Array ℕ) : (mv4 A v).size = 6 := by
  unfold mv4
  exact Array.size_ofFn

theorem mv4_getD (A : Array (Array ℕ)) (v : Array ℕ) {i : ℕ} (hi : i < 6) :
    (mv4 A v).getD i 0 = (∑ k ∈ Finset.range 6, m4Get A i k * v.getD k 0) % 4 := by
  unfold mv4
  rw [getD_ofFn6 _ _ hi]
  congr 1

theorem dig4_mv4K (A n : ℕ) : dig4 (mv4K A n) = mv4 (dec4M A) (dig4 n) := by
  apply dig4_ext (dig4_size _) (mv4_size _ _)
  intro i hi
  rw [dig4_getD _ hi, fget_mv4K A n hi, mv4_getD _ _ hi]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [m4Get_dec4M A hi (Finset.mem_range.1 hk), dig4_getD _ (Finset.mem_range.1 hk)]

theorem dig4_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : dig4 a = dig4 b) : a = b := by
  have e : ∀ k < 6, a / 4 ^ k % 4 = b / 4 ^ k % 4 := fun k hk => by
    have := congrArg (fun v => Array.getD v k 0) h
    simp only [dig4_getD _ hk, fget2_eq] at this
    exact this
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e5 := e 5 (by norm_num)
  norm_num at e0 e1 e2 e3 e4 e5
  omega

theorem beq_dig4 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) : (dig4 a == dig4 b) = Nat.beq a b := by
  by_cases e : a = b
  · subst e
    rw [beq_self_eq_true, Nat.beq_refl]
  · rw [beq_eq_false_iff_ne.2 (fun h => e (dig4_inj ha hb h))]
    cases h : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) e

theorem mv4_beq {A n m : ℕ} (hn : n < 4096) (hm : m < 4096) :
    (mv4 (dec4M A) (dig4 n) == dig4 m) = Nat.beq (mv4K A n) m := by
  rw [← dig4_mv4K, beq_dig4 (mv4K_lt _ _) hm]

theorem nbeq_eq (a b : ℕ) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · exact (beq_eq_false_iff_ne.2 (fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide))).symm
  · rw [Nat.eq_of_beq_eq_true h, beq_self_eq_true]

theorem dot4K_eq (f v : ℕ) : dot4K f v = dot4 (dig4 f) (dig4 v) := by
  change Nat.land (sumN 6 fun k => Nat.mul (fget f k 2) (fget v k 2)) 3 = _
  rw [land3_eq, sumN_eq]
  unfold dot4
  rw [Fin.sum_univ_eq_sum_range (fun k => (dig4 f).getD k 0 * (dig4 v).getD k 0) 6]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [dig4_getD _ (Finset.mem_range.1 hk), dig4_getD _ (Finset.mem_range.1 hk)]
  rfl

theorem annK_eq (ZA : List ℕ) (A n : ℕ) :
    annK ZA A n = (ZA.map dig4).all fun f => dot4 f (mv4 (dec4M A) (dig4 n)) == 0 := by
  unfold annK
  beta_reduce
  induction ZA with
  | nil => rfl
  | cons f ZA ih =>
    change andB (Nat.beq (dot4K f (mv4K A n)) 0) _ = _
    rw [andB_eq, ih, List.map_cons, List.all_cons, dot4K_eq, dig4_mv4K, nbeq_eq]

theorem dec4M_sub4K (A B : ℕ) : dec4M (sub4K A B) = sub4 (dec4M A) (dec4M B) := by
  unfold sub4
  conv_lhs => unfold dec4M
  apply ofFn66_congr
  intro i j
  change ent4 (strictN A fun A => strictN B fun B =>
    mk fun i j => Nat.add (ent4 A i j) (Nat.mul 3 (ent4 B i j))) i j = _
  rw [strictN_eq, strictN_eq, ent4_mk _ i.2 j.2, m4Get_dec4M A i.2 j.2, m4Get_dec4M B i.2 j.2]
  rfl

theorem red2K_lt (A : ℕ) : red2K A < 2 ^ 36 := by
  have h := orN_lt (w := 6) (g := fun i => orN 6 fun j => Nat.shiftLeft (bitN (ent4 A i j) 0) j)
    (fun i => by simpa using orN6_lt (fun k _ => bitN_lt2 _ _)) 6
  rw [show 6 * 6 = 36 by norm_num] at h
  exact h

theorem red2_dec4M (A : ℕ) : red2 (dec4M A) = decR (red2K A) := by
  apply arr6_ext (by unfold red2; exact Array.size_ofFn) (decR_size _)
  intro i hi
  unfold red2
  rw [getD_ofFn6 _ _ hi, decR_getD _ hi]
  change _ = fget (orN 6 fun i => Nat.shiftLeft (orN 6 fun j => Nat.shiftLeft (bitN (ent4 A i j) 0) j)
    (Nat.mul 6 i)) i 6
  rw [fget_orN (fun i _ => by simpa using orN6_lt (fun k _ => bitN_lt2 _ _)) hi]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitsOf]
  by_cases hj : j < 6
  · rw [decide_eq_true hj, Bool.true_and, testBit_orN6 (fun k _ => bitN_lt2 _ _) hj, m4Get_dec4M A hi hj,
      bitN_eq, toNat_testBit0]
    rcases Nat.mod_two_eq_zero_or_one (ent4 A i j) with h | h <;> rw [h] <;> rfl
  · rw [decide_eq_false hj, Bool.false_and, testBit_lt64 (orN6_lt (fun k _ => bitN_lt2 _ _)) (by omega)]

theorem reflBK_eq {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) {v x : ℕ} (hv : v < 64) (hx : x < 64) :
    reflBK Q v x = reflBG q v x := by
  change Nat.xor x (nIf(Nat.beq (bfK Q x v) (nat_lit 1), v, nat_lit 0)) = _
  have hxv : x ^^^ v < 64 := Nat.xor_lt_two_pow (n := 6) hx hv
  rw [bfK_eq, beq_toNat_one, ← hq _ hxv, ← hq _ hx, ← hq _ hv, nIf_eq]
  unfold reflBG bfG
  rfl

theorem reflRowsK_eq {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) {v : ℕ} (hv : v < 64) :
    decR (reflRowsK Q v) = reflRowsG q v := by
  apply arr6_ext (decR_size _) (by unfold reflRowsG; exact Array.size_ofFn)
  intro i hi
  unfold reflRowsG
  rw [getD_ofFn6 _ _ hi, decR_getD _ hi]
  change fget (orN 6 fun i => Nat.shiftLeft (orN 6 fun j => Nat.shiftLeft (bitN (reflBK Q v (pw2 j)) i) j)
    (Nat.mul 6 i)) i 6 = _
  rw [fget_orN (fun i _ => by simpa using orN6_lt (fun k _ => bitN_lt2 _ _)) hi]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitsOf]
  by_cases hj : j < 6
  · have h2 : 2 ^ j < 64 := by
      have : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [decide_eq_true hj, Bool.true_and, testBit_orN6 (fun k _ => bitN_lt2 _ _) hj, pw2_eq,
      reflBK_eq hq hv h2, bitN_eq]
    cases (reflBG q v (2 ^ j)).testBit i <;> rfl
  · rw [decide_eq_false hj, Bool.false_and, testBit_lt64 (orN6_lt (fun k _ => bitN_lt2 _ _)) (by omega)]

theorem ptilK_eq {GP CP : ℕ} {G C : ℕ → Array ℕ} (hG : ∀ s < 6, G s = decR (mat GP s))
    (hC : ∀ s < 6, C s = decR (mat CP s)) {s : ℕ} (hs : s < 6) :
    dec4M (ptilK GP CP s) = ptil4G G C s := by
  change dec4M (add4K (lift2K (mat GP s)) (add4K (lift2K (mat CP s)) (lift2K (mat CP s)))) =
    add4 (lift2 (G s)) (add4 (lift2 (C s)) (lift2 (C s)))
  rw [dec4M_add4K, dec4M_add4K, dec4M_lift2K, dec4M_lift2K, hG s hs, hC s hs]

theorem wordOf_eq : ∀ (ws : List (List ℕ)) (s : ℕ), wordOf ws s = ws.getD s []
  | [], s => by cases s <;> rfl
  | _ :: _, 0 => rfl
  | w :: ws, s + 1 => by
    change wordOf ws s = _
    rw [wordOf_eq ws s]
    rfl

theorem sumN_add (g : ℕ → ℕ) (a : ℕ) : ∀ b, sumN (a + b) g = sumN b (fun l => g (a + l)) + sumN a g
  | 0 => by
    change sumN a g = 0 + sumN a g
    rw [Nat.zero_add]
  | b + 1 => by
    change Nat.add (g (a + b)) (sumN (a + b) g) = Nat.add (g (a + b)) (sumN b fun l => g (a + l)) + sumN a g
    rw [sumN_add g a b]
    simp only [Nat.add_eq]
    ring

theorem sumBelow_sumN (m : ℕ) (f : ℕ → ℕ) : ∀ hi,
    sumBelow m hi f = sumN (64 * hi) fun i => nIf(Nat.blt i m, f i, 0)
  | 0 => rfl
  | hi + 1 => by
    change Nat.add (sumN 64 fun l => (fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft hi 6) l))
      (sumBelow m hi f) = _
    rw [sumBelow_sumN m f hi, show 64 * (hi + 1) = 64 * hi + 64 by ring, sumN_add]
    have e : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq]
      ring
    simp only [e, Nat.add_eq]

theorem sumN_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (f n) (sumN n f) = Nat.add (g n) (sumN n g)
    rw [h n (by omega), ih (fun i hi => h i (by omega))]

theorem sum4096 (p : ℕ → Bool) :
    sumBelow 4096 64 (fun n => nIf(p n, nat_lit 1, nat_lit 0)) = ((List.range 4096).filter p).length := by
  rw [sumBelow_sumN, ← sumN_ind]
  apply sumN_congr
  intro i hi
  rw [nIf_eq, if_pos (by rw [Nat.blt_eq]; omega)]

theorem mtAt_lt (MT i j : ℕ) : mtAt MT i j < 128 := fget_lt _ _ 7

theorem close_of {TL MT : ℕ} (hc : ∀ c < 16, closeOK TL MT c = true) {i j : ℕ} (hi : i < 128)
    (hj : j < 128) : tilAt TL (mtAt MT i j) = mul4K (tilAt TL i) (tilAt TL j) := by
  have h1 := allN_iff.1 (hc (i / 8) (by omega)) (i % 8) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h1
  rw [show Nat.add (Nat.mul 8 (i / 8)) (i % 8) = i by change 8 * (i / 8) + i % 8 = i; omega,
    strictN_eq] at h1
  exact Nat.eq_of_beq_eq_true (allN_iff.1 (nIf_one h1) j hj)

theorem red2Tab_get (TL : ℕ) {i : ℕ} (hi : i < 128) : fget (red2Tab TL) i 36 = red2K (tilAt TL i) :=
  fget_orN (fun i _ => red2K_lt _) hi

structure TabFacts (G C U X : ℕ) (UW : List (List ℕ)) (TL MT XI UI : ℕ) : Prop where
  one : tilAt TL 0 = ONE
  xi : XI < 128
  x : tilAt TL XI = X
  gens : ∀ k < 6, lettersOK (UW.getD k []) = true ∧ wordRowsK G (UW.getD k []) = mat U k ∧
    fget UI k 7 < 128 ∧ tilAt TL (fget UI k 7) = prod4K G C (UW.getD k [])
  dist : ∀ i < 128, ∀ j < i, red2K (tilAt TL i) ≠ red2K (tilAt TL j)

theorem tabFacts {G C U X : ℕ} {UW : List (List ℕ)} {TL MT XI UI : ℕ}
    (h : tabOK G C U X UW TL MT XI UI = true) : TabFacts G C U X UW TL MT XI UI := by
  unfold tabOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, ⟨hxi, hx⟩, hg, hd⟩ := h
  rw [Nat.blt_eq] at hxi
  refine ⟨Nat.eq_of_beq_eq_true h0, hxi, Nat.eq_of_beq_eq_true hx, fun k hk => ?_, ?_⟩
  · have h1 := allN_iff.1 hg k hk
    beta_reduce at h1
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, wordOf_eq, Nat.blt_eq] at h1
    obtain ⟨a, b, c, d⟩ := h1
    exact ⟨a, Nat.eq_of_beq_eq_true b, c, Nat.eq_of_beq_eq_true d⟩
  · intro i hi j hj
    rw [strictN_eq] at hd
    have h1 := allN_iff.1 (allN_iff.1 (nIf_one hd) i hi) j hj
    rw [notB_eq, Bool.not_eq_true', red2Tab_get TL hi, red2Tab_get TL (by omega)] at h1
    intro e
    rw [e, Nat.beq_refl] at h1
    exact absurd h1 (by decide)

theorem red2_ne {G C U X : ℕ} {UW : List (List ℕ)} {TL MT XI UI : ℕ}
    (hf : TabFacts G C U X UW TL MT XI UI) {i j : ℕ} (hi : i < 128) (hj : j < 128) (hij : i ≠ j) :
    red2K (tilAt TL i) ≠ red2K (tilAt TL j) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact fun e => hf.dist j hj i h e.symm
  · exact hf.dist i hi j h

theorem til_inj {T : Array (Array ℕ)} {TL : ℕ} (hT : TilBind T TL) {G C U X : ℕ} {UW : List (List ℕ)}
    {MT XI UI : ℕ} (hf : TabFacts G C U X UW TL MT XI UI) {i j : ℕ} (hi : i < 128) (hj : j < 128)
    (e : tilGetG T i = tilGetG T j) : i = j := by
  by_contra hij
  apply red2_ne hf hi hj hij
  apply decR_inj (red2K_lt _) (red2K_lt _)
  rw [← red2_dec4M, ← red2_dec4M, ← hT.2 i hi, ← hT.2 j hj, e]

theorem idx_lt {T : Array (Array ℕ)} {M : Array (Array ℕ)} {i : ℕ} (hi : i < 128)
    (h : tilGetG T i = M) : tilIdxG T M < 128 := by
  unfold tilIdxG
  cases e : List.find? (fun i => tilGetG T i == M) (List.range 128) with
  | none =>
    rw [List.find?_eq_none] at e
    exact absurd (by rw [h]; exact beq_self_eq_true M) (e i (List.mem_range.2 hi))
  | some a => exact List.mem_range.1 (List.mem_of_find?_eq_some e)

theorem fix4_eq (A : ℕ) : fix4c (dec4M A) = fix4K A := by
  unfold fix4K
  rw [strictN_eq, sum4096]
  unfold fix4c
  exact congrArg List.length (List.filter_congr fun n hn =>
    mv4_beq (List.mem_range.1 hn) (List.mem_range.1 hn))

theorem fix2_eq (R : ℕ) : fix2c (decR R) = fix2K R := by
  unfold fix2K
  rw [sumN_ind]
  unfold fix2c
  exact congrArg List.length (List.filter_congr fun x _ => by rw [bvecK_eq, nbeq_eq])

end CFSG.KC.O8.TilPf

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.KC.O8.S0Pf CFSG.KC.O8.Z4Pf CFSG.KC.O8.T0Pf CFSG.KC.O8.TilPf
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem til_sound_proved {q : ℕ → Bool} {n0 : ℕ} {G C U : ℕ → Array ℕ} {X : Array ℕ}
    {RW UW : List (List ℕ)} {T : Array (Array ℕ)} {z : ℕ} {Q GP CP UP XP TL MT XI UI : Nat}
    (hq : QBind q Q) (hn : n0 < 64) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hC : ∀ s < 6, C s = decR (mat CP s)) (hU : ∀ k < 6, U k = decR (mat UP k))
    (hX : dec4 X = dec4M XP) (hT : TilBind T TL)
    (hx : xOK Q n0 GP CP XP RW = true) (ht : tabOK GP CP UP XP UW TL MT XI UI = true)
    (hc : ∀ c < 16, closeOK TL MT c = true) (hi : ∀ c < 16, invOK TL MT z c = true) :
    tilCheckG q n0 G C U X RW UW T z = true := by
  have hf := tabFacts ht
  have hTi : ∀ i < 128, tilGetG T i = dec4M (tilAt TL i) := hT.2
  have hmul : ∀ i < 128, ∀ j < 128, mul4 (tilGetG T i) (tilGetG T j) = tilGetG T (mtAt MT i j) :=
    fun i hi j hj => by
      rw [hTi i hi, hTi j hj, hTi _ (mtAt_lt _ _ _), close_of hc hi hj, dec4M_mul4K]
  unfold tilCheckG
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    unfold xOK at hx
    rw [strictN_eq, nIf_eq] at hx
    have hx' : (andB (Nat.beq (mul4K XP XP) ONE) (andB (Nat.beq (red2K XP) (reflRowsK Q n0))
        (allN 6 fun s => (fun w => andB (lettersOK w)
          (andB (Nat.beq (mul4K (mul4K XP (ptilK GP CP s)) XP) (prod4K GP CP w))
            (Nat.beq (wordRowsK GP w) (bmulK (reflRowsK Q n0) (bmulK (mat GP s) (reflRowsK Q n0))))))
          (wordOf RW s)))) = true := by
      by_contra hne
      rw [if_neg hne] at hx
      exact absurd hx (by decide)
    simp only [andB_eq, Bool.and_eq_true] at hx'
    obtain ⟨h1, h2, h3⟩ := hx'
    unfold xCheckG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, fun s hs => ?_⟩
    · rw [hX, ← dec4M_mul4K, Nat.eq_of_beq_eq_true h1, dec4M_ONE]
    · rw [hX, red2_dec4M, Nat.eq_of_beq_eq_true h2, reflRowsK_eq hq hn]
    · have h4 := allN_iff.1 h3 s hs
      beta_reduce at h4
      rw [Bool.and_eq_true, Bool.and_eq_true, wordOf_eq] at h4
      obtain ⟨hl, h5, h6⟩ := h4
      have hl' := letters_of hl
      refine ⟨?_, ?_⟩
      · rw [hX, ← ptilK_eq hG hC hs, ← dec4M_mul4K, ← dec4M_mul4K, Nat.eq_of_beq_eq_true h5,
          prod4K_eq hG hC _ hl']
      · rw [← wordRowsK_eq hG _ hl', Nat.eq_of_beq_eq_true h6, decR_bmulK, decR_bmulK,
          reflRowsK_eq hq hn, hG s hs]
  ·
    unfold tabCheckG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
      Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨?_, ?_⟩, fun k hk => ?_⟩, fun i hi j hj => ?_⟩, fun i hi j hj => ?_⟩
    · rw [hTi 0 (by norm_num), hf.one, dec4M_ONE]
    · exact idx_lt hf.xi (by rw [hTi _ hf.xi, hf.x, hX])
    · obtain ⟨hl, hw, hu, hp⟩ := hf.gens k hk
      refine ⟨?_, idx_lt hu (by rw [hTi _ hu, hp, prod4K_eq hG hC _ (letters_of hl)])⟩
      rw [← wordRowsK_eq hG _ (letters_of hl), hw, hU k hk]
    · exact idx_lt (mtAt_lt MT i j) (hmul i hi j hj).symm
    · by_cases hij : i = j
      · exact Or.inl hij
      · right
        rw [hTi i hi, hTi j hj, red2_dec4M, red2_dec4M, decR_beq (red2K_lt _) (red2K_lt _)]
        cases e : Nat.beq (red2K (tilAt TL i)) (red2K (tilAt TL j))
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) (red2_ne hf hi hj hij)
  ·
    unfold invCheckSG
    rw [List.all_eq_true]
    intro i hi'
    have hi1 := List.mem_range.1 hi'
    have h1 := allN_iff.1 (hi (i / 8) (by omega)) (i % 8) (Nat.mod_lt _ (by norm_num))
    rw [show Nat.add (Nat.mul 8 (i / 8)) (i % 8) = i by change 8 * (i / 8) + i % 8 = i; omega] at h1
    unfold invAt at h1
    beta_reduce at h1
    have hinv : isInvol4 (tilGetG T i) = andB (Nat.beq (red2K (tilAt TL (mtAt MT i i))) ID6)
        (notB (Nat.beq (red2K (tilAt TL i)) ID6)) := by
      unfold isInvol4
      rw [hmul i hi1 i hi1, hTi _ (mtAt_lt _ _ _), hTi i hi1, red2_dec4M, red2_dec4M, ← decR_ID6,
        decR_beq (red2K_lt _) (by decide), decR_beq (red2K_lt _) (by decide), andB_eq, notB_eq]
    dsimp only
    rw [hinv]
    rw [orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h1
    rw [Bool.or_eq_true, Bool.not_eq_true']
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · right
      rw [strictN_eq] at h1
      have h2 := nIf_one h1
      rw [andB_eq, orB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, Nat.blt_eq,
        Nat.blt_eq, Nat.blt_eq] at h2
      obtain ⟨h3, h4⟩ := h2
      have hcent : centcG T (tilGetG T i) = centK MT i := by
        unfold centK
        rw [sumN_ind]
        unfold centcG
        refine congrArg List.length (List.filter_congr fun j hj => ?_)
        have hj' := List.mem_range.1 hj
        rw [hmul i hi1 j hj', hmul j hj' i hi1, nbeq_eq]
        by_cases e : mtAt MT i j = mtAt MT j i
        · rw [e, beq_self_eq_true, beq_self_eq_true]
        · rw [beq_eq_false_iff_ne.2 e, beq_eq_false_iff_ne.2 (fun h' => e
            (til_inj hT hf (mtAt_lt _ _ _) (mtAt_lt _ _ _) h'))]
      have e2 : fix2c (red2 (tilGetG T i)) = fix2K (red2K (tilAt TL i)) := by
        rw [hTi i hi1, red2_dec4M, fix2_eq]
      have e4 : fix4c (tilGetG T i) = fix4K (tilAt TL i) := by
        rw [hTi i hi1, fix4_eq]
      have g1 : 128 * fix2c (red2 (tilGetG T i)) < 64 * fix4c (tilGetG T i) := by
        rw [e2, e4]
        exact h3
      have g2 : (i = z ∨ 256 < 2 * fix4c (tilGetG T i)) ∨
          2 * fix4c (tilGetG T i) * centcG T (tilGetG T i) < 16384 := by
        rw [e4, hcent]
        rcases h4 with h4 | h4 | h4
        · exact Or.inl (Or.inl (Nat.eq_of_beq_eq_true h4))
        · exact Or.inl (Or.inr h4)
        · exact Or.inr h4
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨g1, g2⟩

theorem TilPf.wMask_of {SW : List ℕ} {n : ℕ} (h : (wMask SW).testBit n = true) :
    ∃ x ∈ SW, Nat.land x 4095 = n := by
  induction SW with
  | nil => exact absurd h (by simp [wMask])
  | cons x SW ih =>
    change (pw2 (Nat.land x 4095) ||| wMask SW).testBit n = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_pw2, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨y, hy, e⟩ := ih h
      exact ⟨y, by simp [hy], e⟩

theorem TilPf.listRec_all (f : ℕ → Bool) : ∀ SW : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun x _ ih => f x && ih) SW = true → ∀ x ∈ SW, f x = true
  | [], _, x, hx => absurd hx (by simp)
  | y :: SW, h, x, hx => by
    change (f y && List.rec (motive := fun _ => Bool) true (fun x _ ih => f x && ih) SW) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact TilPf.listRec_all f SW h.2 x hx

theorem TilPf.sumN_add2 (n : ℕ) (f g : ℕ → ℕ) :
    sumN n (fun j => Nat.add (f j) (g j)) = sumN n f + sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (Nat.add (f n) (g n)) (sumN n _) = Nat.add (f n) (sumN n f) + Nat.add (g n) (sumN n g)
    rw [ih]
    simp only [Nat.add_eq]
    ring

theorem z_sound_proved {G C : ℕ → Array ℕ} {X : Array ℕ} {UW : List (List ℕ)} {T : Array (Array ℕ)}
    {tr : Array (ℕ × ℕ)} {z r : ℕ} {ann : List (Array ℕ)} {wit : List (ℕ × ℕ × Bool)}
    {GP CP UP XP TL MT XI UI TR WM : Nat} {ZA SW : List ℕ}
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hX : dec4 X = dec4M XP) (hT : TilBind T TL)
    (htr : ∀ i < 128, tr.getD i (0, 0) = (fget TR i 10 % 128, fget TR i 10 / 128))
    (ha : ann = ZA.map dig4)
    (hw : wit = SW.map fun x => (x % 4096, x / 4096 % 4096, x / 16777216 == 1))
    (ht : tabOK GP CP UP XP UW TL MT XI UI = true) (hc : ∀ c < 16, closeOK TL MT c = true)
    (h : zOK GP CP XP UW TL MT TR z r ZA SW WM = true)
    (hf : ∀ c < 16, zFinOK TL z ZA WM c = true) :
    zCheckG G C X UW T tr z r ann wit = true := by
  have hfa := tabFacts ht
  have hTi : ∀ i < 128, tilGetG T i = dec4M (tilAt TL i) := hT.2
  have hmul : ∀ i < 128, ∀ j < 128, mul4 (tilGetG T i) (tilGetG T j) = tilGetG T (mtAt MT i j) :=
    fun i hi j hj => by
      rw [hTi i hi, hTi j hj, hTi _ (mtAt_lt _ _ _), close_of hc hi hj, dec4M_mul4K]
  unfold zOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨htree, ⟨hz, hr⟩, hzc, hrr, hrest⟩ := h
  rw [Nat.blt_eq] at hz hr
  rw [strictN_eq, strictN_eq, strictN_eq, strictN_eq, strictN_eq, nIf_eq] at hrest
  have key : ∀ b : Bool, Nat.beq 1 (if b = true then 1 else 0) = true → b = true := by
    intro b hb
    cases b
    · exact absurd hb (by decide)
    · rfl
  have hrest' := key _ hrest
  simp only [Bool.and_eq_true] at hrest'
  obtain ⟨hfix, hann, hwit, hwm⟩ := hrest'
  have hTz := hTi z hz
  have hTr := hTi r hr
  unfold zCheckG
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨(fun i hi => ?_), (fun j hj => ?_)⟩, ?_⟩, hz⟩, hr⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    have h1 := allN_iff.1 htree i hi
    beta_reduce at h1
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h1
    obtain ⟨h2, h3, h4⟩ := h1
    have e7 : Nat.land (fget TR (Nat.succ i) 10) 127 = fget TR (i + 1) 10 % 128 :=
      Nat.and_two_pow_sub_one_eq_mod _ 7
    have e3 : Nat.shiftRight (fget TR (Nat.succ i) 10) 7 = fget TR (i + 1) 10 / 128 :=
      Nat.shiftRight_eq_div_pow _ 7
    rw [e7] at h2 h4
    rw [e3] at h3 h4
    have hgen : tilGenG G C X UW (fget TR (i + 1) 10 / 128) =
        dec4M (tilGenK GP CP XP UW (fget TR (i + 1) 10 / 128)) := by
      unfold tilGenK tilGenG
      rw [nIf_eq]
      by_cases hg : fget TR (i + 1) 10 / 128 < 6
      · rw [if_pos hg, if_pos (by rw [Nat.blt_eq]; exact hg), wordOf_eq,
          prod4K_eq hG hC _ (letters_of (hfa.gens _ hg).1)]
      · rw [if_neg hg, if_neg (by rw [Nat.blt_eq]; exact hg), hX]
    rw [htr (i + 1) (by omega)]
    refine ⟨⟨h2, h3⟩, ?_⟩
    dsimp only
    rw [hTi _ (by omega), hTi _ (by omega), hgen, ← dec4M_mul4K, ← Nat.eq_of_beq_eq_true h4]
  ·
    rw [hmul z hz j hj, hmul j hj z hz, Nat.eq_of_beq_eq_true (allN_iff.1 hzc j hj)]
  · rw [hTz, fix4_eq, Nat.eq_of_beq_eq_true hfix]
  · rw [hmul r hr r hr, Nat.eq_of_beq_eq_true hrr]
  ·
    intro f hf' n hn
    rw [ha] at hf'
    have h1 := allBelow_spec' hann (by norm_num) n hn
    rw [annK_eq, List.all_eq_true] at h1
    have h2 := h1 f hf'
    rw [dec4M_sub4K, dec4M_ONE, ← hTz] at h2
    exact beq_iff_eq.1 h2
  ·
    intro w hw'
    rw [hw, List.mem_map] at hw'
    obtain ⟨x, hx, rfl⟩ := hw'
    have h2 := TilPf.listRec_all _ SW hwit x hx
    beta_reduce at h2
    have e1 : Nat.land x 4095 = x % 4096 := Nat.and_two_pow_sub_one_eq_mod _ 12
    have e2 : Nat.land (Nat.shiftRight x 12) 4095 = x / 4096 % 4096 := by
      change (x >>> 12) &&& (2 ^ 12 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    have e3 : Nat.beq (Nat.shiftRight x 24) 1 = (x / 16777216 == 1) := by
      rw [nbeq_eq]
      change (x >>> 24 == 1) = _
      rw [Nat.shiftRight_eq_div_pow]
    rw [e1, e2, e3, nIf_eq] at h2
    dsimp only
    rw [hTr]
    by_cases hb : (x / 16777216 == 1) = true
    · rw [if_pos hb] at h2
      rw [if_pos hb, ← dec4M_ONE, ← dec4M_add4K]
      exact beq_iff_eq.1 ((mv4_beq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))).trans h2)
    · rw [if_neg hb] at h2
      rw [if_neg hb, ← dec4M_ONE, ← dec4M_sub4K]
      exact beq_iff_eq.1 ((mv4_beq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))).trans h2)
  ·
    intro n hn
    have h1 := hf (n / 256) (by omega)
    unfold zFinOK at h1
    rw [strictN_eq] at h1
    have h2 := allN_iff.1 (nIf_one h1) (n % 256) (Nat.mod_lt _ (by norm_num))
    beta_reduce at h2
    rw [show Nat.add (Nat.mul 256 (n / 256)) (n % 256) = n by change 256 * (n / 256) + n % 256 = n; omega]
      at h2
    rw [orB_eq, orB_eq, notB_eq, Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2 | h2
    · left
      left
      rw [hTz, ← dec4M_ONE, ← dec4M_add4K, mv4_beq hn (by norm_num)]
      exact h2
    · left
      right
      rw [bit_eq, Nat.eq_of_beq_eq_true hwm |>.symm] at h2
      obtain ⟨x, hx, e⟩ := TilPf.wMask_of h2
      refine ⟨(x % 4096, x / 4096 % 4096, x / 16777216 == 1), by rw [hw]; exact List.mem_map_of_mem hx, ?_⟩
      dsimp only
      rw [← (Nat.and_two_pow_sub_one_eq_mod x 12 : Nat.land x 4095 = x % 4096)]
      exact e
    · right
      rw [Nat.ble_eq] at h2
      refine le_of_eq_of_le ?_ h2
      unfold zCountK
      rw [TilPf.sumN_add2]
      unfold zCountG
      have e : ∀ (b : ℕ → Bool), sumN 128 (fun j => nIf(b j, nat_lit 1, nat_lit 0)) =
          ((List.range 128).filter b).length := fun b => sumN_ind 128 b
      rw [← e, ← e]
      refine congrArg₂ (· + ·) (sumN_congr fun j hj => ?_) (sumN_congr fun j hj => ?_)
      · rw [annK_eq, dec4M_sub4K, dec4M_ONE, ← hTi j hj, ha]
      · rw [annK_eq, dec4M_add4K, dec4M_ONE, ← hTi j hj, ha]

end CFSG.KC.O8

end
