module

public import CFSG.Certificates.Kernel.O8ChainDefs
public import CFSG.Certificates.Kernel.O8WordProved
public import Certificates.Data.Kernel.O8.S0

public section

namespace CFSG.KC.O8.S0Pf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.O8 CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem anyN_eq (n : Nat) (f : Nat → Bool) : anyN n f = (List.range n).any f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change orB (f n) (anyN n f) = _
    rw [orB_eq, ih, List.range_succ, List.any_append, Bool.or_comm]
    simp

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h i hi => h i (List.mem_range.1 hi)⟩

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  rw [anyN_eq, List.any_eq_true]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.1 hi, h⟩, fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.2 hi, h⟩⟩

theorem nIf_one {c : Bool} (h : Nat.beq 1 (nIf(c, nat_lit 1, nat_lit 0)) = true) : c = true := by
  cases c
  · exact absurd h (by decide)
  · rfl

theorem fget_fget {X i j : ℕ} (hj : j < 64) : fget (fget X i 384) j 6 = fget X (64 * i + j) 6 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_fget, testBit_fget, testBit_fget]
  by_cases hp : p < 6
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_and, decide_eq_true (by omega : j * 6 + p < 384),
      Bool.true_and]
    congr 1
    ring
  · simp [hp]

theorem rowMT_get {MT i j : ℕ} (hj : j < 64) : fget (rowMT MT i) j 6 = tget MT i j :=
  fget_fget hj

theorem tget_lt (MT i j : ℕ) : tget MT i j < 64 := fget_lt _ _ 6

theorem getElem_eq {S : Array (Array ℕ)} {L : ℕ} (hL : S0Bind S L) {j : ℕ} (hj : j < 64) :
    S[j]'(by rw [hL.1]; exact hj) = decR (mat L j) := by
  rw [← hL.2 j hj, s0GetG, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
  rfl

theorem distinct_of {L : ℕ} (hd : distinctOK L = true) {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (hij : i ≠ j) : mat L i ≠ mat L j := by
  unfold distinctOK at hd
  have h1 := allN_iff.1 hd i hi
  have h2 := allN_iff.1 h1 j hj
  rw [orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact absurd (Nat.eq_of_beq_eq_true h2) hij
  · intro e
    rw [e, Nat.beq_refl] at h2
    exact absurd h2 (by decide)

theorem mt_of {L MT : ℕ} (hm : mtOK L MT = true) {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    mat L (tget MT i j) = bmulK (mat L i) (mat L j) := by
  unfold mtOK at hm
  have h1 := allN_iff.1 hm i hi
  rw [strictN_eq] at h1
  have h2 := allN_iff.1 (nIf_one h1) j hj
  rw [rowMT_get hj] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem idx_eq {S : Array (Array ℕ)} {L : ℕ} (hL : S0Bind S L) (hd : distinctOK L = true) {k : ℕ}
    (hk : k < 64) : s0IdxG S (decR (mat L k)) = k := by
  unfold s0IdxG
  have e : S.findIdx? (· == decR (mat L k)) = some k := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨by rw [hL.1]; exact hk, ?_, ?_⟩
    · rw [getElem_eq hL hk]
      exact beq_self_eq_true _
    · intro j hjk
      rw [getElem_eq hL (by omega)]
      intro h
      exact distinct_of hd (by omega) hk (by omega) (decR_inj (mat_lt _ _) (mat_lt _ _) (eq_of_beq h))
  rw [e]
  rfl

theorem getD_ofFn64 {α : Type} (f : Fin 64 → α) (d : α) {i : ℕ} (hi : i < 64) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem table_eq {S : Array (Array ℕ)} {L MT : ℕ} (hL : S0Bind S L) (hd : distinctOK L = true)
    (hm : mtOK L MT = true) {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    tabGet (mulTabG S) i j = tget MT i j := by
  unfold tabGet mulTabG
  rw [getD_ofFn64 _ _ hi, getD_ofFn64 _ _ hj]
  dsimp only
  rw [hL.2 i hi, hL.2 j hj, ← decR_bmulK, ← mt_of hm hi hj, idx_eq hL hd (tget_lt _ _ _)]

theorem s0Get_lt {S : Array (Array ℕ)} {L : ℕ} (hL : S0Bind S L) {k : ℕ} (hk : k < 64) :
    s0GetG S k = decR (mat L k) := hL.2 k hk

theorem testBit_orN_shl {w n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 2 ^ w) {j p : ℕ} (hj : j < n)
    (hp : p < w) : (orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)).testBit (w * j + p) =
      (g j).testBit p := by
  rw [Bool.eq_iff_iff, testBit_orN_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    change (g i <<< (w * i)).testBit (w * j + p) = true at h
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      have h1 : w ≤ w * j + p - w * i := by
        have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w hlt
        rw [Nat.mul_succ] at this
        omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg i hi) (Nat.pow_le_pow_right (by omega) h1))]
        at h
      exact absurd h.2 (by decide)
    · rw [show w * i + p - w * i = p by omega] at h
      exact h.2
    · exfalso
      have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w hgt
      rw [Nat.mul_succ] at this
      omega
  · intro h
    refine ⟨j, hj, ?_⟩
    change (g j <<< (w * j)).testBit (w * j + p) = true
    rw [Nat.testBit_shiftLeft, show w * j + p - w * j = p by omega, h]
    simp

theorem fget_orN {w n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 2 ^ w) {j : ℕ} (hj : j < n) :
    fget (orN n fun i => Nat.shiftLeft (g i) (Nat.mul w i)) j w = g j := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_fget]
  by_cases hp : p < w
  · rw [decide_eq_true hp, Bool.true_and, Nat.mul_comm j w, testBit_orN_shl hg hj hp]
  · rw [decide_eq_false hp, Bool.false_and,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg j hj) (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem popc_eq (x : ℕ) : ∀ n, popc n x = ((List.range n).filter fun a => x.testBit a).length
  | 0 => rfl
  | n + 1 => by
    change bitN x n + popc n x = _
    rw [popc_eq x n, bitN_eq, List.range_succ, List.filter_append, List.length_append]
    cases h : x.testBit n <;> simp [h, Nat.add_comm]

theorem colMT_get {MT y a : ℕ} (ha : a < 64) : fget (colMT MT y) a 6 = tget MT a y :=
  fget_orN (fun i _ => tget_lt MT i y) ha

theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := beq_bitN X i

theorem testBit_pw2 (a p : ℕ) : (pw2 a).testBit p = decide (a = p) := by
  rw [pw2_eq, Nat.testBit_two_pow]

theorem testBit_commMask {R Cc a : ℕ} (ha : a < 64) :
    (commMask R Cc).testBit a = (fget Cc a 6 == fget R a 6) := by
  rw [Bool.eq_iff_iff, commMask, testBit_orN_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [nIf_eq] at h
    split at h
    · rename_i hc
      rw [testBit_pw2, decide_eq_true_eq] at h
      subst h
      rwa [beq_iff_eq, ← Nat.beq_eq]
    · exact absurd h (by simp)
  · intro h
    refine ⟨a, ha, ?_⟩
    rw [nIf_eq, if_pos (by rw [Nat.beq_eq]; exact beq_iff_eq.1 h), testBit_pw2]
    simp

theorem testBit_imgK {Cc m p : ℕ} :
    (imgK Cc m).testBit p = true ↔ ∃ a < 64, m.testBit a = true ∧ fget Cc a 6 = p := by
  rw [imgK, testBit_orN_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [nIf_eq] at h
    split at h
    · rename_i hc
      rw [testBit_pw2, decide_eq_true_eq] at h
      refine ⟨a, ha, ?_, h⟩
      rw [← hc, bit_eq]
    · exact absurd h (by simp)
  · rintro ⟨a, ha, hm, hp⟩
    refine ⟨a, ha, ?_⟩
    have hb : bit m a = true := by
      rw [bit_eq]
      exact hm
    rw [nIf_eq, if_pos hb, testBit_pw2, hp]
    simp

theorem imgK_eq {S : Array (Array ℕ)} {L MT : ℕ} (hL : S0Bind S L) (hd : distinctOK L = true)
    (hm : mtOK L MT = true) {y : ℕ} (hy : y < 64) (m : ℕ) :
    imgK (colMT MT y) m = imgMask (mulTabG S) m y := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Bool.eq_iff_iff, testBit_imgK, imgMask, testBit_bitsOf]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨a, ha, hma, hp⟩
    rw [colMT_get ha] at hp
    refine ⟨by rw [← hp]; exact tget_lt _ _ _, a, ha, hma, ?_⟩
    rw [table_eq hL hd hm ha hy, hp]
  · rintro ⟨-, a, ha, hma, he⟩
    exact ⟨a, ha, hma, by rw [colMT_get ha, ← table_eq hL hd hm ha hy, he]⟩

theorem closeK_eq {S : Array (Array ℕ)} {L MT : ℕ} (hL : S0Bind S L) (hd : distinctOK L = true)
    (hm : mtOK L MT = true) {y : ℕ} (hy : y < 64) (m : ℕ) :
    closeK (colMT MT y) m = closeY (mulTabG S) y 8 m := by
  suffices h : ∀ n m, Nat.rec (motive := fun _ => ℕ → ℕ) (fun m => m)
      (fun _ ih m => strictN (Nat.lor m (imgK (colMT MT y) m)) ih) n m = closeY (mulTabG S) y n m from
    h 8 m
  intro n
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
    intro m
    change strictN (Nat.lor m (imgK (colMT MT y) m)) _ = closeY (mulTabG S) y n (m ||| imgMask (mulTabG S) m y)
    rw [strictN_eq, imgK_eq hL hd hm hy]
    exact ih _

theorem testBit_fixAll {F m z : ℕ} (hz : z < 64) :
    (fixAll F m).testBit z = true ↔ ∀ a < 64, m.testBit a = true → (fget F a 64).testBit z = true := by
  suffices h : ∀ n, (Nat.rec (motive := fun _ => Nat) (maskN 64)
      (fun a ih => strictN ih fun acc => nIf(bit m a, Nat.land acc (fget F a (nat_lit 64)), acc))
        n).testBit z = true ↔ ∀ a < n, m.testBit a = true → (fget F a 64).testBit z = true from h 64
  intro n
  induction n with
  | zero =>
    change (maskN 64).testBit z = true ↔ _
    rw [testBit_mask64, decide_eq_true_eq]
    simp [hz]
  | succ n ih =>
    change (strictN _ fun acc => nIf(bit m n, Nat.land acc (fget F n (nat_lit 64)), acc)).testBit z = true ↔ _
    rw [strictN_eq, nIf_eq, bit_eq]
    by_cases hb : m.testBit n = true
    · rw [if_pos hb, testBit_land, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ a ha hma
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · exact h1 a ha hma
        · exact h2
      · intro h
        exact ⟨fun a ha hma => h a (by omega) hma, h n (by omega) hb⟩
    · rw [if_neg hb, ih]
      constructor
      · intro h a ha hma
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · exact h a ha hma
        · exact absurd hma hb
      · intro h a ha hma
        exact h a (by omega) hma

theorem fix_of {S : Array (Array ℕ)} {L F : ℕ} (hL : S0Bind S L) (h : fixOK L F = true) {a z : ℕ}
    (ha : a < 64) (hz : z < 64) :
    (fget F a 64).testBit z = (bmulVec 6 6 (s0GetG S a) z == z) := by
  have h1 := allN_iff.1 (allN_iff.1 h a ha) z hz
  rw [s0Get_lt hL ha, ← bvecK_eq]
  have h2 := Nat.eq_of_beq_eq_true h1
  rw [bitN_eq, nIf_eq] at h2
  by_cases hc : (bvecK (mat L a) z).beq z = true
  · rw [if_pos hc] at h2
    rw [Nat.eq_of_beq_eq_true hc, beq_self_eq_true]
    cases e : (fget F a 64).testBit z
    · rw [e] at h2
      exact absurd h2 (by decide)
    · rfl
  · rw [if_neg hc] at h2
    have hne : bvecK (mat L a) z ≠ z := fun e => hc (by rw [e, Nat.beq_refl])
    rw [beq_eq_false_iff_ne.2 hne]
    cases e : (fget F a 64).testBit z
    · rfl
    · rw [e] at h2
      exact absurd h2 (by decide)

end CFSG.KC.O8.S0Pf

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf CFSG.KC.O8.S0Pf
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem s0_sound_proved {S : Array (Array ℕ)} {U : ℕ → Array ℕ} {tr : Array (ℕ × ℕ)}
    {L MT UP UI TR : Nat} (hL : S0Bind S L) (hU : ∀ k < 6, U k = decR (mat UP k))
    (hT : ∀ i < 64, tr.getD i (0, 0) = (fget TR i 9 % 8, fget TR i 9 / 8))
    (hm : mtOK L MT = true) (h : s0OK L MT UP UI TR = true) : s0CheckG S U tr = true := by
  unfold s0OK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, hd, hact, hgen, hrow, hrow0, htree⟩ := h
  simp only [s0CheckG, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hL.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [s0Get_lt hL (by norm_num), Nat.eq_of_beq_eq_true h0, decR_ID6]
  · intro i hi j hj
    have h1 := allN_iff.1 (allN_iff.1 hact i hi) j hj
    rw [orB_eq, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · right
      obtain ⟨c, hc, h2⟩ := anyN_iff.1 h1
      refine ⟨2 ^ c, by
        have : 2 ^ c ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega, ?_⟩
      rw [s0Get_lt hL hi, s0Get_lt hL hj, ← bvecK_eq, ← bvecK_eq, ← pw2_eq]
      rw [notB_eq, Bool.not_eq_true'] at h2
      intro e
      rw [e, Nat.beq_refl] at h2
      exact absurd h2 (by decide)
  · intro k hk
    have h1 := Nat.eq_of_beq_eq_true (allN_iff.1 hgen k hk)
    have hlt : fget UI k 6 < 64 := fget_lt _ _ 6
    rw [hU k hk, ← h1, idx_eq hL hd hlt, s0Get_lt hL hlt]
    exact ⟨hlt, rfl⟩
  · intro i hi j hj
    rw [table_eq hL hd hm hi hj, s0Get_lt hL (tget_lt _ _ _), s0Get_lt hL hi, s0Get_lt hL hj,
      mt_of hm hi hj, decR_bmulK]
    exact ⟨tget_lt _ _ _, rfl⟩
  · intro i hi
    have h1 := allN_iff.1 hrow i hi
    rw [strictN_eq] at h1
    obtain ⟨j, hj, h2⟩ := anyN_iff.1 (nIf_one h1)
    refine ⟨j, hj, ?_⟩
    rw [table_eq hL hd hm hi hj, ← rowMT_get hj]
    exact Nat.eq_of_beq_eq_true h2
  · intro y hy
    rw [strictN_eq] at hrow0
    have h1 := allN_iff.1 (nIf_one hrow0) y hy
    rw [table_eq hL hd hm (by norm_num) hy, ← rowMT_get hy]
    exact Nat.eq_of_beq_eq_true h1
  · intro i hi
    have h1 := allN_iff.1 htree i hi
    try beta_reduce at h1
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.succ_eq_add_one] at h1
    obtain ⟨hj, hk, he⟩ := h1
    have e7 : Nat.land (fget TR (i + 1) 9) 7 = fget TR (i + 1) 9 % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
    have e3 : Nat.shiftRight (fget TR (i + 1) 9) 3 = fget TR (i + 1) 9 / 8 := Nat.shiftRight_eq_div_pow _ 3
    simp only [treeOkG, hT (i + 1) (by omega), Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [e3] at hj
    rw [e7] at hk
    rw [e7, e3] at he
    refine ⟨⟨hj, hk⟩, ?_⟩
    rw [hU _ hk, s0Get_lt hL (by omega), s0Get_lt hL (by omega), ← decR_bmulK,
      Nat.eq_of_beq_eq_true he]

theorem S0Pf.commK_of {S : Array (Array ℕ)} {L MT y m : ℕ} (hL : S0Bind S L)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (hy : y < 64) (hmlt : m < 2 ^ 64)
    (h : commAll (mulTabG S) m y = true) :
    commK (commMask (rowMT MT y) (colMT MT y)) m = true := by
  unfold commK
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro a
  rw [testBit_land, testBit_nxor, testBit_mask64, Nat.zero_testBit]
  by_cases ha : a < 64
  · unfold commAll at h
    rw [List.all_eq_true] at h
    have h1 := h a (List.mem_range.2 ha)
    rw [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, table_eq hL hd hm ha hy,
      table_eq hL hd hm hy ha] at h1
    rw [testBit_commMask ha, colMT_get ha, rowMT_get ha, decide_eq_true ha]
    rcases h1 with h1 | h1
    · rw [h1, Bool.false_and]
    · rw [h1, beq_self_eq_true]
      simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hmlt (Nat.pow_le_pow_right (by omega) (by omega))),
      Bool.false_and]

theorem abel_sound_proved {S : Array (Array ℕ)} {ms : List ℕ} {L MT F AM n CI : Nat}
    (hL : S0Bind S L) (hA : ms = (List.range n).map fun k => fget AM k 64) (hn : 0 < n)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : abelOK L MT F AM n CI = true) :
    abelCheckG S ms = true := by
  unfold abelOK at h
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h0, hfix, hcl, hpop⟩ := h
  have hmem : ∀ m ∈ ms, ∃ k < n, m = fget AM k 64 := by
    intro m hm'
    rw [hA, List.mem_map] at hm'
    obtain ⟨k, hk, rfl⟩ := hm'
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  have hmem' : ∀ c < n, fget AM c 64 ∈ ms := fun c hc => by
    rw [hA, List.mem_map]
    exact ⟨c, List.mem_range.2 hc, rfl⟩
  simp only [abelCheckG, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.contains_iff_mem, ← Nat.eq_of_beq_eq_true h0]
    exact hmem' 0 hn
  · intro m hm'
    obtain ⟨k, -, rfl⟩ := hmem m hm'
    exact decide_eq_true (fget_lt _ _ _)
  · intro m hm' y hy
    obtain ⟨k, hk, rfl⟩ := hmem m hm'
    have hy' := List.mem_range.1 hy
    have h1 := allN_iff.1 hcl y hy'
    rw [strictN_eq, strictN_eq, strictN_eq, strictN_eq] at h1
    have h2 := allN_iff.1 (nIf_one h1) k hk
    beta_reduce at h2
    rw [orB_eq, orB_eq, Bool.or_eq_true, Bool.or_eq_true, bit_eq] at h2
    rw [Bool.or_eq_true, Bool.or_eq_true]
    rcases h2 with h2 | h2 | h2
    · exact Or.inl (Or.inl h2)
    · left
      right
      rw [notB_eq, Bool.not_eq_true'] at h2
      rw [Bool.not_eq_true']
      cases e : commAll (mulTabG S) (fget AM k 64) y
      · rfl
      · rw [S0Pf.commK_of hL hd hm hy' (fget_lt _ _ _) e] at h2
        exact absurd h2 (by decide)
    · right
      rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h2
      obtain ⟨hc, he⟩ := h2
      rw [List.contains_iff_mem, ← closeK_eq hL hd hm hy', Nat.eq_of_beq_eq_true he]
      exact hmem' _ hc
  · intro m hm'
    obtain ⟨k, hk, rfl⟩ := hmem m hm'
    have h1 := allN_iff.1 hpop k hk
    rw [Nat.ble_eq, popc_eq, popc_eq] at h1
    refine decide_eq_true (le_of_eq_of_le ?_ h1)
    congr 1
    unfold fixMaskG
    congr 1
    apply List.filter_congr
    intro z hz
    have hz' := List.mem_range.1 hz
    rw [Bool.eq_iff_iff, testBit_fixAll hz', List.all_eq_true]
    constructor
    · intro h a ha hma
      have h3 := h a (List.mem_range.2 ha)
      rw [hma, Bool.not_true, Bool.false_or] at h3
      rw [fix_of hL hfix ha hz']
      exact h3
    · intro h a ha
      rw [Bool.or_eq_true, Bool.not_eq_true']
      cases e : (fget AM k 64).testBit a
      · exact Or.inl rfl
      · right
        rw [← fix_of hL hfix (List.mem_range.1 ha) hz']
        exact h a (List.mem_range.1 ha) e

end CFSG.KC.O8

end
