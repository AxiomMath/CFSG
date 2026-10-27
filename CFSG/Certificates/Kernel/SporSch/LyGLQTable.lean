module

public import CFSG.Certificates.Kernel.SporSch.LyGLQSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.SporSch.LyGLQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Th.Native

theorem allBlk_intro' {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_intro' fun l hl => h l (by omega)]

theorem rec_blocks_intro' {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_intro' fun l hl => h l (by omega)]

theorem allN_iff' {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  refine ⟨allN_spec, fun h => ?_⟩
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have h1 : allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) = true := by
    refine allBlk_intro' fun l hl => h _ ?_
    rw [er] at hl
    rw [e6, e64]
    simp only [Nat.add_eq]
    omega
  have h2 := rec_blocks_intro' (f := f) (q := Nat.shiftRight n (nat_lit 6)) fun q hq => by
    refine allBlk_intro' fun l hl => h _ ?_
    rw [e64] at hq
    rw [e6]
    simp only [Nat.add_eq]
    have : l < 64 := hl
    omega
  rw [h1, h2]

theorem allIn_iff {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

theorem lenL_len : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_len L)

theorem getW_eq : ∀ (W : List (List Nat)) (t : Nat), getW W t = W.getD t []
  | [], _ => by simp [getW]
  | _ :: _, 0 => rfl
  | _ :: W, t + 1 => by
    rw [List.getD_cons_succ, ← getW_eq W t]
    rfl

theorem eqL_eq : ∀ (a b : List Nat), eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: a, z :: b, h => by
    have h' : bAnd(Nat.beq x z, eqL a b) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [Nat.eq_of_beq_eq_true h1, eqL_eq a b h2]

theorem let3_mem : ∀ w : List Nat, let3 w = true → ∀ k ∈ w, k < 3
  | [], _ => by simp
  | k :: w, h => by
    have h' : bAnd(Nat.blt k 3, let3 w) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Nat.blt_eq.mp h1
    · exact let3_mem w h2 j hj

theorem b8_pair {a b : Nat} (ha : a < 256) (hb : b < 256) :
    b8 (Nat.add a (Nat.mul 256 b)) 0 = a ∧ b8 (Nat.add a (Nat.mul 256 b)) 1 = b := by
  rw [b8_div, b8_div]
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, Nat.add_eq, Nat.mul_eq]
  omega

theorem words_facts {MT : Nat → Nat} {W : List (List Nat)} (h : wordsK MT W = true) :
    W.length = 256 ∧ getW W 0 = [] ∧
      ∀ x < 256, evK MT gK (getW W x) = x ∧ ∀ k ∈ getW W x, k < 3 := by
  unfold wordsK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨_, h4⟩ := (bAnd_iff _ _).1 h3
  refine ⟨?_, eqL_eq _ _ h2, fun x hx => ?_⟩
  · have e := Nat.eq_of_beq_eq_true h1
    rwa [lenL_len, List.length_map] at e
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h4 x hx)
    exact ⟨Nat.eq_of_beq_eq_true a, let3_mem _ b⟩

section Table

variable {MT : Nat → Nat} (hid : ∀ b < 256, tmK MT 0 b = b) (ha : allN 3 (assocQ MT) = true)

include ha in
theorem gen_assoc {k : Nat} (hk : k < 3) {a b : Nat} (hA : a < 256) (hB : b < 256) :
    tmK MT (tmK MT (b8 gK k) a) b = tmK MT (b8 gK k) (tmK MT a b) := by
  have c := allN_spec ha k hk
  unfold assocQ at c
  simp only [LyLoop.strictB_eqB] at c
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec c a hA) b hB)

include hid ha in
theorem assoc_word : ∀ w : List Nat, (∀ k ∈ w, k < 3) → ∀ b c, b < 256 → c < 256 →
    tmK MT (tmK MT (evK MT gK w) b) c = tmK MT (evK MT gK w) (tmK MT b c)
  | [], _, b, c, hb, _ => by rw [evK_nil, hid b hb, hid _ (tmK_lt _ _ _)]
  | k :: w, hw, b, c, hb, hc => by
    have hk := hw k (by simp)
    have IH := assoc_word w (fun j hj => hw j (by simp [hj]))
    have hv := evK_lt MT gK w
    rw [evK_cons, gen_assoc ha hk hv hb, gen_assoc ha hk (tmK_lt _ _ _) hc, IH b c hb hc,
      ← gen_assoc ha hk hv (tmK_lt _ _ _)]

include hid ha in
theorem rid_word : ∀ w : List Nat, (∀ k ∈ w, k < 3) → tmK MT (evK MT gK w) 0 = evK MT gK w
  | [], _ => by rw [evK_nil, hid 0 (by decide)]
  | k :: w, hw => by
    rw [evK_cons, gen_assoc ha (hw k (by simp)) (evK_lt _ _ _) (by decide),
      rid_word w (fun j hj => hw j (by simp [hj]))]

variable {W : List (List Nat)}
  (hW : ∀ x < 256, evK MT gK (getW W x) = x ∧ ∀ k ∈ getW W x, k < 3)

include hid ha hW in
theorem assoc_all {a b c : Nat} (hA : a < 256) (hB : b < 256) (hC : c < 256) :
    tmK MT (tmK MT a b) c = tmK MT a (tmK MT b c) := by
  have e := (hW a hA).1
  rw [← e]
  exact assoc_word hid ha _ (hW a hA).2 b c hB hC

include hid ha hW in
theorem rid_all {a : Nat} (hA : a < 256) : tmK MT a 0 = a := by
  have e := (hW a hA).1
  rw [← e]
  exact rid_word hid ha _ (hW a hA).2

include hid ha hW in
theorem hom_word {f : Nat → Nat} {y : Nat} (hf0 : f 0 = 0) (hflt : ∀ x < 256, f x < 256)
    (hgen : ∀ k < 3, ∀ x < 256, f (tmK MT (b8 gK k) x) = tmK MT (b8 y k) (f x)) :
    ∀ w : List Nat, (∀ k ∈ w, k < 3) → ∀ b < 256,
      f (tmK MT (evK MT gK w) b) = tmK MT (f (evK MT gK w)) (f b)
  | [], _, b, hb => by rw [evK_nil, hid b hb, hf0, hid _ (hflt b hb)]
  | k :: w, hw, b, hb => by
    have hk := hw k (by simp)
    have hv := evK_lt MT gK w
    rw [evK_cons, gen_assoc ha hk hv hb, hgen k hk (tmK MT (evK MT gK w) b) (tmK_lt _ _ _),
      hom_word hf0 hflt hgen w (fun j hj => hw j (by simp [hj])) b hb,
      hgen k hk (evK MT gK w) hv,
      assoc_all hid ha hW (b8_lt _ _) (hflt _ hv) (hflt b hb)]

include hid ha hW in
theorem hom_all {f : Nat → Nat} {y : Nat} (hf0 : f 0 = 0) (hflt : ∀ x < 256, f x < 256)
    (hgen : ∀ k < 3, ∀ x < 256, f (tmK MT (b8 gK k) x) = tmK MT (b8 y k) (f x))
    {a b : Nat} (hA : a < 256) (hB : b < 256) : f (tmK MT a b) = tmK MT (f a) (f b) := by
  have e := (hW a hA).1
  rw [← e]
  exact hom_word hid ha hW hf0 hflt hgen _ (hW a hA).2 b hB

end Table

@[expose] noncomputable def fKR (MT : Nat → Nat) (y : Nat) (W : List (List Nat)) :
    Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun w _ ih x acc => strictN (Nat.lor acc (Nat.shiftLeft (evK MT y w) (Nat.mul (nat_lit 8) x)))
      (ih (Nat.succ x))) W

@[expose] noncomputable def pkW (MT : Nat → Nat) (y : Nat) : List (List Nat) → Nat
  | [] => 0
  | w :: W => evK MT y w + 256 * pkW MT y W

theorem fKR_eq (MT : Nat → Nat) (y : Nat) : ∀ (W : List (List Nat)) (x acc : Nat),
    acc < 256 ^ x → fKR MT y W x acc = acc + 256 ^ x * pkW MT y W
  | [], x, acc, _ => by simp [fKR, pkW]
  | w :: W, x, acc, hacc => by
    have e1 : fKR MT y (w :: W) x acc =
        fKR MT y W (x + 1) (Nat.lor acc (Nat.shiftLeft (evK MT y w) (Nat.mul 8 x))) :=
      LyLoop.strictN_eqP _ _
    have hv := evK_lt MT y w
    have e2 : Nat.lor acc (Nat.shiftLeft (evK MT y w) (Nat.mul 8 x)) =
        acc + evK MT y w * 256 ^ x := by
      have h2 : acc < 2 ^ (8 * x) := by rwa [Nat.pow_mul]
      change acc ||| evK MT y w <<< (8 * x) = _
      rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h2, Nat.shiftLeft_eq, Nat.pow_mul]
      norm_num
      ring
    have hlt : acc + evK MT y w * 256 ^ x < 256 ^ (x + 1) := by
      rw [Nat.pow_succ]
      have := Nat.mul_le_mul_right (256 ^ x) (Nat.le_of_lt_succ hv)
      generalize 256 ^ x = P at *
      omega
    rw [e1, e2, fKR_eq MT y W (x + 1) _ hlt, pkW, Nat.pow_succ]
    ring

theorem pkW_b8 (MT : Nat → Nat) (y : Nat) : ∀ (W : List (List Nat)) (i : Nat),
    b8 (pkW MT y W) i = evK MT y (W.getD i [])
  | [], i => by
    rw [b8_div]
    simp [pkW, evK_nil]
  | w :: W, 0 => by
    rw [b8_div, pkW]
    have := evK_lt MT y w
    simp only [Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | w :: W, i + 1 => by
    rw [b8_div, pkW, Nat.pow_succ', ← Nat.div_div_eq_div_mul, List.getD_cons_succ,
      ← pkW_b8 MT y W i, b8_div]
    have := evK_lt MT y w
    have e : (evK MT y w + 256 * pkW MT y W) / 256 = pkW MT y W := by omega
    rw [e]

theorem fK_b8 (MT : Nat → Nat) (W : List (List Nat)) (y x : Nat) :
    b8 (fK MT W y) x = evK MT y (getW W x) := by
  have e : fK MT W y = fKR MT y W 0 0 := rfl
  rw [e, fKR_eq MT y W 0 0 (by decide), Nat.pow_zero, Nat.zero_add, Nat.one_mul, pkW_b8,
    getW_eq]

theorem pick_unpk {y k : Nat} (hk : k < 3) : pickY (unpk y) k = b8 y k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl

theorem gens_eq : glqGens = unpk gK := by decide +kernel

theorem evalY_eq {MT : Nat → Nat} {y : Nat} (w : List Nat) (hw : ∀ k ∈ w, k < 3) :
    evalY (TBL MT 256) (unpk y) w = evK MT y w :=
  evalY_at w fun k hk => ⟨hw k hk, pick_unpk (hw k hk)⟩

theorem arr_get {W : List (List Nat)} (hl : W.length = 256) {x : Nat} (hx : x < 256) :
    W.toArray[x]! = getW W x := by
  rw [getElem!_pos _ x (by simpa [hl] using hx), List.getElem_toArray, getW_eq,
    List.getD_eq_getElem]

theorem fm_get {MT : Nat → Nat} {W : List (List Nat)} (hl : W.length = 256)
    (hW : ∀ x < 256, ∀ k ∈ getW W x, k < 3) (y : Nat) {x : Nat} (hx : x < 256) :
    (fmapY (TBL MT 256) W.toArray (unpk y))[x]! = evK MT y (getW W x) := by
  unfold fmapY
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  dsimp only
  rw [arr_get hl hx, evalY_eq _ (hW x hx)]

section Hom

variable {MT : Nat → Nat} {W : List (List Nat)} (hid : ∀ b < 256, tmK MT 0 b = b)
  (ha : allN 3 (assocQ MT) = true) (hw : wordsK MT W = true)

include hid ha hw in
theorem hom_of_crit {y : Nat} (h : critK MT W y = true) :
    isHomT (TBL MT 256) (fmapY (TBL MT 256) W.toArray (unpk y)) = true := by
  obtain ⟨hl, h0, hW⟩ := words_facts hw
  have hW3 : ∀ x < 256, ∀ k ∈ getW W x, k < 3 := fun x hx => (hW x hx).2
  unfold critK at h
  rw [LyLoop.strictB_eqB] at h
  unfold critF at h
  obtain ⟨c1, c2⟩ := (bAnd_iff _ _).1 h
  simp only [LyLoop.strictB_eqB, fK_b8] at c1 c2
  have hgen : ∀ k < 3, ∀ x < 256, evK MT y (getW W (tmK MT (b8 gK k) x)) =
      tmK MT (b8 y k) (evK MT y (getW W x)) := fun k hk x hx =>
    Nat.eq_of_beq_eq_true (allN_spec (allN_spec c2 k hk) x hx)
  have hf0 : evK MT y (getW W 0) = 0 := by rw [h0, evK_nil]
  have hom := fun {a b : Nat} (hA : a < 256) (hB : b < 256) =>
    hom_all hid ha hW hf0 (fun x _ => evK_lt MT y _) hgen hA hB
  unfold isHomT
  simp only [Bool.and_eq_true, allIn_iff]
  refine ⟨⟨fun x _ hx => ?_, fun x hx1 hx => ?_⟩, fun a _ hA b _ hB => ?_⟩
  · rw [fm_get hl hW3 y hx]
    exact decide_eq_true (evK_lt _ _ _)
  · rw [fm_get hl hW3 y hx]
    have c := allN_spec c1 (x - 1) (by omega)
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hx1] at c
    simp only [Bool.not_eq_true'] at c
    simpa using Nat.ne_of_beq_eq_false c
  · rw [tbl_tm hA hB, fm_get hl hW3 y (tmK_lt _ _ _), fm_get hl hW3 y hA, fm_get hl hW3 y hB,
      tbl_tm (evK_lt _ _ _) (evK_lt _ _ _), hom hA hB]
    exact beq_self_eq_true _

include hid ha hw in
theorem genT_of_hom {y : Nat} (h1 : getW W 1 = [0]) (h3 : getW W 3 = [1]) (h5 : getW W 5 = [2])
    (h : isHomT (TBL MT 256) (fmapY (TBL MT 256) W.toArray (unpk y)) = true) :
    ∀ t < 768, genT MT W y t = true := by
  obtain ⟨hl, _, hW⟩ := words_facts hw
  have hW3 : ∀ x < 256, ∀ k ∈ getW W x, k < 3 := fun x hx => (hW x hx).2
  unfold isHomT at h
  simp only [Bool.and_eq_true, allIn_iff] at h
  have hom : ∀ a < 256, ∀ b < 256, evK MT y (getW W (tmK MT a b)) =
      tmK MT (evK MT y (getW W a)) (evK MT y (getW W b)) := fun a hA b hB => by
    have c := h.2 a (Nat.zero_le _) hA b (Nat.zero_le _) hB
    rw [tbl_tm hA hB, fm_get hl hW3 y (tmK_lt _ _ _), fm_get hl hW3 y hA, fm_get hl hW3 y hB,
      tbl_tm (evK_lt _ _ _) (evK_lt _ _ _)] at c
    exact beq_iff_eq.mp c
  have hg : ∀ k < 3, getW W (b8 gK k) = [k] := fun k hk => by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h5
  intro t ht
  unfold genT
  simp only [LyLoop.strictB_eqB]
  have ek : Nat.shiftRight t 8 = t / 256 := by
    change t >>> 8 = t / 2 ^ 8
    rw [Nat.shiftRight_eq_div_pow]
  have ex : Nat.land t 255 = t % 256 := by
    change t &&& (2 ^ 8 - 1) = t % 2 ^ 8
    exact Nat.and_two_pow_sub_one_eq_mod t 8
  rw [ek, ex]
  have hk : t / 256 < 3 := by omega
  have hx : t % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [hom _ (b8_lt _ _) _ hx, hg _ hk, evK_cons, evK_nil,
    rid_all hid ha hW (b8_lt _ _)]
  exact Nat.beq_refl _

include hid ha hw in
theorem failK_of_hom {y : Nat} (h1 : getW W 1 = [0]) (h3 : getW W 3 = [1])
    (h5 : getW W 5 = [2])
    (h : isHomT (TBL MT 256) (fmapY (TBL MT 256) W.toArray (unpk y)) = true) :
    failK MT W y 768 = false := by
  have hg := genT_of_hom hid ha hw h1 h3 h5 h
  have key : ∀ n t, t + n ≤ 768 → Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
      (fun _ ih t => bIf(genT MT W y t, ih (Nat.succ t), true)) n t = false := by
    intro n
    induction n with
    | zero => intro t _; rfl
    | succ n ih =>
      intro t ht
      change Bool.rec (motive := fun _ => Bool) true
        (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
          (fun _ ih t => bIf(genT MT W y t, ih (Nat.succ t), true)) n (Nat.succ t))
        (genT MT W y t) = false
      rw [hg t (by omega)]
      exact ih (t + 1) (by omega)
  have k2 : ∀ n, n ≤ 768 → failK MT W y n = false := fun n hn => by
    unfold failK
    exact key n 0 (by omega)
  exact k2 768 (Nat.le_refl _)

end Hom

theorem fixF_mem {F : Nat} : ∀ {P : List Nat}, fixF P F = true →
    ∃ p ∈ P, b8 F (b8 p 0) = b8 p 0 ∧ b8 F (b8 p 1) = b8 p 1
  | [], h => absurd h Bool.false_ne_true
  | p :: P, h => by
    have h' : bIf(bAnd(Nat.beq (b8 F (b8 p 0)) (b8 p 0), Nat.beq (b8 F (b8 p 1)) (b8 p 1)), true,
        fixF P F) = true := h
    cases e : bAnd(Nat.beq (b8 F (b8 p 0)) (b8 p 0), Nat.beq (b8 F (b8 p 1)) (b8 p 1))
    · rw [e] at h'
      obtain ⟨q, hq, r⟩ := fixF_mem h'
      exact ⟨q, List.mem_cons_of_mem _ hq, r⟩
    · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 e
      exact ⟨p, List.mem_cons_self, Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem pairsK_mem {MT : Nat → Nat} {p : Nat} (hp : p ∈ pairsK MT) :
    (b8 p 0, b8 p 1) ∈ glqPairs (TBL MT 256) := by
  unfold pairsK at hp
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    LyLoop.bAnd_eqP, Bool.and_eq_true] at hp
  obtain ⟨a, ⟨haR, ha1, ha2⟩, b, ⟨⟨hbR, hb1, hb2⟩, hab, hc⟩, rfl⟩ := hp
  obtain ⟨e0, e1⟩ := b8_pair haR hbR
  rw [e0, e1]
  unfold glqPairs prodL
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Bool.and_eq_true,
    Prod.mk.injEq, decide_eq_true_eq]
  have hI : ∀ x < 256, Bool.not (Nat.beq x 0) = true → Nat.beq (tmK MT x x) 0 = true →
      isInv (TBL MT 256) x = true := fun x hx h1 h2 => by
    unfold isInv
    rw [tbl_tm hx hx]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    simp only [Bool.not_eq_true'] at h1
    exact ⟨Nat.ne_of_beq_eq_false h1, Nat.eq_of_beq_eq_true h2⟩
  refine ⟨⟨a, ⟨haR, hI a haR ha1 ha2⟩, b, ⟨hbR, hI b hbR hb1 hb2⟩, rfl, rfl⟩,
    Nat.blt_eq.mp hab, ?_⟩
  rw [tbl_tm haR hbR, tbl_tm hbR haR]
  exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true hc)

theorem table_ok {MT : Nat → Nat} {SG : Nat} {W : List (List Nat)} {A : List Nat}
    (hid : ∀ b < 256, tmK MT 0 b = b) (hsig : allN 256 (sigQ MT SG) = true)
    (ha : allN 3 (assocQ MT) = true) (hw : wordsK MT W = true)
    (h1 : getW W 1 = [0]) (h3 : getW W 3 = [1]) (h5 : getW W 5 = [2])
    (hauts : bAnd(Nat.beq (lenL (candsK MT SG)) 5632, autsK MT W (candsK MT SG) A) = true)
    (halen : Nat.beq (lenL A) 512 = true)
    (hinvo : Nat.beq (invoCnt MT W (pairsK MT) A) 176 = true) :
    glqWithTable (TBL MT 256) = true := by
  obtain ⟨hl, _, hW⟩ := words_facts hw
  have hW3 : ∀ x < 256, ∀ k ∈ getW W x, k < 3 := fun x hx => (hW x hx).2
  have hWs := words_sound hw
  have hA : glqAuts (TBL MT 256) W.toArray = A.map unpk := by
    unfold glqAuts
    rw [cands_sound hsig, List.filter_map]
    congr 1
    refine auts_split ((bAnd_iff _ _).1 hauts).2 (fun y _ hc => hom_of_crit hid ha hw hc)
      (fun y _ hf => ?_)
    simp only [Function.comp_apply]
    cases e : isHomT (TBL MT 256) (fmapY (TBL MT 256) W.toArray (unpk y))
    · rfl
    · rw [failK_of_hom hid ha hw h1 h3 h5 e] at hf
      exact absurd hf Bool.false_ne_true
  have hinv : ∀ y, isInvoT (fmapY (TBL MT 256) W.toArray (unpk y)) = invoF (fK MT W y) := by
    intro y
    have e : ∀ x < 256, ((fmapY (TBL MT 256) W.toArray (unpk y))[
        (fmapY (TBL MT 256) W.toArray (unpk y))[x]!]! == x) =
        Nat.beq (b8 (fK MT W y) (b8 (fK MT W y) x)) x := fun x hx => by
      rw [fm_get hl hW3 y hx, fm_get hl hW3 y (evK_lt _ _ _), fK_b8, fK_b8]
      rfl
    apply Bool.eq_iff_iff.mpr
    unfold isInvoT invoF
    rw [allIn_iff, allN_iff']
    constructor
    · intro h x hx
      rw [← e x hx]
      exact h x (Nat.zero_le _) hx
    · intro h x _ hx
      rw [e x hx]
      exact h x hx
  obtain ⟨hcnt, hfix⟩ := invo_sound hinvo
  unfold glqWithTable glqWithWords glqChecks
  rw [hWs, hA]
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_iff, List.length_map, List.size_toArray,
    List.filter_map, List.all_map, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, fun x _ hx => ?_⟩, fun x _ hx => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [arr_get hl hx]
    exact fun k hk => decide_eq_true (hW3 x hx k hk)
  · rw [arr_get hl hx, gens_eq, evalY_eq _ (hW3 x hx)]
    exact (hW x hx).1
  · rw [arr_get hl (by decide)]
    exact h1
  · rw [arr_get hl (by decide)]
    exact h3
  · rw [arr_get hl (by decide)]
    exact h5
  · exact (lenL_len A).symm.trans (Nat.eq_of_beq_eq_true halen)
  · have hf : A.filter ((fun y => isInvoT (fmapY (TBL MT 256) W.toArray y)) ∘ unpk) =
        A.filter (fun y => invoF (fK MT W y)) := List.filter_congr fun y _ => hinv y
    exact (congrArg List.length hf).trans hcnt
  · intro p hp
    have hp' := hp
    unfold glqPairs prodL at hp'
    simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
      decide_eq_true_eq] at hp'
    obtain ⟨⟨a, ⟨_, ha'⟩, b, ⟨_, hb'⟩, rfl⟩, hlt, hc⟩ := hp'
    exact ⟨⟨⟨ha', hb'⟩, bne_iff_ne.mpr (Nat.ne_of_lt hlt)⟩, beq_iff_eq.mp hc⟩
  · intro y hy
    simp only [Function.comp_apply]
    cases e : isInvoT (fmapY (TBL MT 256) W.toArray (unpk y))
    · rfl
    · rw [hinv] at e
      obtain ⟨p, hp, r0, r1⟩ := fixF_mem (hfix y hy e)
      have hm := pairsK_mem hp
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine ⟨_, hm, ?_, ?_⟩
      · rw [fm_get hl hW3 y (b8_lt _ _), ← fK_b8]
        exact r0
      · rw [fm_get hl hW3 y (b8_lt _ _), ← fK_b8]
        exact r1

end CFSG.KS.SporSch.LyGLQ

end
