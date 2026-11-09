module

public import Certificates.Data.Kernel.Fi22Search2071

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

set_option exponentiation.threshold 4096

theorem strictN_ckc (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem foldN_blkFold (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = blkFold n (fun b len s => foldBlk b f len s) s := rfl

theorem blkRec_congr {g₁ g₂ : Nat → Nat → Nat → Nat} (q : Nat)
    (h : ∀ j < q, ∀ s, g₁ (Nat.shiftLeft j (nat_lit 6)) (nat_lit 64) s =
      g₂ (Nat.shiftLeft j (nat_lit 6)) (nat_lit 64) s) (x : Nat) :
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun i ih s => strictN (g₁ (Nat.shiftLeft i (nat_lit 6)) (nat_lit 64) s) ih) q x =
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun i ih s => strictN (g₂ (Nat.shiftLeft i (nat_lit 6)) (nat_lit 64) s) ih) q x := by
  induction q generalizing x with
  | zero => rfl
  | succ j ih =>
    change strictN _ _ = strictN _ _
    rw [strictN_ckc, strictN_ckc, h j (by omega) x]
    exact ih (fun j' hj' => h j' (by omega)) _

theorem blkFold_congr {n : Nat} {g₁ g₂ : Nat → Nat → Nat → Nat}
    (h : ∀ b len s, len ≤ 64 → b ≤ n → g₁ b len s = g₂ b len s) (s : Nat) :
    blkFold n g₁ s = blkFold n g₂ s := by
  unfold blkFold
  dsimp only
  have hq : (n >>> 6) <<< 6 ≤ n := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    exact Nat.div_mul_le_self n _
  have hl : n &&& 63 ≤ 64 := Nat.le_trans Nat.and_le_right (by decide)
  rw [h (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) (Nat.land n (nat_lit 63)) s hl hq]
  refine blkRec_congr _ (fun j hj s => h _ _ s (Nat.le_refl _) ?_) _
  change j < n >>> 6 at hj
  change j <<< 6 ≤ n
  rw [Nat.shiftLeft_eq]
  rw [Nat.shiftRight_eq_div_pow] at hj
  have e : (2 : Nat) ^ 6 = 64 := rfl
  rw [e] at hj ⊢
  omega

theorem foldBlk_succC (b : Nat) (f : Nat → Nat → Nat) (l s : Nat) :
    foldBlk b f (l + 1) s = foldBlk b f l (f (b + l) s) := by
  unfold foldBlk
  exact strictN_ckc _ _

theorem chunkRd32 {C b Ch M l : Nat} (hM : M = 2 ^ 2048 - 1)
    (hCh : Ch = Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M)
    (hl : l < 64) :
    Nat.land (Nat.shiftRight Ch (Nat.mul (nat_lit 32) l)) (nat_lit 4294967295) = cget C (Nat.add b l) := by
  subst hCh hM
  have h := rd_chunk C (64 + 32 * b) 2048 32 l (by omega)
  have e : 64 + 32 * b + 32 * l = 64 + 32 * (b + l) := by omega
  rw [e] at h
  exact h

theorem chunkRd48 {A b Ah MA l : Nat} (hMA : MA = 2 ^ 3072 - 1)
    (hAh : Ah = Nat.land (Nat.shiftRight A (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) b))) MA)
    (hl : l < 64) :
    Nat.land (Nat.shiftRight Ah (Nat.mul (nat_lit 48) l)) (nat_lit 281474976710655) =
      Nat.land (Nat.shiftRight A (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) (Nat.add b l))))
        (nat_lit 281474976710655) := by
  subst hAh hMA
  have h := rd_chunk A (128 + 48 * b) 3072 48 l (by omega)
  have e : 128 + 48 * b + 48 * l = 128 + 48 * (b + l) := by omega
  rw [e] at h
  exact h

theorem accBlkC_succ (S : Nat → Nat) (b Ch l s : Nat) :
    accBlkC S b Ch (l + 1) s = accBlkC S b Ch l (Nat.add s (Nat.mul (hcK (Nat.land
      (Nat.shiftRight Ch (Nat.mul (nat_lit 32) l)) (nat_lit 4294967295))) (S (Nat.add b l)))) := by
  unfold accBlkC
  exact strictN_ckc _ _

theorem accBlk_eq {S : Nat → Nat} {C b Ch M : Nat} (hM : M = 2 ^ 2048 - 1)
    (hCh : Ch = Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M) :
    ∀ len, len ≤ 64 → ∀ s, accBlkC S b Ch len s =
      foldBlk b (fun w a => Nat.add a (Nat.mul (hcK (cget C w)) (S w))) len s := by
  intro len
  induction len with
  | zero => intro _ s; rfl
  | succ l ih =>
    intro hl s
    rw [accBlkC_succ, foldBlk_succC, chunkRd32 hM hCh (by omega)]
    exact ih (by omega) _

theorem accKc_eq (n : Nat) (S : Nat → Nat) (C : Nat) {M : Nat} (hM : M = 2 ^ 2048 - 1) :
    accKc n S C M = accK n S C := by
  unfold accKc accK
  rw [foldN_blkFold]
  apply blkFold_congr
  intro b len s hl _
  rw [strictN_ckc]
  exact accBlk_eq hM rfl len hl s

theorem newColC_eq {T C A b Ch Ah M MA l : Nat} (hM : M = 2 ^ 2048 - 1) (hMA : MA = 2 ^ 3072 - 1)
    (hCh : Ch = Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M)
    (hAh : Ah = Nat.land (Nat.shiftRight A (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) b))) MA)
    (hl : l < 64) : newColC T C Ch Ah b l = newCol T C A (b + l) := by
  unfold newColC newCol
  rw [chunkRd32 hM hCh hl, chunkRd48 hMA hAh hl]
  rfl

theorem stepBlkC_succ (T C b Ch Ah l s : Nat) :
    stepBlkC T C b Ch Ah (l + 1) s =
      stepBlkC T C b Ch Ah l (s + (newColC T C Ch Ah b l <<< (64 + 32 * l)) + 1) := by
  unfold stepBlkC
  exact strictN_ckc _ _

theorem div_mod_step (u y : Nat) (hu : u % 2 ^ 64 + 1 < 2 ^ 64) :
    (u + y * 2 ^ 64 + 1) / 2 ^ 64 = u / 2 ^ 64 + y ∧ (u + y * 2 ^ 64 + 1) % 2 ^ 64 = u % 2 ^ 64 + 1 := by
  have e : u + y * 2 ^ 64 + 1 = (u % 2 ^ 64 + 1) + (u / 2 ^ 64 + y) * 2 ^ 64 := by
    have := Nat.div_add_mod u (2 ^ 64)
    rw [Nat.add_mul, Nat.mul_comm (u / 2 ^ 64)]
    omega
  rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hu, Nat.mod_eq_of_lt hu, Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem stepBlk_main {T C b Ch Ah : Nat} {f : Nat → Nat → Nat}
    (hf : ∀ l s, l < 64 → f (b + l) s = s + newColC T C Ch Ah b l * 2 ^ (64 + 32 * (b + l)) + 1) :
    ∀ len, len ≤ 64 → ∀ v u, u % 2 ^ 64 + len < 2 ^ 64 →
      foldBlk b f len v + u / 2 ^ 64 * 2 ^ (64 + 32 * b) =
        v + stepBlkC T C b Ch Ah len u / 2 ^ 64 * 2 ^ (64 + 32 * b) + len ∧
      stepBlkC T C b Ch Ah len u % 2 ^ 64 = u % 2 ^ 64 + len := by
  intro len
  induction len with
  | zero => intro _ v u _; exact ⟨rfl, rfl⟩
  | succ l ih =>
    intro hl v u hu
    rw [foldBlk_succC, stepBlkC_succ, hf l v (by omega), Nat.shiftLeft_eq]
    have hy : newColC T C Ch Ah b l * 2 ^ (64 + 32 * l) =
        newColC T C Ch Ah b l * 2 ^ (32 * l) * 2 ^ 64 := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm (32 * l) 64]
    rw [hy]
    obtain ⟨hd, hm⟩ := div_mod_step u (newColC T C Ch Ah b l * 2 ^ (32 * l)) (by omega)
    obtain ⟨h1, h2⟩ := ih (by omega) (v + newColC T C Ch Ah b l * 2 ^ (64 + 32 * (b + l)) + 1)
      (u + newColC T C Ch Ah b l * 2 ^ (32 * l) * 2 ^ 64 + 1) (by omega)
    rw [hd, Nat.add_mul] at h1
    have hp : newColC T C Ch Ah b l * 2 ^ (32 * l) * 2 ^ (64 + 32 * b) =
        newColC T C Ch Ah b l * 2 ^ (64 + 32 * (b + l)) := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      omega
    rw [hp] at h1
    rw [hm] at h2
    constructor
    · omega
    · omega

theorem stepBlk_eq {T C A b Ch Ah M MA len : Nat} (s : Nat) (f : Nat → Nat → Nat)
    (hM : M = 2 ^ 2048 - 1) (hMA : MA = 2 ^ 3072 - 1)
    (hCh : Ch = Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M)
    (hAh : Ah = Nat.land (Nat.shiftRight A (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) b))) MA)
    (hf : ∀ l s, f (b + l) s = s + (newCol T C A (b + l) <<< (64 + 32 * (b + l))) + 1)
    (hb : b < 1000000) (hl : len ≤ 64) :
    s + ((stepBlkC T C b Ch Ah len (4096 * (b + 1)) >>> 64) <<< (64 + 32 * b)) + len =
      foldBlk b f len s := by
  have hf' : ∀ l s, l < 64 →
      f (b + l) s = s + newColC T C Ch Ah b l * 2 ^ (64 + 32 * (b + l)) + 1 := by
    intro l s hl
    rw [hf, newColC_eq hM hMA hCh hAh hl, Nat.shiftLeft_eq]
  have hK : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hσ : 4096 * (b + 1) < 2 ^ 64 := by rw [hK]; omega
  obtain ⟨h1, -⟩ := stepBlk_main hf' len hl s (4096 * (b + 1))
    (by rw [Nat.mod_eq_of_lt hσ, hK]; omega)
  rw [Nat.div_eq_of_lt hσ, Nat.zero_mul, Nat.add_zero] at h1
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem stepKc_eq {n : Nat} (S : Nat → Nat) (T C : Nat) (hn : n < 4096) :
    stepKc n S T C = stepK n S T C := by
  unfold stepKc stepK
  rw [strictN_ckc, strictN_ckc, strictN_ckc, strictN_ckc]
  have hM : Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1) = 2 ^ 2048 - 1 := by decide
  have hMA : Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3072)) (nat_lit 1) = 2 ^ 3072 - 1 := by
    decide
  rw [accKc_eq n S C hM, foldN_blkFold]
  apply blkFold_congr
  intro b len s hl hb
  rw [strictN_ckc, strictN_ckc]
  exact stepBlk_eq s _ hM hMA rfl rfl (fun _ _ => rfl) (by omega) hl

theorem colourKc_eq {n : Nat} (S : Nat → Nat) (T : Nat) (pre : List Nat) (hn : n < 4096) :
    ∀ k, colourKc n S T pre k = colourK n S T pre k
  | 0 => rfl
  | k + 1 => by
    have e1 : colourKc n S T pre (k + 1) = stepKc n S T (colourKc n S T pre k) := by
      change strictN (colourKc n S T pre k) (fun C => stepKc n S T C) = _
      exact strictN_ckc _ _
    have e2 : colourK n S T pre (k + 1) = stepK n S T (colourK n S T pre k) := by
      change strictN (colourK n S T pre k) (fun C => stepK n S T C) = _
      exact strictN_ckc _ _
    rw [e1, e2, colourKc_eq S T pre hn k, stepKc_eq S T _ hn]

theorem foldBlk_eqC (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    rw [foldBlk_succC, ih, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem foldr_range_addC (f : Nat → Nat → Nat) (a b s : Nat) :
    (List.range (a + b)).foldr f s =
      (List.range a).foldr f ((List.range b).foldr (fun l s => f (a + l) s) s) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

theorem foldN_recC (f : Nat → Nat → Nat) (h : Nat) : ∀ x : Nat,
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) h x
      = (List.range (h * 64)).foldr f x := by
  induction h with
  | zero => intro x; rfl
  | succ h ih =>
    intro x
    have hs : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
        (h + 1) x
        = strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) x)
            (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
              (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
              h) :=
      rfl
    have e6 : Nat.shiftLeft h (nat_lit 6) = h * 64 := by
      change h <<< 6 = h * 64
      rw [Nat.shiftLeft_eq]
    rw [hs, strictN_ckc, ih, foldBlk_eqC, e6, Nat.add_one_mul h 64, foldr_range_addC f (h * 64) 64 x]

theorem foldN_eqC (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  refine Eq.trans (foldN_recC f (Nat.shiftRight n (nat_lit 6))
    (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) s)) ?_
  have e6 : Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6) = n / 64 * 64 := by
    change (n >>> 6) <<< 6 = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have r6 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  have l63 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  rw [foldBlk_eqC, e6, l63, r6, ← foldr_range_addC f (n / 64 * 64) (n % 64) s, Nat.div_add_mod' n 64]

end CFSG.KC.N3153

namespace CFSG.KC.S2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.Sporadic.FischerOddCore.Native

theorem foldr_addC (h : Nat → Nat) : ∀ (l : List Nat) (s : Nat),
    l.foldr (fun v a => a + h v) s = s + l.foldr (fun v a => a + h v) 0
  | [], s => by simp
  | x :: l, s => by
    simp only [List.foldr_cons]
    rw [foldr_addC h l s]
    omega

theorem foldr_add2 (h₁ h₂ : Nat → Nat) : ∀ l : List Nat,
    l.foldr (fun v a => a + (h₁ v + h₂ v)) 0 =
      l.foldr (fun v a => a + h₁ v) 0 + l.foldr (fun v a => a + h₂ v) 0
  | [] => rfl
  | x :: l => by
    simp only [List.foldr_cons]
    rw [foldr_add2 h₁ h₂ l]
    omega

theorem foldr_zeroC (h : Nat → Nat) (hh : ∀ v, h v = 0) : ∀ l : List Nat,
    l.foldr (fun v a => a + h v) 0 = 0
  | [] => rfl
  | x :: l => by
    simp only [List.foldr_cons]
    rw [foldr_zeroC h hh l, hh]

theorem foldr_point (x y : Nat) : ∀ l : List Nat, l.Nodup →
    l.foldr (fun v a => a + if v = x then y else 0) 0 = if x ∈ l then y else 0
  | [], _ => by simp
  | z :: l, hl => by
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons, List.mem_cons]
    rw [foldr_point x y l hl.2]
    by_cases hz : z = x
    · subst hz
      simp [hl.1]
    · have hx : x ≠ z := fun h => hz h.symm
      simp [hz, hx]

theorem nIf_beqC (a b x y : Nat) : nIf(Nat.beq a b, x, y) = if a = b then x else y := by
  cases h : Nat.beq a b
  · change y = _
    simp [Nat.ne_of_beq_eq_false h]
  · change x = _
    simp [Nat.eq_of_beq_eq_true h]

theorem memL_iffC (E : List Nat) (a : Nat) : memL E a = true ↔ a ∈ E := by
  induction E with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | cons b E ih =>
    change bIf(Nat.beq b a, true, memL E a) = true ↔ _
    rw [List.mem_cons]
    cases h : Nat.beq b a
    · change memL E a = true ↔ _
      have hb : a ≠ b := fun e => Nat.ne_of_beq_eq_false h e.symm
      rw [ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left hb⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

def idxFrom : List Nat → Nat → List Nat → Nat → Nat
  | [], _, _, _ => 0
  | a :: r, off, E, v => (if v = a ∧ a ∉ E then off + 1 else 0) + idxFrom r (off + 1) (a :: E) v

theorem idxK_consC (a : Nat) (r : List Nat) (v : Nat) :
    idxK (a :: r) v = if a = v then 1 else (if idxK r v = 0 then 0 else idxK r v + 1) := by
  change nIf(Nat.beq a v, nat_lit 1, nIf(Nat.beq (idxK r v) (nat_lit 0), nat_lit 0,
    Nat.add (idxK r v) (nat_lit 1))) = _
  rw [nIf_beqC, nIf_beqC]

theorem idxFrom_eq (v : Nat) : ∀ (pre : List Nat) (off : Nat) (E : List Nat),
    idxFrom pre off E v = if v ∈ E then 0 else (if idxK pre v = 0 then 0 else idxK pre v + off)
  | [], off, E => by
    have h0 : idxK [] v = 0 := rfl
    simp [idxFrom, h0]
  | a :: r, off, E => by
    simp only [idxFrom]
    rw [idxFrom_eq v r (off + 1) (a :: E), idxK_consC]
    simp only [List.mem_cons]
    by_cases ha : v = a
    · subst ha
      by_cases hE : v ∈ E <;> simp [hE, Nat.add_comm]
    · have ha' : a ≠ v := fun h => ha h.symm
      by_cases hE : v ∈ E <;> by_cases hr : idxK r v = 0 <;> simp [ha, ha', hE, hr] <;> omega

theorem preCorr_term (n a X : Nat) (E : List Nat) :
    nIf(bAnd(Nat.blt a n, Bool.not (memL E a)), X, nat_lit 0) = if a < n then (if a ∉ E then X else 0)
      else 0 := by
  cases h1 : Nat.blt a n <;> cases h2 : memL E a
  · have : ¬ a < n := fun h => by rw [← Nat.blt_eq, h1] at h; exact Bool.noConfusion h
    simp [this]
  · have : ¬ a < n := fun h => by rw [← Nat.blt_eq, h1] at h; exact Bool.noConfusion h
    simp [this]
  · have h3 : a < n := by rw [← Nat.blt_eq, h1]
    have h4 : a ∉ E := fun h => by rw [← memL_iffC, h2] at h; exact Bool.noConfusion h
    simp [h3, h4]
  · have h3 : a < n := by rw [← Nat.blt_eq, h1]
    have h4 : a ∈ E := (memL_iffC E a).1 h2
    simp [h3, h4]

theorem preCorr_sum (n : Nat) : ∀ (pre : List Nat) (off : Nat) (E : List Nat),
    (List.range n).foldr (fun v a => a + (2 * idxFrom pre off E v) <<< (64 + 32 * v)) 0 =
      preCorrK n pre off E
  | [], off, E => foldr_zeroC _ (fun v => by simp [idxFrom]) _
  | a :: r, off, E => by
    have hs : (fun v x => x + (2 * idxFrom (a :: r) off E v) <<< (64 + 32 * v)) =
        fun v x => x + ((if v = a then (if a ∉ E then (2 * (off + 1)) <<< (64 + 32 * a) else 0)
          else 0) + (2 * idxFrom r (off + 1) (a :: E) v) <<< (64 + 32 * v)) := by
      funext v x
      simp only [idxFrom, Nat.shiftLeft_eq]
      by_cases hv : v = a <;> by_cases hE : a ∈ E <;> simp [hv, hE, Nat.mul_add, Nat.add_mul]
    rw [hs, foldr_add2, foldr_point _ _ _ List.nodup_range, preCorr_sum n r (off + 1) (a :: E)]
    simp only [List.mem_range]
    change _ = Nat.add (nIf(bAnd(Nat.blt a n, Bool.not (memL E a)),
        Nat.shiftLeft (Nat.mul (nat_lit 2) (Nat.add off (nat_lit 1)))
          (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) a)), nat_lit 0))
      (preCorrK n r (Nat.add off (nat_lit 1)) (a :: E))
    rw [preCorr_term]
    rfl

theorem initK_pre (n T : Nat) (pre : List Nat) : initK n T pre = initK n T [] + preCorrK n pre 0 [] := by
  change foldN n (fun v a => a + (initVal T pre v <<< (64 + 32 * v)) + 1) 0 =
    foldN n (fun v a => a + (initVal T [] v <<< (64 + 32 * v)) + 1) 0 + preCorrK n pre 0 []
  rw [foldN_eqC, foldN_eqC]
  simp only [Nat.add_assoc]
  have hv : ∀ v, initVal T pre v <<< (64 + 32 * v) + 1 =
      (initVal T [] v <<< (64 + 32 * v) + 1) + (2 * idxFrom pre 0 [] v) <<< (64 + 32 * v) := by
    intro v
    have h0 : idxK [] v = 0 := rfl
    have hi : idxFrom pre 0 [] v = idxK pre v := by
      rw [idxFrom_eq]
      by_cases h : idxK pre v = 0 <;> simp [h]
    have hT : initVal T pre v = 2 * idxK pre v + initVal T [] v := by
      unfold initVal
      rw [h0]
      change 2 * idxK pre v + _ = 2 * idxK pre v + (2 * 0 + _)
      omega
    rw [hi, hT, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.add_mul]
    omega
  have hf : (fun v a => a + (initVal T pre v <<< (64 + 32 * v) + 1)) =
      fun v a => a + ((initVal T [] v <<< (64 + 32 * v) + 1) +
        (2 * idxFrom pre 0 [] v) <<< (64 + 32 * v)) := by
    funext v a
    rw [hv]
  rw [hf, foldr_add2, preCorr_sum]

theorem colourKr_eq {n : Nat} (S : Nat → Nat) (T F : Nat) (pre : List Nat) (hF : initK n T [] = F)
    (hn : n < 4096) : ∀ k, colourKr n S T F pre k = colourK n S T pre k
  | 0 => by
    change F + preCorrK n pre 0 [] = initK n T pre
    rw [initK_pre, hF]
  | k + 1 => by
    have e1 : colourKr n S T F pre (k + 1) = stepKc n S T (colourKr n S T F pre k) := by
      change strictN (colourKr n S T F pre k) (fun C => stepKc n S T C) = _
      exact strictN_ckc _ _
    have e2 : colourK n S T pre (k + 1) = stepK n S T (colourK n S T pre k) := by
      change strictN (colourK n S T pre k) (fun C => stepK n S T C) = _
      exact strictN_ckc _ _
    rw [e1, e2, colourKr_eq S T F pre hF hn k, stepKc_eq S T _ hn]

theorem nodeKc_eq {n : Nat} (hn : n < 4096) (S : Nat → Nat) (T F : Nat) (hF : initK n T [] = F)
    (PL : Nat → Nat) (np : Nat)
    (AC : Nat → Nat) (na : Nat) (nodes : Array SNode) (base SC : List Nat) (CB k : Nat)
    (DT : Nat → Nat) (i : Nat) :
    nodeKc n S T F PL np AC na nodes base SC CB k DT i =
      nodeK n S T PL np AC na nodes base SC CB k DT i := by
  have hc : colourKr n S T F = colourK n S T :=
    funext fun pre => funext (colourKr_eq S T F pre hF hn)
  unfold nodeKc nodeK branchKc branchK leafKc leafK
  rw [hc]

theorem srcColKc_eq {n : Nat} (hn : n < 4096) (S : Nat → Nat) (T F : Nat) (hF : initK n T [] = F)
    (base : List Nat) (k d sc : Nat) : srcColKc n S T F base k d sc = srcColK n S T base k d sc := by
  unfold srcColKc srcColK
  rw [colourKr_eq S T F _ hF hn]

end CFSG.KC.S2071

end
