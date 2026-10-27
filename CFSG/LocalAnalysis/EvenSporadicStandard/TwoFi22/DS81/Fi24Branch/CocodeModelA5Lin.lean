module

public import CFSG.Quasithin.Background.HMathieuBits

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Lin

open CFSG.Quasithin.H.Mathieu

@[expose] def unpackL : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, u => u % 16 :: unpackL n (u / 16)

@[expose] def evalU (u c : ℕ) : ℕ := actM (unpackL 6 u) c

theorem xor_mod_16 (a b : ℕ) : (a ^^^ b) % 16 = a % 16 ^^^ b % 16 := by
  simpa using Nat.xor_mod_two_pow (a := a) (b := b) (n := 4)

theorem xor_div_16 (a b : ℕ) : (a ^^^ b) / 16 = a / 16 ^^^ b / 16 := by
  simpa using Nat.xor_div_two_pow (a := a) (b := b) (n := 4)

theorem actM_unpackL_xor : ∀ (n u v m : ℕ), actM (unpackL n (u ^^^ v)) m =
    actM (unpackL n u) m ^^^ actM (unpackL n v) m := by
  intro n
  induction n with
  | zero => intro u v m; simp [unpackL, actM]
  | succ n ih =>
    intro u v m
    rw [unpackL, unpackL, unpackL, actM, actM, actM, xor_mod_16, xor_div_16, ih]
    by_cases h : m % 2 = 1
    · simp only [h, if_true]; ac_rfl
    · simp only [h, if_false, Nat.zero_xor]

theorem xorLin_evalU (c : ℕ) : XorLin (fun u => evalU u c) := by
  intro a b
  simpa [evalU] using actM_unpackL_xor 6 a b c

theorem XorLin.xor' {f g : ℕ → ℕ} (hf : XorLin f) (hg : XorLin g) :
    XorLin (fun u => f u ^^^ g u) := by
  intro a b
  show f (a ^^^ b) ^^^ g (a ^^^ b) = (f a ^^^ g a) ^^^ (f b ^^^ g b)
  rw [hf a b, hg a b]
  ac_rfl

theorem xorLin_foldr {ι : Type*} (f : ι → ℕ → ℕ) (hf : ∀ i, XorLin (f i)) :
    ∀ l : List ι, XorLin (fun u => l.foldr (fun i acc => f i u ^^^ acc) 0) := by
  intro l
  induction l with
  | nil =>
    intro a b
    simp
  | cons i l ih =>
    intro a b
    simp only [List.foldr_cons]
    rw [hf i a b]
    have hih : List.foldr (fun i acc => f i (a ^^^ b) ^^^ acc) 0 l =
        List.foldr (fun i acc => f i a ^^^ acc) 0 l ^^^
          List.foldr (fun i acc => f i b ^^^ acc) 0 l := ih a b
    rw [hih]
    ac_rfl

theorem foldr_xor_zero {ι : Type*} (f : ι → ℕ) :
    ∀ l : List ι, (∀ i ∈ l, f i = 0) → l.foldr (fun i acc => f i ^^^ acc) 0 = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons i l ih =>
    intro h
    rw [List.foldr_cons, h i (List.mem_cons_self ..), Nat.zero_xor]
    exact ih fun j hj => h j (List.mem_cons_of_mem i hj)

private lemma add16_mod (x y : ℕ) : (x + 16 * y) % 16 = x % 16 :=
  Nat.add_mul_mod_self_left x 16 y

private lemma add16_div (x y : ℕ) : (x + 16 * y) / 16 = x / 16 + y :=
  Nat.add_mul_div_left x y (by norm_num)

theorem unpackL_pack {a b c d e f : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (he : e < 16) (hf : f < 16) :
    unpackL 6 (a + 16 * (b + 16 * (c + 16 * (d + 16 * (e + 16 * f))))) = [a, b, c, d, e, f] := by
  simp only [unpackL, add16_mod, add16_div, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
    Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hd, Nat.div_eq_of_lt he, Nat.div_eq_of_lt hf,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf, Nat.zero_add, Nat.add_zero]

theorem pack_lt {a b c d e f : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (he : e < 16) (hf : f < 16) :
    a + 16 * (b + 16 * (c + 16 * (d + 16 * (e + 16 * f)))) < 2 ^ 24 := by
  norm_num
  omega

@[expose] def cPs : List ℕ := [12, 4, 10, 15, 20, 40, 2, 3, 14, 7, 18, 35]

@[expose] def mqs : List (List ℕ) := [[3, 5, 9, 1], [5, 4, 6, 12]]

@[expose] def tBlk : List (List (List ℕ)) :=
  [[[6, 3, 8, 1], [3, 13, 15, 7], [6, 3, 8, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [8, 15, 12, 2]],
   [[2, 1, 12, 5], [1, 15, 11, 7], [2, 1, 12, 5], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [13, 9, 14, 12]],
   [[5, 3, 8, 10], [2, 12, 3, 7], [5, 3, 8, 10], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [11, 2, 13, 8]],
   [[8, 7, 13, 1], [4, 7, 13, 8], [9, 5, 9, 9], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [10, 12, 5, 13]],
   [[3, 14, 7, 6], [1, 11, 14, 2], [3, 14, 7, 6], [0, 0, 0, 0], [15, 1, 12, 7], [0, 0, 0, 0],
    [9, 1, 4, 7]],
   [[7, 2, 4, 15], [12, 2, 4, 7], [8, 3, 8, 8], [0, 0, 0, 0], [0, 0, 0, 0], [15, 1, 12, 7],
    [6, 11, 3, 4]]]

@[expose] def resid (k u : ℕ) : ℕ :=
  evalU u (cPs.getD k 0) ^^^ actM (mqs.getD (k / 6) []) (evalU u (2 ^ (k % 6)))

@[expose] def leftInv (l u : ℕ) : ℕ :=
  (List.range 7).foldr (fun k acc => actM ((tBlk.getD l []).getD k []) (resid k u) ^^^ acc) 0

theorem xorLin_resid (k : ℕ) : XorLin (resid k) :=
  XorLin.xor' (xorLin_evalU _) ((actM_xor _).comp (xorLin_evalU _))

theorem xorLin_leftInv (l : ℕ) : XorLin (leftInv l) :=
  xorLin_foldr (fun k u => actM ((tBlk.getD l []).getD k []) (resid k u))
    (fun _ => (actM_xor _).comp (xorLin_resid _)) (List.range 7)

theorem leftInv_units : ∀ l < 6, matOf 24 (fun u => evalU u (2 ^ l)) = matOf 24 (leftInv l) := by
  decide +kernel

theorem leftInv_eq {l : ℕ} (hl : l < 6) {u : ℕ} (hu : u < 2 ^ 24) :
    evalU u (2 ^ l) = leftInv l u := by
  rw [← actM_matOf (xorLin_evalU (2 ^ l)) 24 u hu, ← actM_matOf (xorLin_leftInv l) 24 u hu,
    leftInv_units l hl]

theorem cPs_lt : ∀ k < 7, cPs.getD k 0 < 64 := by decide

theorem xorLin_ext {f g : ℕ → ℕ} (hf : XorLin f) (hg : XorLin g) (n : ℕ)
    (h : ∀ j < n, f (2 ^ j) = g (2 ^ j)) : ∀ m < 2 ^ n, f m = g m := by
  intro m hm
  rw [← actM_matOf hf n m hm, ← actM_matOf hg n m hm]
  congr 1
  exact List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

theorem lin_vanish (g : ℕ → ℕ) (hg : XorLin g) (hlt : ∀ c, g c < 16)
    (h : ∀ k < 7, k ≠ 3 → g (cPs.getD k 0) = actM (mqs.getD (k / 6) []) (g (2 ^ (k % 6)))) :
    ∀ c < 64, g c = 0 := by
  have hz : ∀ x, actM [0, 0, 0, 0] x = 0 := fun x => by simp [actM]
  have h3 : ∀ l < 6, (tBlk.getD l []).getD 3 [] = [0, 0, 0, 0] := by decide
  have hul : unpackL 6 (g 1 + 16 * (g 2 + 16 * (g 4 + 16 * (g 8 + 16 * (g 16 + 16 * g 32))))) =
      matOf 6 g := by
    rw [unpackL_pack (hlt 1) (hlt 2) (hlt 4) (hlt 8) (hlt 16) (hlt 32)]
    rfl
  set u : ℕ := g 1 + 16 * (g 2 + 16 * (g 4 + 16 * (g 8 + 16 * (g 16 + 16 * g 32)))) with hu
  have hu24 : u < 2 ^ 24 := pack_lt (hlt 1) (hlt 2) (hlt 4) (hlt 8) (hlt 16) (hlt 32)
  have hev : ∀ c < 64, evalU u c = g c := fun c hc => by
    rw [evalU, hul, actM_matOf hg 6 c hc]
  have hpow : ∀ i < 6, 2 ^ i < 64 := by decide
  have hres : ∀ k < 7, k ≠ 3 → resid k u = 0 := fun k hk hk3 => by
    rw [resid, hev _ (cPs_lt k hk), hev _ (hpow _ (Nat.mod_lt _ (by norm_num))), h k hk hk3,
      Nat.xor_self]
  have hl : ∀ l < 6, g (2 ^ l) = 0 := fun l hl => by
    rw [← hev (2 ^ l) (hpow l hl), leftInv_eq hl hu24, leftInv]
    refine foldr_xor_zero _ _ fun k hk => ?_
    have hk7 : k < 7 := List.mem_range.1 hk
    by_cases hk3 : k = 3
    · subst hk3
      rw [h3 l hl]
      exact hz _
    · rw [hres k hk7 hk3]
      exact (actM_xor _).map_zero
  intro c hc
  rw [← actM_matOf hg 6 c hc]
  have h0 : matOf 6 g = [0, 0, 0, 0, 0, 0] := by
    have e : matOf 6 g = [g (2 ^ 0), g (2 ^ 1), g (2 ^ 2), g (2 ^ 3), g (2 ^ 4), g (2 ^ 5)] := rfl
    rw [e, hl 0 (by norm_num), hl 1 (by norm_num), hl 2 (by norm_num), hl 3 (by norm_num),
      hl 4 (by norm_num), hl 5 (by norm_num)]
  rw [h0]
  simp [actM]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Lin
