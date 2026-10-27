module

public import Certificates.Data.Kernel.Misc.OrbPath
public import Certificates.Data.Kernel.Misc.F2BfsRec
public import CFSG.Sporadic.HeldB.Common
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.KC.WordPts

open CFSG.KLie.CT CFSG.KS CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
open CFSG.KC.Enum (pg strictN)
open CFSG.Monster.B.Co2.Native (lettersOK)

variable {n : ℕ}

@[expose] def PackRep (n w t : ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, pg w (mask w) t x = (g x : ℕ)

@[expose] def LetRep (n w : ℕ) (G GI : ℕ → ℕ) (gs : List (Equiv.Perm (Fin n))) : Prop :=
  ∀ k < gs.length, PackRep n w (G k) (gs.getD k 1) ∧ PackRep n w (GI k) (gs.getD k 1)⁻¹

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem imgP_rep {w t : ℕ} {g : Equiv.Perm (Fin n)} (h : PackRep n w t g) (x : Fin n) :
    imgP n w t x = (g x : ℕ) := by
  have hx : Nat.blt (x : ℕ) n = true := Nat.blt_eq.mpr x.2
  change Bool.rec (motive := fun _ => ℕ) 0 (pg w (mask w) t x) (Nat.blt (x : ℕ) n) = _
  rw [hx]
  exact h x

theorem evalSignedWord_nil' (gs : List (Equiv.Perm (Fin n))) : evalSignedWord gs [] = 1 := by
  rw [evalSignedWord, ite_eq_left (by rfl)]
  rfl

theorem evalSignedWord_cons' {gs : List (Equiv.Perm (Fin n))} {l : ℤ} {w : List ℤ}
    (hl : l ≠ 0 ∧ l.natAbs ≤ gs.length) (hw : lettersOK gs.length w = true) :
    evalSignedWord gs (l :: w) =
      (if 0 < l then gs.getD (l.natAbs - 1) 1 else (gs.getD (l.natAbs - 1) 1)⁻¹) *
        evalSignedWord gs w := by
  have hlw : lettersOK gs.length (l :: w) = true := by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw ⊢
    exact ⟨hl, hw⟩
  rw [evalSignedWord, ite_eq_left hlw, evalSignedWord, ite_eq_left hw]
  have hcons : toLetters gs.length (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
      toLetters gs.length w := by
    simp [toLetters, hl.1, hl.2]
  rw [hcons, Quiver.SchreierGraph.evalWord, Quiver.SchreierGraph.evalWord,
    show FreeGroup.mk ((⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: toLetters gs.length w) =
      FreeGroup.mk [(⟨l.natAbs - 1, by omega⟩, decide (0 < l))] *
        FreeGroup.mk (toLetters gs.length w) from rfl, map_mul]
  congr 1
  have hget : gs.get ⟨l.natAbs - 1, by omega⟩ = gs.getD (l.natAbs - 1) 1 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    rfl
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, decide_eq_true hpos,
      show FreeGroup.mk [((⟨l.natAbs - 1, by omega⟩ : Fin gs.length), true)] =
        FreeGroup.of ⟨l.natAbs - 1, by omega⟩ from rfl, FreeGroup.lift_apply_of, hget]
  · rw [ite_eq_right hpos, decide_eq_false hpos,
      show FreeGroup.mk [((⟨l.natAbs - 1, by omega⟩ : Fin gs.length), false)] =
        (FreeGroup.of ⟨l.natAbs - 1, by omega⟩)⁻¹ from rfl, map_inv, FreeGroup.lift_apply_of,
      hget]

variable {w : ℕ} {G GI : ℕ → ℕ} {gs : List (Equiv.Perm (Fin n))}

theorem letP_rep (hG : LetRep n w G GI gs) {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ gs.length) :
    PackRep n w (letP G GI z)
        (if 0 < z then gs.getD (z.natAbs - 1) 1 else (gs.getD (z.natAbs - 1) 1)⁻¹) ∧
      PackRep n w (letP GI G z)
        (if 0 < z then gs.getD (z.natAbs - 1) 1 else (gs.getD (z.natAbs - 1) 1)⁻¹)⁻¹ := by
  rcases z with k | k
  · have hk : k ≠ 0 := by
      rintro rfl
      exact hz.1 rfl
    have hpos : (0 : ℤ) < Int.ofNat k := by
      rw [Int.ofNat_eq_coe]
      exact_mod_cast Nat.pos_of_ne_zero hk
    rw [if_pos hpos]
    have e : (Int.ofNat k).natAbs - 1 = k - 1 := rfl
    rw [e]
    have hk2 : k ≤ gs.length := hz.2
    exact hG (k - 1) (by omega)
  · have hneg : ¬ (0 : ℤ) < Int.negSucc k := by simp
    rw [if_neg hneg, inv_inv]
    have e : (Int.negSucc k).natAbs - 1 = k := rfl
    rw [e]
    have hk2 : k + 1 ≤ gs.length := hz.2
    have hk : k < gs.length := by omega
    exact ⟨(hG k hk).2, (hG k hk).1⟩

theorem letters_cons {k : ℕ} {z : ℤ} {wd : List ℤ} (h : lettersOK k (z :: wd) = true) :
    (z ≠ 0 ∧ z.natAbs ≤ k) ∧ lettersOK k wd = true := by
  simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  exact h

theorem evW_eq (hG : LetRep n w G GI gs) :
    ∀ {wd : List ℤ}, lettersOK gs.length wd = true →
      ∀ x : Fin n, evW n w G GI wd x = (evalSignedWord gs wd x : ℕ)
  | [], _, x => by rw [evalSignedWord_nil']; rfl
  | z :: wd, h, x => by
    obtain ⟨hz, hwd⟩ := letters_cons h
    change strictN (evW n w G GI wd x) (fun q => imgP n w (letP G GI z) q) = _
    rw [strictN_eq', evW_eq hG hwd x, imgP_rep (letP_rep hG hz).1, evalSignedWord_cons' hz hwd,
      Equiv.Perm.mul_apply]

theorem evIW_eq (hG : LetRep n w G GI gs) :
    ∀ {wd : List ℤ}, lettersOK gs.length wd = true →
      ∀ x : Fin n, evIW n w G GI wd x = ((evalSignedWord gs wd)⁻¹ x : ℕ)
  | [], _, x => by rw [evalSignedWord_nil']; rfl
  | z :: wd, h, x => by
    obtain ⟨hz, hwd⟩ := letters_cons h
    change strictN (imgP n w (letP GI G z) x) (fun q => evIW n w G GI wd q) = _
    rw [strictN_eq', imgP_rep (letP_rep hG hz).2, evIW_eq hG hwd, evalSignedWord_cons' hz hwd,
      mul_inv_rev, Equiv.Perm.mul_apply]

theorem evWs_eq (hG : LetRep n w G GI gs) :
    ∀ {ws : List (List ℤ)}, (∀ wd ∈ ws, lettersOK gs.length wd = true) →
      ∀ x : Fin n, evWs n w G GI ws x = ((ws.map (evalSignedWord gs)).prod x : ℕ)
  | [], _, x => rfl
  | wd :: ws, h, x => by
    change strictN (evWs n w G GI ws x) (fun q => evW n w G GI wd q) = _
    rw [strictN_eq', evWs_eq hG (fun v hv => h v (List.mem_cons_of_mem _ hv)) x,
      evW_eq hG (h wd List.mem_cons_self), List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem eqPtsK_sound (hG : LetRep n w G GI gs) {xs ys : List (List ℤ)}
    (hx : ∀ wd ∈ xs, lettersOK gs.length wd = true) (hy : ∀ wd ∈ ys, lettersOK gs.length wd = true) :
    ∀ {bs : List ℕ}, eqPtsK n w G GI bs xs ys = true → ∀ x : Fin n, (x : ℕ) ∈ bs →
      (xs.map (evalSignedWord gs)).prod x = (ys.map (evalSignedWord gs)).prod x
  | [], _, _, hb => absurd hb List.not_mem_nil
  | b :: bs, h, x, hb => by
    have h' : andB (Nat.beq (evWs n w G GI xs b) (evWs n w G GI ys b)) (eqPtsK n w G GI bs xs ys) =
      true := h
    cases h1 : Nat.beq (evWs n w G GI xs b) (evWs n w G GI ys b) <;> rw [h1] at h'
    · exact absurd h' Bool.false_ne_true
    rcases List.mem_cons.mp hb with e | hb
    · subst e
      apply Fin.ext
      rw [← evWs_eq hG hx, ← evWs_eq hG hy]
      exact Nat.eq_of_beq_eq_true h1
    · exact eqPtsK_sound hG hx hy h' x hb

theorem fixPtsK_sound (hG : LetRep n w G GI gs) {xs : List (List ℤ)}
    (hx : ∀ wd ∈ xs, lettersOK gs.length wd = true) :
    ∀ {bs : List ℕ}, fixPtsK n w G GI bs xs = true → ∀ x : Fin n, (x : ℕ) ∈ bs →
      (xs.map (evalSignedWord gs)).prod x = x
  | [], _, _, hb => absurd hb List.not_mem_nil
  | b :: bs, h, x, hb => by
    have h' : andB (Nat.beq (evWs n w G GI xs b) b) (fixPtsK n w G GI bs xs) = true := h
    cases h1 : Nat.beq (evWs n w G GI xs b) b <;> rw [h1] at h'
    · exact absurd h' Bool.false_ne_true
    rcases List.mem_cons.mp hb with e | hb
    · subst e
      apply Fin.ext
      rw [← evWs_eq hG hx]
      exact Nat.eq_of_beq_eq_true h1
    · exact fixPtsK_sound hG hx h' x hb

theorem conjPtsK_sound (hG : LetRep n w G GI gs) {g b : List ℤ} {ys : List (List ℤ)}
    (hg : lettersOK gs.length g = true) (hb : lettersOK gs.length b = true)
    (hy : ∀ wd ∈ ys, lettersOK gs.length wd = true) :
    ∀ {bs : List ℕ}, conjPtsK n w G GI bs g b ys = true → ∀ x : Fin n, (x : ℕ) ∈ bs →
      (evalSignedWord gs g * evalSignedWord gs b * (evalSignedWord gs g)⁻¹) x =
        (ys.map (evalSignedWord gs)).prod x
  | [], _, _, hp => absurd hp List.not_mem_nil
  | p :: bs, h, x, hp => by
    have h' : andB (Nat.beq (evW n w G GI g (evW n w G GI b (evIW n w G GI g p)))
      (evWs n w G GI ys p)) (conjPtsK n w G GI bs g b ys) = true := h
    cases h1 : Nat.beq (evW n w G GI g (evW n w G GI b (evIW n w G GI g p)))
      (evWs n w G GI ys p) <;> rw [h1] at h'
    · exact absurd h' Bool.false_ne_true
    rcases List.mem_cons.mp hp with e | hp
    · subst e
      apply Fin.ext
      rw [← evWs_eq hG hy, ← Nat.eq_of_beq_eq_true h1, evIW_eq hG hg, evW_eq hG hb,
        evW_eq hG hg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    · exact conjPtsK_sound hG hg hb hy h' x hp

private theorem andB_tt {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem allN_tt {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) : ∀ i < m, f i = true := by
  induction m with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    obtain ⟨h1, h2⟩ := andB_tt (a := f m) (b := allN m f) h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

private theorem strictB_eq'' (y : ℕ) (k : ℕ → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

private theorem pw2_eq (k : ℕ) : pw2 k = 2 ^ k := by
  change 1 <<< k = 2 ^ k
  rw [Nat.shiftLeft_eq, one_mul]

private theorem land_maskN_lt (x w : ℕ) : Nat.land x (maskN w) < 2 ^ w := by
  have h1 : maskN w = 2 ^ w - 1 := by
    change pw2 w - 1 = 2 ^ w - 1
    rw [pw2_eq]
  have h2 : Nat.land x (maskN w) ≤ maskN w := Nat.and_le_right
  have h3 : 0 < 2 ^ w := Nat.two_pow_pos w
  omega

private theorem mono_of_succ {N : ℕ} {K : ℕ → ℕ} (h : ∀ k, k + 1 < N → K k < K (k + 1)) :
    ∀ k k', k < k' → k' < N → K k < K k' := by
  intro k k' hkk' hk'
  induction k' with
  | zero => omega
  | succ k' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkk' with h' | rfl
    · exact lt_trans (ih h' (by omega)) (h k' hk')
    · exact h k hk'

private theorem inj_of_succ {N : ℕ} {K : ℕ → ℕ} (h : ∀ k, k + 1 < N → K k < K (k + 1)) :
    ∀ k < N, ∀ k' < N, K k = K k' → k = k' := by
  intro k hk k' hk' e
  rcases Nat.lt_trichotomy k k' with h' | h' | h'
  · exact absurd e (ne_of_lt (mono_of_succ h k k' h' hk'))
  · exact h'
  · exact absurd e (ne_of_gt (mono_of_succ h k' k h' hk))

private noncomputable def selFrom (B : List (List ℤ)) (c : ℕ) : ℕ → List (List ℤ) :=
  List.rec (motive := fun _ => ℕ → List (List ℤ)) (fun _ => [])
    (fun b _ ih r => Bool.rec (motive := fun _ => List (List ℤ)) (ih (Nat.succ r))
      (b :: ih (Nat.succ r)) (bit c r)) B

private theorem selFrom_mem (c : ℕ) : ∀ (B : List (List ℤ)) (r : ℕ), ∀ wd ∈ selFrom B c r, wd ∈ B
  | [], _, _, h => absurd h List.not_mem_nil
  | b :: B, r, wd, h => by
    have e : selFrom (b :: B) c r = Bool.rec (motive := fun _ => List (List ℤ))
        (selFrom B c (Nat.succ r)) (b :: selFrom B c (Nat.succ r)) (bit c r) := rfl
    rw [e] at h
    cases hb : bit c r <;> rw [hb] at h
    · exact List.mem_cons_of_mem _ (selFrom_mem c B _ wd h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (selFrom_mem c B _ wd h)

private theorem getD_letters {k : ℕ} {B : List (List ℤ)} (hB : ∀ wd ∈ B, lettersOK k wd = true) (i : ℕ) :
    lettersOK k (B.getD i []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases e : B[i]? with
  | none => rfl
  | some v => exact hB v (List.mem_of_getElem? e)

private theorem fixPtsK_false {xs : List (List ℤ)} :
    ∀ {bs : List ℕ}, fixPtsK n w G GI bs xs = false → ∃ b ∈ bs, evWs n w G GI xs b ≠ b
  | [], h => Bool.noConfusion (h : true = false)
  | b :: bs, h => by
    have h' : andB (Nat.beq (evWs n w G GI xs b) b) (fixPtsK n w G GI bs xs) = false := h
    cases h1 : Nat.beq (evWs n w G GI xs b) b
    · exact ⟨b, List.mem_cons_self, Nat.ne_of_beq_eq_false h1⟩
    · rw [h1] at h'
      obtain ⟨b', hb', hne⟩ := fixPtsK_false (bs := bs) h'
      exact ⟨b', List.mem_cons_of_mem _ hb', hne⟩

theorem ebK_sound (hG : LetRep n w G GI gs) {bs : List ℕ} (hbs : ∀ b ∈ bs, b < n)
    {B : List (List ℤ)} (hB : ∀ wd ∈ B, lettersOK gs.length wd = true) {k : ℕ}
    (h : ebK n w G GI bs B k = true) :
    B.length = k ∧
      (∀ i < k, ∀ x : Fin n, (x : ℕ) ∈ bs →
        (evalSignedWord gs (B.getD i []) * evalSignedWord gs (B.getD i [])) x = x) ∧
      (∀ i < k, ∀ j < k, ∀ x : Fin n, (x : ℕ) ∈ bs →
        (evalSignedWord gs (B.getD i []) * evalSignedWord gs (B.getD j [])) x =
          (evalSignedWord gs (B.getD j []) * evalSignedWord gs (B.getD i [])) x) ∧
      ∀ c, 0 < c → c < 2 ^ k → ∃ x : Fin n, (x : ℕ) ∈ bs ∧
        ((selW B c).map (evalSignedWord gs)).prod x ≠ x := by
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h⟩ := andB_tt h
  obtain ⟨h3, h4⟩ := andB_tt h
  have hpair : ∀ i j, ∀ wd ∈ [B.getD i [], B.getD j []], lettersOK gs.length wd = true := by
    intro i j wd hwd
    rcases List.mem_cons.mp hwd with rfl | hwd
    · exact getD_letters hB i
    rcases List.mem_cons.mp hwd with rfl | hwd
    · exact getD_letters hB j
    exact absurd hwd List.not_mem_nil
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_, ?_, ?_⟩
  · intro i hi x hx
    have e := fixPtsK_sound hG (hpair i i) (allN_tt h2 i hi) x hx
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at e
    exact e
  · intro i hi j hj x hx
    have e := eqPtsK_sound hG (hpair i j) (hpair j i) (allN_tt (allN_tt h3 i hi) j hj) x hx
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at e
    exact e
  · intro c hc0 hck
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hn : notB (fixPtsK n w G GI bs (selW B (c' + 1))) = true :=
      allN_tt h4 c' (by change c' < pw2 k - 1; rw [pw2_eq]; omega)
    have hf : fixPtsK n w G GI bs (selW B (c' + 1)) = false := by
      cases e : fixPtsK n w G GI bs (selW B (c' + 1))
      · rfl
      · rw [e] at hn
        exact absurd hn Bool.false_ne_true
    obtain ⟨b, hb, hne⟩ := fixPtsK_false hf
    refine ⟨⟨b, hbs b hb⟩, hb, fun heq => hne ?_⟩
    have e : evWs n w G GI (selW B (c' + 1)) b =
        ((((selW B (c' + 1)).map (evalSignedWord gs)).prod ⟨b, hbs b hb⟩ : Fin n) : ℕ) :=
      evWs_eq hG (fun v hv => hB v (selFrom_mem _ B 0 v hv)) ⟨b, hbs b hb⟩
    rw [heq] at e
    exact e

theorem matK_sound (hG : LetRep n w G GI gs) {bs : List ℕ} {B : List (List ℤ)}
    (hB : ∀ wd ∈ B, lettersOK gs.length wd = true) {k : ℕ} {g : List ℤ}
    (hg : lettersOK gs.length g = true) {M : ℕ} (h : matK n w G GI bs B k g M = true) :
    ∀ i < k, ∀ x : Fin n, (x : ℕ) ∈ bs →
      (evalSignedWord gs g * evalSignedWord gs (B.getD i []) * (evalSignedWord gs g)⁻¹) x =
        ((selW B (colF k M i)).map (evalSignedWord gs)).prod x := by
  intro i hi x hx
  have hc : conjPtsK n w G GI bs g (B.getD i []) (selW B (colF k M i)) = true := allN_tt h i hi
  exact conjPtsK_sound hG hg (getD_letters hB i) (fun v hv => hB v (selFrom_mem _ B 0 v hv)) hc x hx

end CFSG.KC.WordPts

namespace CFSG.KC.OrbPath

open CFSG.KLie.CT CFSG.KS CFSG.Sporadic.HeldB CFSG.KC.WordPts
open CFSG.KC.Enum (pg strictN)
open CFSG.Monster.B.Co2.Native (lettersOK)

variable {n : ℕ}

private noncomputable def digE (hs : List (Equiv.Perm (Fin n))) (d : ℕ) : Equiv.Perm (Fin n) :=
  if d = 0 then 1 else hs.getD (d - 1) 1

private noncomputable def pathE (hs : List (Equiv.Perm (Fin n))) : ℕ → ℕ → Equiv.Perm (Fin n)
  | 0, _ => 1
  | f + 1, P => digE hs (Nat.land P 3) * pathE hs f (Nat.shiftRight P 2)

private noncomputable def keyFrom (n w : ℕ) (G GI H : ℕ → ℕ) (f P y : ℕ) (T : List (List ℤ)) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun t _ ih i => Nat.lor (Nat.shiftLeft (pathAp n w H f P (evW n w G GI t y)) (Nat.mul w i))
      (ih (Nat.succ i))) T

private theorem digP_eq {w : ℕ} {H HI : ℕ → ℕ} {hs : List (Equiv.Perm (Fin n))} (hH3 : hs.length = 3)
    (hH : LetRep n w H HI hs) {d : ℕ} (hd : d ≤ 3) (x : Fin n) :
    digP n w H d x = (digE hs d x : ℕ) ∧ digP n w HI d x = ((digE hs d)⁻¹ x : ℕ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · have e : digE hs 0 = 1 := if_pos rfl
    rw [e, inv_one]
    exact ⟨rfl, rfl⟩
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have e : digE hs (d' + 1) = hs.getD d' 1 := if_neg (Nat.succ_ne_zero d')
    rw [e]
    exact ⟨imgP_rep (hH d' (by omega)).1 x, imgP_rep (hH d' (by omega)).2 x⟩

private theorem pathAp_eq {w : ℕ} {H HI : ℕ → ℕ} {hs : List (Equiv.Perm (Fin n))} (hH3 : hs.length = 3)
    (hH : LetRep n w H HI hs) :
    ∀ (f P : ℕ) (x : Fin n), pathAp n w H f P x = (pathE hs f P x : ℕ) ∧
      pathApI n w HI f P x = ((pathE hs f P)⁻¹ x : ℕ)
  | 0, _, _ => ⟨rfl, rfl⟩
  | f + 1, P, x => by
    have hd : Nat.land P 3 ≤ 3 := Nat.and_le_right
    constructor
    · change strictN (pathAp n w H f (Nat.shiftRight P 2) x)
        (fun y => digP n w H (Nat.land P 3) y) = _
      rw [strictN_eq', (pathAp_eq hH3 hH f _ x).1, (digP_eq hH3 hH hd _).1]
      rfl
    · change strictN (digP n w HI (Nat.land P 3) x)
        (fun y => pathApI n w HI f (Nat.shiftRight P 2) y) = _
      rw [strictN_eq', (digP_eq hH3 hH hd x).2, (pathAp_eq hH3 hH f _ _).2]
      change _ = (((digE hs (Nat.land P 3) * pathE hs f (Nat.shiftRight P 2))⁻¹ x : Fin n) : ℕ)
      rw [mul_inv_rev, Equiv.Perm.mul_apply]

private theorem getD_mem_closure (hs : List (Equiv.Perm (Fin n))) (i : ℕ) :
    hs.getD i 1 ∈ Subgroup.closure {x | x ∈ hs} := by
  rw [List.getD_eq_getElem?_getD]
  cases e : hs[i]? with
  | none => exact Subgroup.one_mem _
  | some v => exact Subgroup.subset_closure (List.mem_of_getElem? e)

private theorem pathE_mem (hs : List (Equiv.Perm (Fin n))) :
    ∀ f P, pathE hs f P ∈ Subgroup.closure {x | x ∈ hs}
  | 0, _ => Subgroup.one_mem _
  | f + 1, P => by
    refine Subgroup.mul_mem _ ?_ (pathE_mem hs f _)
    unfold digE
    split
    · exact Subgroup.one_mem _
    · exact getD_mem_closure hs _

private theorem keyFrom_congr {w : ℕ} {G GI H HI : ℕ → ℕ} {gs hs : List (Equiv.Perm (Fin n))}
    (hG : LetRep n w G GI gs) (hH3 : hs.length = 3) (hH : LetRep n w H HI hs) {f b : ℕ}
    (hb : b < n) {P P' : ℕ} :
    ∀ {T : List (List ℤ)}, (∀ t ∈ T, lettersOK gs.length t = true) →
      (∀ t ∈ T, pathE hs f P * evalSignedWord gs t * (pathE hs f P)⁻¹ =
        pathE hs f P' * evalSignedWord gs t * (pathE hs f P')⁻¹) → ∀ i,
      keyFrom n w G GI H f P ((pathE hs f P)⁻¹ ⟨b, hb⟩ : Fin n) T i =
        keyFrom n w G GI H f P' ((pathE hs f P')⁻¹ ⟨b, hb⟩ : Fin n) T i
  | [], _, _, _ => rfl
  | t :: T, hT, he, i => by
    have hT' : ∀ t ∈ T, lettersOK gs.length t = true :=
      fun v hv => hT v (List.mem_cons_of_mem _ hv)
    have he' : ∀ v ∈ T, pathE hs f P * evalSignedWord gs v * (pathE hs f P)⁻¹ =
        pathE hs f P' * evalSignedWord gs v * (pathE hs f P')⁻¹ :=
      fun v hv => he v (List.mem_cons_of_mem _ hv)
    have key : pathAp n w H f P (evW n w G GI t ((pathE hs f P)⁻¹ ⟨b, hb⟩ : Fin n)) =
        pathAp n w H f P' (evW n w G GI t ((pathE hs f P')⁻¹ ⟨b, hb⟩ : Fin n)) := by
      have ht := hT t List.mem_cons_self
      rw [evW_eq hG ht, evW_eq hG ht, (pathAp_eq hH3 hH f P _).1, (pathAp_eq hH3 hH f P' _).1]
      have e := congrArg (fun p : Equiv.Perm (Fin n) => (p ⟨b, hb⟩ : ℕ)) (he t List.mem_cons_self)
      simp only [Equiv.Perm.mul_apply] at e
      exact e
    change Nat.lor (Nat.shiftLeft (pathAp n w H f P (evW n w G GI t
        ((pathE hs f P)⁻¹ ⟨b, hb⟩ : Fin n))) (Nat.mul w i))
        (keyFrom n w G GI H f P ((pathE hs f P)⁻¹ ⟨b, hb⟩ : Fin n) T (Nat.succ i)) =
      Nat.lor (Nat.shiftLeft (pathAp n w H f P' (evW n w G GI t
        ((pathE hs f P')⁻¹ ⟨b, hb⟩ : Fin n))) (Nat.mul w i))
        (keyFrom n w G GI H f P' ((pathE hs f P')⁻¹ ⟨b, hb⟩ : Fin n) T (Nat.succ i))
    rw [key, keyFrom_congr hG hH3 hH hb hT' he' (Nat.succ i)]

theorem orbRecK_sound {w : ℕ} (hn : n ≤ 2 ^ w) {G GI H HI : ℕ → ℕ}
    {gs hs : List (Equiv.Perm (Fin n))} (hG : LetRep n w G GI gs) (hH3 : hs.length = 3)
    (hH : LetRep n w H HI hs) {f b : ℕ} (hb : b < n) {T : List (List ℤ)}
    (hT : ∀ t ∈ T, lettersOK gs.length t = true) {rw lb N : ℕ} {CF : ℕ → ℕ}
    (h : ∀ k < N, orbRecK n w G GI H HI f b T rw lb CF N k = true) :
    ∃ c : ℕ → Equiv.Perm (Fin n), (∀ k < N, c k ∈ Subgroup.closure {x | x ∈ hs}) ∧
      ∀ k < N, ∀ k' < N,
        (∀ t ∈ T, c k * evalSignedWord gs t * (c k)⁻¹ = c k' * evalSignedWord gs t * (c k')⁻¹) →
          k = k' := by
  let kw := Nat.mul w T.length
  let Pk : ℕ → ℕ := fun k => Nat.shiftRight (recAt rw lb CF k) kw
  let Kc : ℕ → ℕ := fun k => Nat.land (recAt rw lb CF k) (maskN kw)
  have hrec : ∀ k < N, Nat.beq (keyK n w G GI H HI f b T (Pk k)) (Kc k) = true ∧
      Bool.rec (motive := fun _ => Bool) true (Nat.blt (Kc k) (Kc (Nat.succ k)))
        (Nat.blt (Nat.succ k) N) = true := by
    intro k hk
    have hk' := h k hk
    unfold orbRecK at hk'
    simp only [strictB_eq''] at hk'
    exact andB_tt hk'
  have hkey : ∀ k < N, keyK n w G GI H HI f b T (Pk k) = Kc k :=
    fun k hk => Nat.eq_of_beq_eq_true (hrec k hk).1
  have hinc : ∀ k, k + 1 < N → Kc k < Kc (k + 1) := by
    intro k hk1
    have e := (hrec k (by omega)).2
    have e1 : Nat.blt (Nat.succ k) N = true := Nat.ble_eq_true_of_le hk1
    rw [e1] at e
    exact Nat.le_of_ble_eq_true e
  refine ⟨fun k => pathE hs f (Pk k), fun k _ => pathE_mem hs f _, ?_⟩
  intro k hk k' hk' he
  apply inj_of_succ hinc k hk k' hk'
  rw [← hkey k hk, ← hkey k' hk']
  have e1 : keyK n w G GI H HI f b T (Pk k) =
      keyFrom n w G GI H f (Pk k) (pathApI n w HI f (Pk k) b) T 0 := strictN_eq' _ _
  have e2 : keyK n w G GI H HI f b T (Pk k') =
      keyFrom n w G GI H f (Pk k') (pathApI n w HI f (Pk k') b) T 0 := strictN_eq' _ _
  have i1 := (pathAp_eq hH3 hH f (Pk k) ⟨b, hb⟩).2
  have i2 := (pathAp_eq hH3 hH f (Pk k') ⟨b, hb⟩).2
  rw [e1, e2]
  change keyFrom n w G GI H f (Pk k) (pathApI n w HI f (Pk k) (⟨b, hb⟩ : Fin n)) T 0 =
    keyFrom n w G GI H f (Pk k') (pathApI n w HI f (Pk k') (⟨b, hb⟩ : Fin n)) T 0
  rw [i1, i2]
  exact keyFrom_congr hG hH3 hH hb hT he 0

end CFSG.KC.OrbPath

namespace CFSG.KC.F2BfsRec

open CFSG.KLie.CT CFSG.KC.M1F2

private theorem recK_parts {d w lb ng N k : ℕ} {CF G : ℕ → ℕ} (h : recK d w lb ng CF G N k = true) :
    edgesK d w lb ng CF G N (recAt d w lb ng CF k) (elemAt d w lb ng CF k) = true ∧
      k < fldOf d w (recAt d w lb ng CF k) ng ∧
      rowK d w (recAt d w lb ng CF k) (fldOf d w (recAt d w lb ng CF k) ng) ng =
        nextM d w lb ng CF N k ∧
      sortK d w lb ng CF N k (fldOf d w (recAt d w lb ng CF k) (ng + 1)) = true := by
  unfold recK at h
  simp only [WordPts.strictB_eq''] at h
  obtain ⟨h1, h⟩ := WordPts.andB_tt h
  obtain ⟨h2, h⟩ := WordPts.andB_tt h
  obtain ⟨h3, h4⟩ := WordPts.andB_tt h
  exact ⟨h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3, h4⟩

private theorem edgesK_spec {d w lb ng N r X : ℕ} {CF G : ℕ → ℕ}
    (h : edgesK d w lb ng CF G N r X = true) {j : ℕ} (hj : j < ng) :
    fldOf d w r j < N ∧ elemAt d w lb ng CF (fldOf d w r j) = mulF d X (G j) := by
  have h1 : strictB (fldOf d w r j) (fun t => andB (Nat.blt t N)
      (Nat.beq (elemAt d w lb ng CF t) (mulF d X (G j)))) = true := WordPts.allN_tt h j hj
  rw [WordPts.strictB_eq''] at h1
  obtain ⟨h2, h3⟩ := WordPts.andB_tt h1
  exact ⟨Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

private theorem sortK_spec {d w lb ng N k s : ℕ} {CF : ℕ → ℕ} (h : sortK d w lb ng CF N k s = true) :
    s < N ∧ (k + 1 < N → elemAt d w lb ng CF s <
      elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF (k + 1)) (ng + 1))) := by
  obtain ⟨h1, h2⟩ := WordPts.andB_tt h
  refine ⟨Nat.le_of_ble_eq_true h1, fun hk => ?_⟩
  have e : Nat.blt (Nat.succ k) N = true := Nat.ble_eq_true_of_le hk
  rw [e] at h2
  exact Nat.le_of_ble_eq_true h2

private theorem fldOf_lt (d w r i : ℕ) : fldOf d w r i < 2 ^ w := WordPts.land_maskN_lt _ _

private theorem stK_spec (w t m : ℕ) :
    (t < m ∧ stK w t m = m) ∨ (t = m ∧ stK w t m = Nat.succ m) ∨ stK w t m = 2 ^ w := by
  by_cases h1 : t < m
  · have e : Nat.blt t m = true := Nat.ble_eq_true_of_le h1
    refine Or.inl ⟨h1, ?_⟩
    unfold stK
    rw [e]
  · have e : Nat.blt t m = false := by
      cases h : Nat.blt t m
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) h1
    by_cases h2 : t = m
    · subst h2
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      have e2 : Nat.beq t t = true := Nat.beq_refl t
      unfold stK
      rw [e, e2]
    · have e2 : Nat.beq t m = false := by
        cases h : Nat.beq t m
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h2
      refine Or.inr (Or.inr ?_)
      unfold stK
      rw [e, e2]
      exact WordPts.pw2_eq w

private theorem rowK_good {d w r m ng : ℕ} {Q : ℕ → Prop} (hQ : ∀ j < ng, Q (fldOf d w r j))
    (hm : ∀ t < m, Q t) : ∀ j ≤ ng, rowK d w r m j = 2 ^ w ∨ ∀ t < rowK d w r m j, Q t
  | 0, _ => Or.inr hm
  | j + 1, hj => by
    have e : rowK d w r m (j + 1) = stK w (fldOf d w r j) (rowK d w r m j) := rfl
    have hlt := fldOf_lt d w r j
    rw [e]
    rcases rowK_good hQ hm j (by omega) with h0 | h0 <;>
      rcases stK_spec w (fldOf d w r j) (rowK d w r m j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h2
    · exact Or.inl (h2.trans h0)
    · exact absurd (h1.trans h0) (Nat.ne_of_lt hlt)
    · exact Or.inl h2
    · rw [h2]
      exact Or.inr h0
    · rw [h2]
      refine Or.inr fun t ht => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact h0 t ht
      · rw [← h1]
        exact hQ j (by omega)
    · exact Or.inl h2

private theorem nextM_lt {d w lb ng N k : ℕ} {CF : ℕ → ℕ} (hNw : N < 2 ^ w) :
    nextM d w lb ng CF N k < 2 ^ w := by
  unfold nextM
  cases Nat.blt (Nat.succ k) N
  · exact hNw
  · exact fldOf_lt _ _ _ _

private theorem nextM_of_lt {d w lb ng N k : ℕ} {CF : ℕ → ℕ} (hk : k + 1 < N) :
    nextM d w lb ng CF N k = fldOf d w (recAt d w lb ng CF (k + 1)) ng := by
  have e : Nat.blt (Nat.succ k) N = true := Nat.ble_eq_true_of_le hk
  unfold nextM
  rw [e]

private theorem nextM_last {d w lb ng N k : ℕ} {CF : ℕ → ℕ} (hk : ¬ k + 1 < N) :
    nextM d w lb ng CF N k = N := by
  have e : Nat.blt (Nat.succ k) N = false := by
    cases h : Nat.blt (Nat.succ k) N
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) hk
  unfold nextM
  rw [e]

theorem recK_sound {d w lb ng N : ℕ} {CF G : ℕ → ℕ} (hN : 0 < N) (hNw : N < 2 ^ w)
    (hh : headK d w lb ng CF = true) (h : ∀ k < N, recK d w lb ng CF G N k = true) :
    elemAt d w lb ng CF 0 = idF d ∧
      (∀ k < N, ∀ k' < N, elemAt d w lb ng CF k = elemAt d w lb ng CF k' → k = k') ∧
      (∀ k < N, ∀ j < ng, ∃ t < N, elemAt d w lb ng CF t = mulF d (elemAt d w lb ng CF k) (G j)) ∧
      ∀ P : ℕ → Prop, P (idF d) → (∀ X j, j < ng → P X → P (mulF d X (G j))) →
        ∀ k < N, P (elemAt d w lb ng CF k) := by
  have hh' : elemAt d w lb ng CF 0 = idF d ∧ fldOf d w (recAt d w lb ng CF 0) ng = 1 := by
    unfold headK at hh
    simp only [WordPts.strictB_eq''] at hh
    obtain ⟨h1, h2⟩ := WordPts.andB_tt hh
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  refine ⟨hh'.1, ?_, ?_, ?_⟩
  · have hS : ∀ k, k + 1 < N → elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF k) (ng + 1)) <
        elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF (k + 1)) (ng + 1)) :=
      fun k hk => (sortK_spec (recK_parts (h k (by omega))).2.2.2).2 hk
    have hSinj := WordPts.inj_of_succ hS
    have hSlt : ∀ k < N, fldOf d w (recAt d w lb ng CF k) (ng + 1) < N :=
      fun k hk => (sortK_spec (recK_parts (h k hk)).2.2.2).1
    let σ : Fin N → Fin N := fun k => ⟨fldOf d w (recAt d w lb ng CF k) (ng + 1), hSlt k k.2⟩
    have hσ : Function.Injective σ := by
      intro a b hab
      have e : fldOf d w (recAt d w lb ng CF a) (ng + 1) =
          fldOf d w (recAt d w lb ng CF b) (ng + 1) := congrArg Fin.val hab
      exact Fin.ext (hSinj a a.2 b b.2 (by rw [e]))
    have hsurj := Finite.surjective_of_injective hσ
    intro a ha b hb hE
    obtain ⟨ka, hka⟩ := hsurj ⟨a, ha⟩
    obtain ⟨kb, hkb⟩ := hsurj ⟨b, hb⟩
    have ea : fldOf d w (recAt d w lb ng CF ka) (ng + 1) = a := congrArg Fin.val hka
    have eb : fldOf d w (recAt d w lb ng CF kb) (ng + 1) = b := congrArg Fin.val hkb
    have hk : (ka : ℕ) = kb := hSinj ka ka.2 kb kb.2 (by rw [ea, eb]; exact hE)
    rw [← ea, ← eb, hk]
  · intro k hk j hj
    have e := edgesK_spec (recK_parts (h k hk)).1 hj
    exact ⟨_, e.1, e.2⟩
  · intro P hP1 hPG
    have hC : ∀ k ≤ N, ∀ t < (if k < N then fldOf d w (recAt d w lb ng CF k) ng else N),
        P (elemAt d w lb ng CF t) := by
      intro k
      induction k with
      | zero =>
        intro _ t ht
        rw [if_pos hN, hh'.2] at ht
        obtain rfl : t = 0 := by omega
        rw [hh'.1]
        exact hP1
      | succ k ih =>
        intro hk
        have ihk := ih (by omega)
        rw [if_pos (by omega : k < N)] at ihk
        obtain ⟨e1, e2, e3, _⟩ := recK_parts (h k (by omega))
        have hPk : P (elemAt d w lb ng CF k) := ihk k e2
        have hQ : ∀ j < ng, P (elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF k) j)) := by
          intro j hj
          rw [(edgesK_spec e1 hj).2]
          exact hPG _ j hj hPk
        rcases rowK_good (Q := fun t => P (elemAt d w lb ng CF t)) hQ ihk ng le_rfl with h0 | h0
        · exact absurd (e3.symm.trans h0) (Nat.ne_of_lt (nextM_lt hNw))
        · rw [e3] at h0
          by_cases hk1 : k + 1 < N
          · rw [if_pos hk1]
            rw [nextM_of_lt hk1] at h0
            exact h0
          · rw [if_neg hk1]
            rw [nextM_last hk1] at h0
            exact h0
    intro k hk
    have hN' := hC N le_rfl
    rw [if_neg (lt_irrefl N)] at hN'
    exact hN' k hk

end CFSG.KC.F2BfsRec

end
