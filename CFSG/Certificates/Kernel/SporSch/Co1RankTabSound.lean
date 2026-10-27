module

public import CFSG.Certificates.Kernel.SporSch.Co1RankAsmSound
public import CFSG.Certificates.Kernel.Co1Three.TermSound
public import Certificates.Data.Kernel.SporSch.Co1RankBnd
public import CFSG.Certificates.Kernel.SporSch.Co1RankRCSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankTab CFSG.KC.Co1B CFSG.KC.Co1Cl
  CFSG.KC.Co1RankBnd CFSG.Sporadic.Co1Schreier

section Words

variable {M : Type*} [Monoid M]

@[expose] def wordP (f : ℕ → M) : ℕ → ℕ → M
  | 0, _ => 1
  | n + 1, w => if w % 16 = 0 then 1 else f (w % 16 - 1) * wordP f n (w / 16)

theorem wordP_map {M' : Type*} [Monoid M'] (φ : M →* M') (f : ℕ → M) : ∀ n w,
    φ (wordP f n w) = wordP (fun g => φ (f g)) n w
  | 0, _ => map_one φ
  | n + 1, w => by
    rw [wordP, wordP]
    split
    · exact map_one φ
    · rw [map_mul, wordP_map φ f n]

theorem wordP_congr {f f' : ℕ → M} {nG : ℕ} (h : ∀ g < nG, f g = f' g) : ∀ n w,
    wordOKn nG n w = true → wordP f n w = wordP f' n w
  | 0, _, _ => rfl
  | n + 1, w, hw => by
    rw [wordOKn] at hw
    rw [wordP, wordP]
    split
    · rfl
    · rename_i h0
      rw [if_neg h0] at hw
      obtain ⟨hl, hw⟩ := Bool.and_eq_true_iff.1 hw
      have := of_decide_eq_true hl
      rw [h _ (by omega), wordP_congr h n _ hw]

end Words

theorem matK_walkM (G : List ℕ) : ∀ n w acc, matK (Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ a => a) (fun _ ih w a => strictN (Nat.land w 15) fun l =>
      nIf(Nat.beq l 0, a, strictN (mulWK a (getM G (Nat.sub l 1))) fun a' =>
        ih (Nat.shiftRight w 4) a')) n w acc) = matK acc * wordP (fun g => matK (getM G g)) n w
  | 0, _, acc => by simp [wordP]
  | n + 1, w, acc => by
    change matK (strictN (Nat.land w 15) _) = _
    rw [strictN_eq, land15, wordP]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw, hw, mul_one]
      rfl
    · rw [if_neg hw, beq_false hw]
      change matK (strictN _ _) = _
      rw [strictN_eq, matK_walkM G n, matK_mulWK, shr4, mul_assoc]
      rfl

theorem matK_walkM' (G : List ℕ) (w acc : ℕ) :
    matK (walkM G w acc) = matK acc * wordP (fun g => matK (getM G g)) 8 w :=
  matK_walkM G 8 w acc

theorem matK_qOf (D : Co1RankTab.Dat) (v : ℕ) : ∀ n, matK (Nat.rec (motive := fun _ => Nat) oneK
    (fun s acc => nIf(Nat.beq (Nat.land (Nat.shiftRight v s) 1) 1,
      strictN acc fun a => mulWK a (getM D.BS s), acc)) n) =
    qProd (fun s => matK (getM D.BS s)) n v
  | 0 => matK_oneK
  | n + 1 => by
    change matK (Bool.rec (motive := fun _ => Nat) _ _ (bitB v n)) = _
    rw [qProd]
    cases bitB v n
    · exact matK_qOf D v n
    · change matK (strictN _ _) = _
      rw [strictN_eq, matK_mulWK, matK_qOf D v n]
      rfl

theorem matK_qOf' (D : Co1RankTab.Dat) (v : ℕ) :
    matK (qOf D v) = qProd (fun s => matK (getM D.BS s)) D.d v := matK_qOf D v D.d

theorem phiR_single (row : ℕ → ℕ) (s : ℕ) : ∀ n, phiR row n (2 ^ s) = if s < n then row s else 0
  | 0 => by simp [phiR]
  | n + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (phiR row n (2 ^ s))
      (Nat.xor (phiR row n (2 ^ s)) (row n)) (bitB (2 ^ s) n) = _
    rw [bitB_eq, Nat.testBit_two_pow, phiR_single row s n]
    by_cases h : s = n
    · subst h
      simp
    · have h' : decide (s = n) = false := decide_eq_false h
      rw [h']
      by_cases hs : s < n
      · rw [if_pos hs, if_pos (by omega)]
      · rw [if_neg hs, if_neg (by omega)]

section Walk

variable {G : Type*} [Group G]

theorem relK_lt (D : Co1RankTab.Dat) (j g : ℕ) : relK D j g < 2 ^ (7 + D.d) := land_mask_lt _ _

theorem relK_shr_lt (D : Co1RankTab.Dat) (j g : ℕ) : Nat.shiftRight (relK D j g) 7 < 2 ^ D.d := by
  change relK D j g >>> 7 < 2 ^ D.d
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_of_lt_mul ?_
  rw [← pow_add]
  exact relK_lt D j g

theorem stepC_lo_lt (D : Co1RankTab.Dat) (x g : ℕ) :
    Nat.xor (Nat.land x (mask D.d)) (Nat.shiftRight (relK D (x >>> D.d) g) 7) < 2 ^ D.d :=
  Nat.xor_lt_two_pow (land_mask_lt _ _) (relK_shr_lt D _ g)

theorem stepC_eq (D : Co1RankTab.Dat) (x g : ℕ) : stepC D x g =
    Nat.land (relK D (x >>> D.d) g) 127 * 2 ^ D.d +
      Nat.xor (Nat.land x (mask D.d)) (Nat.shiftRight (relK D (x >>> D.d) g) 7) := by
  rw [stepC, strictN_eq]
  change (Nat.land (relK D (x >>> D.d) g) 127 <<< D.d) |||
    Nat.xor (Nat.land x (mask D.d)) (Nat.shiftRight (relK D (x >>> D.d) g) 7) = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (stepC_lo_lt D x g), Nat.shiftLeft_eq]

theorem land127_lt (r : ℕ) : Nat.land r 127 < 128 := by
  have := land_mask_lt r 7
  rw [mask_eq] at this
  exact this

theorem split_lt {d k lo : ℕ} (hk : k < 128) (hlo : lo < 2 ^ d) : k * 2 ^ d + lo < 2 ^ (d + 7) :=
  calc k * 2 ^ d + lo < k * 2 ^ d + 2 ^ d := Nat.add_lt_add_left hlo _
    _ = (k + 1) * 2 ^ d := (Nat.succ_mul _ _).symm
    _ ≤ 128 * 2 ^ d := Nat.mul_le_mul_right _ hk
    _ = 2 ^ (d + 7) := by rw [pow_add, Nat.mul_comm]; rfl

theorem el_stepC {D : Co1RankTab.Dat} {b w gg : ℕ → G}
    (hc : ∀ s < D.d, ∀ t < D.d, b s * b t = b t * b s) (hsq : ∀ s < D.d, b s * b s = 1)
    (hrel : ∀ j < 128, ∀ g < D.nG, w j * gg g =
      qProd b D.d (Nat.shiftRight (relK D j g) 7) * w (Nat.land (relK D j g) 127))
    {x g : ℕ} (hx : x < 2 ^ (D.d + 7)) (hg : g < D.nG) :
    stepC D x g < 2 ^ (D.d + 7) ∧ el D.d b w (stepC D x g) = el D.d b w x * gg g := by
  have hlo := stepC_lo_lt D x g
  rw [stepC_eq]
  refine ⟨split_lt (land127_lt _) hlo, ?_⟩
  rw [el_split _ _ _ _ _ hlo, qProd_xor' hc hsq, el, mul_assoc (qProd b D.d x),
    hrel _ (shiftRight_lt hx) g hg, ← mul_assoc, land_mask, qProd_mod]

theorem el_walkC {D : Co1RankTab.Dat} {b w gg : ℕ → G}
    (hc : ∀ s < D.d, ∀ t < D.d, b s * b t = b t * b s) (hsq : ∀ s < D.d, b s * b s = 1)
    (hrel : ∀ j < 128, ∀ g < D.nG, w j * gg g =
      qProd b D.d (Nat.shiftRight (relK D j g) 7) * w (Nat.land (relK D j g) 127)) :
    ∀ n wd x, x < 2 ^ (D.d + 7) → wordOKn D.nG n wd = true →
      Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
        (fun _ ih w x => strictN (Nat.land w 15) fun l =>
          nIf(Nat.beq l 0, x, strictN (stepC D x (Nat.sub l 1)) fun x' =>
            ih (Nat.shiftRight w 4) x')) n wd x < 2 ^ (D.d + 7) ∧
      el D.d b w (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
        (fun _ ih w x => strictN (Nat.land w 15) fun l =>
          nIf(Nat.beq l 0, x, strictN (stepC D x (Nat.sub l 1)) fun x' =>
            ih (Nat.shiftRight w 4) x')) n wd x) = el D.d b w x * wordP gg n wd
  | 0, _, x, hx, _ => ⟨hx, by simp [wordP]⟩
  | n + 1, wd, x, hx, hw => by
    rw [wordOKn] at hw
    change strictN (Nat.land wd 15) _ < _ ∧ el D.d b w (strictN (Nat.land wd 15) _) = _
    rw [strictN_eq, land15, wordP]
    by_cases h0 : wd % 16 = 0
    · rw [if_pos h0, h0, mul_one]
      exact ⟨hx, rfl⟩
    · rw [if_neg h0] at hw ⊢
      rw [beq_false h0]
      obtain ⟨hl, hw⟩ := Bool.and_eq_true_iff.1 hw
      have := of_decide_eq_true hl
      obtain ⟨h1, h2⟩ := el_stepC hc hsq hrel (g := wd % 16 - 1) hx (by omega)
      change strictN (stepC D x (wd % 16 - 1)) _ < _ ∧
        el D.d b w (strictN (stepC D x (wd % 16 - 1)) _) = _
      rw [strictN_eq, shr4]
      obtain ⟨h3, h4⟩ := el_walkC hc hsq hrel n (wd / 16) _ h1 hw
      refine ⟨h3, ?_⟩
      rw [h4]
      change el D.d b w (stepC D x (wd % 16 - 1)) * _ = _
      rw [h2, mul_assoc]

theorem cocycle_of_walks {D : Co1RankTab.Dat} {b w gg : ℕ → G}
    (hc : ∀ s < D.d, ∀ t < D.d, b s * b t = b t * b s) (hsq : ∀ s < D.d, b s * b s = 1)
    (hrel : ∀ j < 128, ∀ g < D.nG, w j * gg g =
      qProd b D.d (Nat.shiftRight (relK D j g) 7) * w (Nat.land (relK D j g) 127))
    (hw : ∀ j < 128, w j = wordP gg 8 (getL D.CW j))
    (hword : ∀ j < 128, wordOKn D.nG 8 (getL D.CW j) = true)
    (hwalk : ∀ i < 128, ∀ j < 128, walkC D (getL D.CW j) (Nat.shiftLeft i D.d) =
      Nat.lor (Nat.shiftLeft (kt D.Kt i j) D.d) (nc D.d D.NCt i j))
    {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    w i * w j = qProd b D.d (nc D.d D.NCt i j) * w (kt D.Kt i j) := by
  have hx0 : Nat.shiftLeft i D.d < 2 ^ (D.d + 7) := by
    have := split_lt (d := D.d) (lo := 0) hi (Nat.two_pow_pos _)
    rw [Nat.add_zero] at this
    change i <<< D.d < _
    rw [Nat.shiftLeft_eq]
    exact this
  have e1 := (el_walkC hc hsq hrel 8 (getL D.CW j) (Nat.shiftLeft i D.d) hx0 (hword j hj)).2
  change el D.d b w (walkC D (getL D.CW j) (Nat.shiftLeft i D.d)) = _ at e1
  rw [hwalk i hi j hj, ← hw j hj] at e1
  have hlo := nc_lt D.d D.NCt i j
  have e2 : Nat.lor (Nat.shiftLeft (kt D.Kt i j) D.d) (nc D.d D.NCt i j) =
      kt D.Kt i j * 2 ^ D.d + nc D.d D.NCt i j := by
    change (_ <<< D.d) ||| _ = _
    rw [← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
  have e3 : el D.d b w (Nat.shiftLeft i D.d) = w i := by
    have := el_split D.d b w i 0 (Nat.two_pow_pos _)
    rw [Nat.add_zero, qProd_zero, one_mul] at this
    change el D.d b w (i <<< D.d) = _
    rw [Nat.shiftLeft_eq]
    exact this
  rw [e2, el_split _ _ _ _ _ hlo, e3] at e1
  exact e1.symm

end Walk

theorem bAnd_rk {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem recAnd_rk {f : ℕ → Bool → Bool} {p : ℕ → Prop} :
    ∀ {m}, Nat.rec (motive := fun _ => Bool) true f m = true →
      (∀ k b, f k b = true → p k ∧ b = true) → ∀ k < m, p k
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, h, hf, k, hk => by
    obtain ⟨h1, h2⟩ := hf m _ h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recAnd_rk h2 hf k hk
    · exact h1

theorem allBelow_rk {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  have inner : ∀ (hh : ℕ) (n : ℕ), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n hn l hl hlm
    have e := recAnd_rk (p := fun l => (fun i => bIf(Nat.blt i m, f i, true))
      (Nat.add (Nat.shiftLeft hh 6) l) = true) hn (fun _ _ hb => bAnd_rk hb) l hl
    beta_reduce at e
    have hb : Nat.blt (Nat.add (Nat.shiftLeft hh 6) l) m = true := Nat.blt_eq.mpr hlm
    rw [hb] at e
    exact e
  intro i him
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have h1 := recAnd_rk (p := fun hh => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64 = true)
    h (fun _ _ hb => bAnd_rk hb) (i / 64) (by omega)
  have := inner _ 64 h1 (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem chkM_sound {D : Co1RankTab.Dat} (h : chkM D = true) :
    (∀ s < D.d, ∀ t < D.d, mulWK (getM D.BS s) (getM D.BS t) = mulWK (getM D.BS t) (getM D.BS s)) ∧
    (∀ s < D.d, mulWK (getM D.BS s) (getM D.BS s) = oneK) ∧
    indepOK D.BS = true ∧
    (∀ i < 128, getM D.WL i = walkM D.G (getL D.CW i) oneK) ∧
    (∀ j < 128, ∀ g < D.nG, mulWK (getM D.WL j) (getM D.G g) =
      mulWK (qOf D (Nat.shiftRight (relK D j g) 7)) (getM D.WL (Nat.land (relK D j g) 127))) ∧
    (∀ j < 128, ∀ s < D.d, mulWK (getM D.WL j) (getM D.BS s) =
      mulWK (qOf D (phi D.d D.PHt j (Nat.shiftLeft 1 s))) (getM D.WL j)) ∧
    eltM D (fld(D.UC, 0, mask (Nat.add D.d 7))) = D.cM ∧
    (∀ j < 128, ∀ v < 2 ^ D.d,
      fld(getL (Co1RankCand.getLL D.T2A (Nat.shiftRight j 3)) (Nat.land j 7), v, 1) = 1 →
      rankRC 24 24 (Nat.xor (eltM D (Nat.lor (Nat.shiftLeft j D.d) v)) oneK) = 8) := by
  unfold chkM at h
  generalize hN : (128 : ℕ) = N at h
  obtain ⟨h1, h⟩ := bAnd_rk h
  obtain ⟨h2, h⟩ := bAnd_rk h
  obtain ⟨h3, h⟩ := bAnd_rk h
  obtain ⟨h4, h⟩ := bAnd_rk h
  obtain ⟨h5, h6⟩ := bAnd_rk h
  have hL1 := recAnd_rk (p := fun s => (∀ t < D.d, mulWK (getM D.BS s) (getM D.BS t) =
      mulWK (getM D.BS t) (getM D.BS s)) ∧ mulWK (getM D.BS s) (getM D.BS s) = oneK) h1
    (fun s b hb => by
      obtain ⟨a1, a2⟩ := bAnd_rk hb
      obtain ⟨a3, a4⟩ := bAnd_rk a2
      refine ⟨⟨recAnd_rk (p := fun t => mulWK (getM D.BS s) (getM D.BS t) =
          mulWK (getM D.BS t) (getM D.BS s)) a1 (fun t b' hb' => by
            beta_reduce at hb'
            rw [strictB_eq', strictB_eq'] at hb'
            obtain ⟨c1, c2⟩ := bAnd_rk hb'
            exact ⟨Nat.eq_of_beq_eq_true c1, c2⟩), Nat.eq_of_beq_eq_true a3⟩, a4⟩)
  have hL2 := recAnd_rk (p := fun i => getM D.WL i = walkM D.G (getL D.CW i) oneK) h3
    (fun i b hb => by
      obtain ⟨c1, c2⟩ := bAnd_rk hb
      exact ⟨Nat.eq_of_beq_eq_true c1, c2⟩)
  have hL3 := recAnd_rk (p := fun j => (∀ g < D.nG, mulWK (getM D.WL j) (getM D.G g) =
      mulWK (qOf D (Nat.shiftRight (relK D j g) 7)) (getM D.WL (Nat.land (relK D j g) 127))) ∧
      (∀ s < D.d, mulWK (getM D.WL j) (getM D.BS s) =
        mulWK (qOf D (phi D.d D.PHt j (Nat.shiftLeft 1 s))) (getM D.WL j))) h4
    (fun j b hb => by
      beta_reduce at hb
      rw [strictB_eq'] at hb
      obtain ⟨a1, a2⟩ := bAnd_rk hb
      obtain ⟨a3, a4⟩ := bAnd_rk a2
      refine ⟨⟨recAnd_rk (p := fun g => mulWK (getM D.WL j) (getM D.G g) =
          mulWK (qOf D (Nat.shiftRight (relK D j g) 7)) (getM D.WL (Nat.land (relK D j g) 127)))
          a1 (fun g b' hb' => by
            beta_reduce at hb'
            rw [strictB_eq'] at hb'
            obtain ⟨c1, c2⟩ := bAnd_rk hb'
            exact ⟨Nat.eq_of_beq_eq_true c1, c2⟩),
        recAnd_rk (p := fun s => mulWK (getM D.WL j) (getM D.BS s) =
          mulWK (qOf D (phi D.d D.PHt j (Nat.shiftLeft 1 s))) (getM D.WL j))
          a3 (fun s b' hb' => by
            obtain ⟨c1, c2⟩ := bAnd_rk hb'
            exact ⟨Nat.eq_of_beq_eq_true c1, c2⟩)⟩, a4⟩)
  have hm : Nat.shiftLeft 1 D.d ≤ 64 * Nat.shiftLeft 1 (Nat.sub D.d 6) := by
    change 1 <<< D.d ≤ 64 * (1 <<< (D.d - 6))
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
    have e : 2 ^ D.d ≤ 2 ^ (6 + (D.d - 6)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at e
    simpa using e
  have hL4 := recAnd_rk (p := fun j => ∀ v < 2 ^ D.d,
      fld(getL (Co1RankCand.getLL D.T2A (Nat.shiftRight j 3)) (Nat.land j 7), v, 1) = 1 →
      rankRC 24 24 (Nat.xor (eltM D (Nat.lor (Nat.shiftLeft j D.d) v)) oneK) = 8) h6
    (fun j b hb => by
      beta_reduce at hb
      rw [strictB_eq'] at hb
      obtain ⟨a1, a2⟩ := bAnd_rk hb
      refine ⟨fun v hv hbit => ?_, a2⟩
      have hv' : v < Nat.shiftLeft 1 D.d := by
        change v < 1 <<< D.d
        rw [Nat.one_shiftLeft]
        exact hv
      have e := allBelow_rk a1 hm v hv'
      beta_reduce at e
      have hb1 : Nat.beq (fld(getL (Co1RankCand.getLL D.T2A (Nat.shiftRight j 3)) (Nat.land j 7),
          v, 1)) 1 = true := by
        rw [Nat.beq_eq]
        exact hbit
      rw [hb1] at e
      exact Nat.eq_of_beq_eq_true e)
  subst hN
  exact ⟨fun s hs => (hL1 s hs).1, fun s hs => (hL1 s hs).2, h2, hL2,
    fun j hj => (hL3 j hj).1, fun j hj => (hL3 j hj).2, Nat.eq_of_beq_eq_true h5, hL4⟩

theorem chkT_sound {D : Co1RankTab.Dat} (h : chkT D = true) :
    getL D.CW 0 = 0 ∧
    (∀ i < 128, ∀ j < 128, walkC D (getL D.CW j) (Nat.shiftLeft i D.d) =
      Nat.lor (Nat.shiftLeft (kt D.Kt i j) D.d) (nc D.d D.NCt i j)) ∧
    (∀ i < 128, ∀ j < 128, i < j → phRow D i ≠ phRow D j) := by
  unfold chkT at h
  obtain ⟨h0, h⟩ := bAnd_rk h
  obtain ⟨h1, h2⟩ := bAnd_rk h
  have hij : ∀ i < 128, ∀ j < 128, 128 * i + j < 16384 ∧
      Nat.shiftRight (128 * i + j) 7 = i ∧ Nat.land (128 * i + j) 127 = j := by
    intro i hi j hj
    have e1 : Nat.land (128 * i + j) 127 = (128 * i + j) % 128 :=
      Nat.and_two_pow_sub_one_eq_mod _ 7
    refine ⟨by omega, ?_, by rw [e1]; omega⟩
    change (128 * i + j) >>> 7 = i
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi j hj => ?_, fun i hi j hj hlt hr => ?_⟩
  · obtain ⟨hp, e1, e2⟩ := hij i hi j hj
    have e := allBelow_rk h1 (by norm_num) _ hp
    beta_reduce at e
    rw [strictB_eq', strictB_eq', e1, e2] at e
    exact Nat.eq_of_beq_eq_true e
  · obtain ⟨hp, e1, e2⟩ := hij i hi j hj
    have e := allBelow_rk h2 (by norm_num) _ hp
    beta_reduce at e
    have hb : Nat.blt i j = true := Nat.blt_eq.mpr hlt
    rw [strictB_eq', strictB_eq', e1, e2, hr, Nat.beq_refl, hb] at e
    exact absurd e Bool.false_ne_true

@[expose] def vecRk (d x : ℕ) : Fin d → ZMod 2 := fun j => if x.testBit j then 1 else 0

theorem vecRk_xor (d x y : ℕ) : vecRk d (Nat.xor x y) = vecRk d x + vecRk d y := by
  funext j
  simp only [vecRk, Pi.add_apply]
  have e : (Nat.xor x y).testBit j = (x.testBit j ^^ y.testBit j) := Nat.testBit_xor x y j
  rw [e]
  cases x.testBit j <;> cases y.testBit j <;> decide

theorem vecRk_inj {d x y : ℕ} (hx : x < 2 ^ d) (hy : y < 2 ^ d) (h : vecRk d x = vecRk d y) :
    x = y := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    simp only [vecRk] at this
    cases hx' : x.testBit j <;> cases hy' : y.testBit j <;> rw [hx', hy'] at this <;>
      first | rfl | exact absurd this (by decide)
  · have hd : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hd), Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hd)]

theorem foldr_xor_append (g : ℕ × ℕ → ℕ) (L1 L2 : List (ℕ × ℕ)) :
    (L1 ++ L2).foldr (fun p acc => Nat.xor (g p) acc) 0 =
      Nat.xor (L1.foldr (fun p acc => Nat.xor (g p) acc) 0)
        (L2.foldr (fun p acc => Nat.xor (g p) acc) 0) := by
  induction L1 with
  | nil => exact (Nat.zero_xor _).symm
  | cons a L ih =>
    rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih]
    exact (Nat.xor_assoc _ _ _).symm

@[expose] noncomputable def nK (D : Co1RankTab.Dat) (k : ℕ) : ℕ :=
  Nat.shiftRight (fld(D.REL, Nat.mul (Nat.add 7 D.d) k, mask (Nat.add 7 D.d))) 7

theorem nK_lt (D : Co1RankTab.Dat) (k : ℕ) : nK D k < 2 ^ D.d := by
  have hm : mask (Nat.add 7 D.d) < 2 ^ (7 + D.d) := by
    rw [Co1RankRC.mask_eq]
    exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
  have hf := Nat.and_lt_two_pow (Nat.shiftRight D.REL (Nat.mul (Nat.add 7 D.d) k)) hm
  change Nat.land _ _ >>> 7 < _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 7), ← pow_add, add_comm]
  exact hf

theorem foldr_lt (D : Co1RankTab.Dat) : ∀ L : List (ℕ × ℕ),
    L.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0 < 2 ^ D.d
  | [] => Nat.two_pow_pos _
  | p :: L => Nat.xor_lt_two_pow (nK_lt D _) (foldr_lt D L)

theorem relN_bit (D : Co1RankTab.Dat) (t j : ℕ) (hj : j < D.d) : ∀ m,
    (relN D m).testBit (D.d * t + j) = (decide (t < m) && (nK D t).testBit j)
  | 0 => by
    change (0 : ℕ).testBit _ = _
    simp
  | m + 1 => by
    change ((relN D m) ||| (nK D m <<< (D.d * m))).testBit (D.d * t + j) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, relN_bit D t j hj m]
    rcases lt_trichotomy t m with h | rfl | h
    · have h1 : D.d * (t + 1) ≤ D.d * m := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h1
      simp [h, show t < m + 1 by omega, show ¬ (D.d * t + j ≥ D.d * m) by omega]
    · simp
    · have h1 : D.d * (m + 1) ≤ D.d * t := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h1
      have hb : (nK D m).testBit (D.d * t + j - D.d * m) = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (nK_lt D m) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hb, show ¬ t < m by omega, show ¬ t < m + 1 by omega]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem span_of_rk {D : Co1RankTab.Dat}
    (h : Co1RankRC.rk (Nat.mul 128 D.nG) D.d (relN D (Nat.mul 128 D.nG)) = D.d) :
    ∀ v < 2 ^ D.d, ∃ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 < 128 ∧ p.2 < D.nG) ∧
      v = L.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0 := by
  intro v hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrow : ∀ t : Fin (Nat.mul 128 D.nG),
      Co1RankRC.rowV D.d (relN D (Nat.mul 128 D.nG)) t = vecRk D.d (nK D t) := by
    intro t
    funext j
    simp only [Co1RankRC.rowV, vecRk]
    rw [relN_bit D t j j.2, decide_eq_true t.2, Bool.true_and]
  have htop : Submodule.span (ZMod 2) (Set.range fun t : Fin (Nat.mul 128 D.nG) =>
      Co1RankRC.rowV D.d (relN D (Nat.mul 128 D.nG)) t) = ⊤ := Co1RankRC.span_eq_top_of_rk h
  have key : ∀ x ∈ Submodule.span (ZMod 2) (Set.range fun t : Fin (Nat.mul 128 D.nG) =>
      Co1RankRC.rowV D.d (relN D (Nat.mul 128 D.nG)) t), ∃ L : List (ℕ × ℕ),
        (∀ p ∈ L, p.1 < 128 ∧ p.2 < D.nG) ∧
        x = vecRk D.d (L.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      have ht : t.1 < 128 * D.nG := t.2
      have hnG : 0 < D.nG := by
        rcases Nat.eq_zero_or_pos D.nG with h0 | h0
        · have : 128 * D.nG = 0 := by rw [h0]
          omega
        · exact h0
      refine ⟨[(t / D.nG, t % D.nG)], ?_, ?_⟩
      · intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        exact ⟨(Nat.div_lt_iff_lt_mul hnG).2 ht, Nat.mod_lt _ hnG⟩
      · dsimp only
        rw [hrow t, List.foldr_cons, List.foldr_nil]
        congr 1
        have e : Nat.add (Nat.mul D.nG (t / D.nG)) (t % D.nG) = t := Nat.div_add_mod t D.nG
        unfold relK nK
        dsimp only
        rw [e]
        exact (Nat.xor_zero _).symm
    | zero =>
      refine ⟨[], by simp, ?_⟩
      funext j
      simp [vecRk]
    | add x y _ _ hx hy =>
      obtain ⟨L1, h1, rfl⟩ := hx
      obtain ⟨L2, h2, rfl⟩ := hy
      exact ⟨L1 ++ L2, fun p hp => (List.mem_append.1 hp).elim (h1 p) (h2 p),
        by rw [foldr_xor_append, vecRk_xor]⟩
    | smul c x _ hx =>
      obtain ⟨L, hL, rfl⟩ := hx
      rcases zmod2_cases c with rfl | rfl
      · refine ⟨[], by simp, ?_⟩
        rw [zero_smul]
        funext j
        simp [vecRk]
      · exact ⟨L, hL, by rw [one_smul]⟩
  obtain ⟨L, hL, hv'⟩ := key _ (htop ▸ Submodule.mem_top)
  exact ⟨L, hL, vecRk_inj hv (foldr_lt D L) hv'⟩

theorem tabOK_sound {D : Co1RankTab.Dat} (h : tabOK D = true) :
    (∀ i < 128, wordOKn D.nG 8 (getL D.CW i) = true) ∧
    ∀ v < 2 ^ D.d, ∃ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 < 128 ∧ p.2 < D.nG) ∧
      v = L.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0 := by
  unfold tabOK at h
  obtain ⟨h1, h2⟩ := bAnd_rk h
  refine ⟨?_, ?_⟩
  · generalize hN : (128 : ℕ) = N at h1
    have := recAnd_rk (p := fun i => wordOKn D.nG 8 (getL D.CW i) = true) h1 (fun i b hb => by
      obtain ⟨c1, c2⟩ := bAnd_rk hb
      exact ⟨by rw [← wordOK_eq]; exact c1, c2⟩)
    subst hN
    exact this
  rw [strictB_eq'] at h2
  have hrk := Nat.eq_of_beq_eq_true h2
  rw [Co1RankRC.rankRC_eq] at hrk
  exact span_of_rk hrk

@[expose] noncomputable def bU (D : Co1RankTab.Dat) (s : ℕ) : GL24 :=
  if h : matK (getM D.BS s) * matK (getM D.BS s) = 1 then ⟨_, _, h, h⟩ else 1

theorem val_bU {D : Co1RankTab.Dat} {s : ℕ} (h : matK (getM D.BS s) * matK (getM D.BS s) = 1) :
    (bU D s : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matK (getM D.BS s) := by
  rw [bU, dif_pos h]

@[expose] noncomputable def wU (D : Co1RankTab.Dat) (gens : ℕ → GL24) (i : ℕ) : GL24 := wordP gens 8 (getL D.CW i)

theorem model_of_checks {D : Co1RankTab.Dat} {gens : ℕ → GL24} (hM : chkM D = true)
    (hT : chkT D = true) (htab : tabOK D = true)
    (hG : ∀ g < D.nG, matK (getM D.G g) = (gens g : Matrix (Fin 24) (Fin 24) (ZMod 2))) :
    Model (toC D) (bU D) (wU D gens) ∧ wU D gens 0 = 1 ∧
      ∀ j < 128, ∀ g < D.nG, wU D gens j * gens g =
        qProd (bU D) D.d (Nat.shiftRight (relK D j g) 7) * wU D gens (Nat.land (relK D j g) 127) := by
  obtain ⟨hcm, hsq, -, hWL, hrel, hrow, -, -⟩ := chkM_sound hM
  obtain ⟨hCW0, hwalk, -⟩ := chkT_sound hT
  obtain ⟨hword, -⟩ := tabOK_sound htab
  have hsqM : ∀ s < D.d, matK (getM D.BS s) * matK (getM D.BS s) = 1 := fun s hs => by
    rw [← matK_mulWK, hsq s hs, matK_oneK]
  have hb : ∀ s < D.d, ((bU D s : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      matK (getM D.BS s) := fun s hs => val_bU (hsqM s hs)
  have hq : ∀ v, ((qProd (bU D) D.d v : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      matK (qOf D v) := fun v => by
    have e := qProd_map (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) (bU D) D.d v
    simp only [Units.coeHom_apply] at e
    rw [e, matK_qOf']
    exact qProd_congr_fun _ hb v
  have hw : ∀ i < 128, ((wU D gens i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      matK (getM D.WL i) := fun i hi => by
    have e := wordP_map (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) gens 8 (getL D.CW i)
    simp only [Units.coeHom_apply] at e
    rw [hWL i hi, matK_walkM', matK_oneK, one_mul, wU, e]
    exact wordP_congr (fun g hg => (hG g hg).symm) 8 _ (hword i hi)
  have hcomm : ∀ s < D.d, ∀ t < D.d, bU D s * bU D t = bU D t * bU D s := fun s hs t ht =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hb s hs, hb t ht, ← matK_mulWK, ← matK_mulWK,
        hcm s hs t ht])
  have hsq' : ∀ s < D.d, bU D s * bU D s = 1 := fun s hs => Units.ext (by
    rw [Units.val_mul, Units.val_one, hb s hs, hsqM s hs])
  have hrel' : ∀ j < 128, ∀ g < D.nG, wU D gens j * gens g =
      qProd (bU D) D.d (Nat.shiftRight (relK D j g) 7) * wU D gens (Nat.land (relK D j g) 127) :=
    fun j hj g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul, hw j hj, hq, hw _ (land127_lt _), ← hG g hg,
        ← matK_mulWK, ← matK_mulWK, hrel j hj g hg])
  have hw0 : wU D gens 0 = 1 := by
    rw [wU, hCW0]
    rfl
  refine ⟨⟨hcomm, hsq', fun i hi s hs => ?_, fun i hi j hj => ?_⟩, hw0, hrel'⟩
  ·
    have e : wU D gens i * bU D s = qProd (bU D) D.d (phi D.d D.PHt i (Nat.shiftLeft 1 s)) *
        wU D gens i := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hw i hi, hb s hs, hq, ← matK_mulWK, ← matK_mulWK,
        hrow i hi s hs])
    have hph : phi D.d D.PHt i (Nat.shiftLeft 1 s) =
        fld(D.PHt, Nat.mul D.d (Nat.add (Nat.mul D.d i) s), mask D.d) := by
      rw [phi_eq]
      change phiR _ D.d (1 <<< s) = _
      have hs' : s < D.d := hs
      rw [Nat.shiftLeft_eq, one_mul, phiR_single, if_pos hs']
    change wU D gens i * bU D s * (wU D gens i)⁻¹ = qProd (bU D) D.d
      (fld(D.PHt, Nat.mul D.d (Nat.add (Nat.mul D.d i) s), mask D.d))
    rw [e, ← hph]
    group
  · have hc1 := @cocycle_of_walks GL24 _ D (bU D) (wU D gens) gens hcomm
    have hc2 := hc1 hsq'
    have hc3 := hc2 hrel'
    have hc4 := hc3 (fun j _ => rfl)
    have hc5 := hc4 hword
    have hc6 := hc5 hwalk (i := i) (j := j) hi hj
    exact hc6

end CFSG.KS.SporSch.Co1Rank

end
