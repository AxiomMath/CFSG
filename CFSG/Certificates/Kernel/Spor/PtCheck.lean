module

public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.PtC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def rd (w p j : Nat) : Nat :=
  strictN (Nat.shiftRight j (nat_lit 4)) (fun c =>
    Nat.land (Nat.shiftRight
      (Nat.land (Nat.shiftRight p (Nat.mul (Nat.mul w (nat_lit 16)) c))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w (nat_lit 16))) (nat_lit 1)))
      (Nat.mul w (Nat.land j (nat_lit 15)))) (mask w))

theorem rd_eq (w p j : Nat) : rd w p j = pg w (mask w) p j := by
  unfold rd
  rw [PF.strictN_eqP]
  have e1 : ∀ a b, Nat.land a b = a &&& b := fun _ _ => rfl
  have e2 : ∀ a b, Nat.shiftRight a b = a >>> b := fun _ _ => rfl
  have e3 : ∀ a b, Nat.mul a b = a * b := fun _ _ => rfl
  have e4 : ∀ a b, Nat.sub a b = a - b := fun _ _ => rfl
  have e5 : ∀ a b, Nat.shiftLeft a b = a <<< b := fun _ _ => rfl
  have hq : j >>> 4 = j / 16 := Nat.shiftRight_eq_div_pow j 4
  have hr : j &&& 15 = j % 16 := Nat.and_two_pow_sub_one_eq_mod j 4
  apply Nat.eq_of_testBit_eq
  intro k
  rw [PF.testBit_pgM]
  simp only [e1, e2, e3, e4, e5, hq, hr, PF.mask_eq, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < w
  · have hj : w * j = w * 16 * (j / 16) + w * (j % 16) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
    have hr' : w * (j % 16) ≤ w * 15 :=
      Nat.mul_le_mul_left w (Nat.le_of_lt_succ (Nat.mod_lt j (by decide)))
    have h1 : w * 16 * (j / 16) + (w * (j % 16) + k) = w * j + k := by omega
    have h2 : w * (j % 16) + k < w * 16 := by omega
    simp [h1, h2, hk]
  · simp [hk]

@[expose] noncomputable def cutT (rb H p : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun k => Nat.land (Nat.shiftRight p (Nat.mul k (Nat.shiftLeft rb H)))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft rb H)) (nat_lit 1)))
    (fun t ih k => strictN (Nat.shiftRight k (nat_lit 1)) fun k' => strictN (ih k') fun q =>
      Nat.land (Nat.shiftRight q (Nat.mul (Nat.land k (nat_lit 1)) (Nat.shiftLeft rb (Nat.sub (Nat.sub H t) (nat_lit 1)))))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft rb (Nat.sub (Nat.sub H t) (nat_lit 1)))) (nat_lit 1)))

theorem cutT_succ (rb H p t k : Nat) : cutT rb H p (t + 1) k =
    strictN (Nat.shiftRight k (nat_lit 1)) fun k' => strictN (cutT rb H p t k') fun q =>
      Nat.land (Nat.shiftRight q (Nat.mul (Nat.land k (nat_lit 1)) (Nat.shiftLeft rb (Nat.sub (Nat.sub H t) (nat_lit 1)))))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft rb (Nat.sub (Nat.sub H t) (nat_lit 1)))) (nat_lit 1)) := rfl

theorem cutT_spec (rb H p : Nat) : ∀ t, t ≤ H → ∀ k,
    cutT rb H p t k = (p >>> (k * (rb * 2 ^ (H - t)))) &&& (2 ^ (rb * 2 ^ (H - t)) - 1)
  | 0, _, k => by
    show Nat.land _ _ = _
    simp only [Nat.sub_zero]
    rw [show Nat.shiftLeft rb H = rb * 2 ^ H from Nat.shiftLeft_eq rb H,
      show Nat.shiftLeft 1 (rb * 2 ^ H) = 2 ^ (rb * 2 ^ H) from
        (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _)]
    rfl
  | t + 1, ht, k => by
    rw [cutT_succ, PF.strictN_eqP, PF.strictN_eqP, show Nat.shiftRight k 1 = k >>> 1 from rfl,
      cutT_spec rb H p t (by omega) (k >>> 1)]
    have hS : Nat.shiftLeft rb (Nat.sub (Nat.sub H t) 1) = rb * 2 ^ (H - (t + 1)) := by
      refine (Nat.shiftLeft_eq rb _).trans ?_
      show rb * 2 ^ (H - t - 1) = rb * 2 ^ (H - (t + 1))
      rw [Nat.sub_sub]
    rw [hS]
    show (((p >>> ((k >>> 1) * (rb * 2 ^ (H - t)))) &&& (2 ^ (rb * 2 ^ (H - t)) - 1)) >>>
        ((k &&& 1) * (rb * 2 ^ (H - (t + 1))))) &&& (Nat.shiftLeft 1 (rb * 2 ^ (H - (t + 1))) - 1) = _
    rw [show Nat.shiftLeft 1 (rb * 2 ^ (H - (t + 1))) = 2 ^ (rb * 2 ^ (H - (t + 1))) from
      (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _)]
    have hH : H - t = (H - (t + 1)) + 1 := by omega
    have hk : k >>> 1 = k / 2 := Nat.shiftRight_eq_div_pow k 1
    have hb : k &&& 1 = k % 2 := Nat.and_two_pow_sub_one_eq_mod k 1
    rw [hk, hb, hH]
    generalize H - (t + 1) = e
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < rb * 2 ^ e
    · have hm : k % 2 < 2 := Nat.mod_lt k (by decide)
      have h2 : rb * 2 ^ (e + 1) = 2 * (rb * 2 ^ e) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (rb * 2 ^ e) 2]
      have h3 : (k % 2) * (rb * 2 ^ e) + i < rb * 2 ^ (e + 1) := by
        rw [h2]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
        · have : k % 2 = 0 := by omega
          rw [this]; omega
        · have : k % 2 = 1 := by omega
          rw [this]; omega
      have h4 : k / 2 * (rb * 2 ^ (e + 1)) + ((k % 2) * (rb * 2 ^ e) + i) = k * (rb * 2 ^ e) + i := by
        rw [h2]
        have hk2 : k * (rb * 2 ^ e) = k / 2 * (2 * (rb * 2 ^ e)) + k % 2 * (rb * 2 ^ e) :=
          calc k * (rb * 2 ^ e) = (2 * (k / 2) + k % 2) * (rb * 2 ^ e) := by rw [Nat.div_add_mod k 2]
            _ = k / 2 * (2 * (rb * 2 ^ e)) + k % 2 * (rb * 2 ^ e) := by
              rw [Nat.add_mul, Nat.mul_comm 2 (k / 2), Nat.mul_assoc]
        rw [hk2, Nat.add_assoc]
      simp [hi, h3, h4]
    · simp [hi]

@[expose] noncomputable def rdT (w H p j : Nat) : Nat :=
  strictN (Nat.shiftRight j (nat_lit 4)) (fun c =>
    Nat.land (Nat.shiftRight (cutT (Nat.mul w (nat_lit 16)) H p H c) (Nat.mul w (Nat.land j (nat_lit 15))))
      (mask w))

theorem rdT_eq (w H p j : Nat) : rdT w H p j = pg w (mask w) p j := by
  rw [← rd_eq]
  unfold rdT rd
  rw [PF.strictN_eqP, PF.strictN_eqP, cutT_spec _ H p H (Nat.le_refl _), Nat.sub_self, Nat.pow_zero,
    Nat.mul_one]
  show (((p >>> (j >>> 4 * (w * 16))) &&& (2 ^ (w * 16) - 1)) >>> (w * (j &&& 15))) &&& mask w =
    (((p >>> (w * 16 * (j >>> 4))) &&& (Nat.shiftLeft 1 (w * 16) - 1)) >>> (w * (j &&& 15))) &&& mask w
  rw [show Nat.shiftLeft 1 (w * 16) = 2 ^ (w * 16) from (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _),
    Nat.mul_comm (j >>> 4)]

@[expose] noncomputable def letK (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def wimg (w : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun z _ ih i => strictN (ih i) (fun t => strictN (icode z) (fun c => rd w (letK S SI c) t)))
    wd

theorem wordK_cons (n w m idn : Nat) (S SI : Nat → Nat) (z : Int) (wd : List Int) :
    wordK n w m idn S SI (z :: wd) = pcomp n w m (letK S SI (icode z)) (wordK n w m idn S SI wd) := by
  unfold wordK
  simp only [PF.strictN_eqP]
  rfl

theorem wimg_cons (w : Nat) (S SI : Nat → Nat) (z : Int) (wd : List Int) (i : Nat) :
    wimg w S SI (z :: wd) i = rd w (letK S SI (icode z)) (wimg w S SI wd i) := by
  unfold wimg
  simp only [PF.strictN_eqP]

variable {n w : Nat}

theorem n32 (hn : n < 16777216) : n < 2 ^ 32 := Nat.lt_trans hn (by decide)

theorem wordK_shr (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (S SI : Nat → Nat) :
    ∀ wd : List Int, wordK n w (mask w) (pidn n w) S SI wd >>> (n * w) = 0
  | [] => PF.pidn_shr hn hw
  | z :: wd => by
    rw [wordK_cons]
    exact PF.pcomp_shr _ _ (n32 hn) (PF.w_pos hw)

theorem pg_wordK (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (S SI : Nat → Nat) :
    ∀ (wd : List Int) (i : Nat), i < n →
      pg w (mask w) (wordK n w (mask w) (pidn n w) S SI wd) i = wimg w S SI wd i
  | [], i, hi => PF.pg_pidn hn hw hi
  | z :: wd, i, hi => by
    rw [wordK_cons, PF.pg_pcomp (n32 hn) hi, pg_wordK hn hw S SI wd i hi, wimg_cons, rd_eq]

theorem beq_of_fields {p q : Nat} (hw : 0 < w) (hp : p >>> (n * w) = 0) :
    Nat.beq p q = (Nat.beq (Nat.shiftRight q (Nat.mul n w)) 0 &&
      allN n (fun i => Nat.beq (pg w (mask w) p i) (pg w (mask w) q i))) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Nat.beq_eq, Raw.Orb.allN_iff]
  constructor
  · intro e
    subst e
    refine ⟨?_, fun i _ => Nat.beq_refl _⟩
    show Nat.beq (p >>> (n * w)) 0 = true
    rw [hp]
    rfl
  · intro ⟨h1, h2⟩
    exact PF.eq_of_fields hw hp (Nat.eq_of_beq_eq_true h1) fun i hi => Nat.eq_of_beq_eq_true (h2 i hi)

theorem beq_wordK (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (S SI : Nat → Nat) (wd : List Int)
    (r : Nat) :
    Nat.beq (wordK n w (mask w) (pidn n w) S SI wd) r = (Nat.beq (Nat.shiftRight r (Nat.mul n w)) 0 &&
      allN n (fun i => Nat.beq (wimg w S SI wd i) (rd w r i))) := by
  rw [beq_of_fields (PF.w_pos hw) (wordK_shr hn hw S SI wd)]
  congr 1
  rw [Bool.eq_iff_iff, Raw.Orb.allN_iff, Raw.Orb.allN_iff]
  exact ⟨fun h i hi => by rw [← pg_wordK hn hw S SI wd i hi, rd_eq]; exact h i hi,
    fun h i hi => by rw [pg_wordK hn hw S SI wd i hi, ← rd_eq]; exact h i hi⟩

@[expose] noncomputable def wordPtK (n w : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int)
    (r : Nat) : Bool :=
  bAnd(szOK n w, bAnd(lettersK kS wd, Nat.beq (Nat.shiftRight r (Nat.mul n w)) 0 &&
    allN n (fun i => Nat.beq (wimg w S SI wd i) (rd w r i))))

theorem wordEqK_pt (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (S SI : Nat → Nat) (kS : Nat)
    (wd : List Int) (r : Nat) :
    wordEqK n w (mask w) (pidn n w) S SI kS wd r = wordPtK n w S SI kS wd r := by
  unfold wordEqK wordPtK
  rw [beq_wordK hn hw]

theorem beq_pcomp_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (T TI : Nat) :
    Nat.beq (pcomp n w (mask w) T TI) (pidn n w) =
      allN n (fun i => Nat.beq (rd w T (rd w TI i)) i) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Raw.Orb.allN_iff]
  constructor
  · intro e i hi
    have := congrArg (fun X => pg w (mask w) X i) e
    simp only [PF.pg_pcomp (n32 hn) hi, PF.pg_pidn hn hw hi] at this
    rw [rd_eq, rd_eq, this]
    exact Nat.beq_refl _
  · intro h
    refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ (n32 hn) (PF.w_pos hw))
      (PF.pidn_shr hn hw) fun i hi => ?_
    rw [PF.pg_pcomp (n32 hn) hi, PF.pg_pidn hn hw hi, ← rd_eq, ← rd_eq]
    exact Nat.eq_of_beq_eq_true (h i hi)

theorem beq_pcomp_r (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (t g T : Nat) :
    Nat.beq t (pcomp n w (mask w) g T) = (Nat.beq (Nat.shiftRight t (Nat.mul n w)) 0 &&
      allN n (fun i => Nat.beq (rd w t i) (rd w g (rd w T i)))) := by
  rw [show Nat.beq t (pcomp n w (mask w) g T) = Nat.beq (pcomp n w (mask w) g T) t by
    rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq]; exact eq_comm,
    beq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ (n32 hn) (PF.w_pos hw))]
  congr 1
  rw [Bool.eq_iff_iff, Raw.Orb.allN_iff, Raw.Orb.allN_iff]
  constructor
  · intro h i hi
    rw [rd_eq, rd_eq, rd_eq, ← PF.pg_pcomp (n32 hn) hi, Nat.eq_of_beq_eq_true (h i hi)]
    exact Nat.beq_refl _
  · intro h i hi
    rw [PF.pg_pcomp (n32 hn) hi, ← rd_eq, ← rd_eq, ← rd_eq, Nat.eq_of_beq_eq_true (h i hi)]
    exact Nat.beq_refl _

theorem beq_pcomp_pcomp (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (a b c d : Nat) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) c d) =
      allN n (fun i => Nat.beq (rd w a (rd w b i)) (rd w c (rd w d i))) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Raw.Orb.allN_iff]
  constructor
  · intro e i hi
    have := congrArg (fun X => pg w (mask w) X i) e
    simp only [PF.pg_pcomp (n32 hn) hi] at this
    rw [rd_eq, rd_eq, rd_eq, rd_eq, this]
    exact Nat.beq_refl _
  · intro h
    refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ (n32 hn) (PF.w_pos hw))
      (PF.pcomp_shr _ _ (n32 hn) (PF.w_pos hw)) fun i hi => ?_
    rw [PF.pg_pcomp (n32 hn) hi, PF.pg_pcomp (n32 hn) hi, ← rd_eq, ← rd_eq, ← rd_eq, ← rd_eq]
    exact Nat.eq_of_beq_eq_true (h i hi)

theorem beq_pcomp_pidnT (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (H T TI : Nat) :
    Nat.beq (pcomp n w (mask w) T TI) (pidn n w) =
      allN n (fun i => Nat.beq (rdT w H T (rdT w H TI i)) i) := by
  rw [beq_pcomp_pidn hn hw]
  simp only [rd_eq, rdT_eq]

theorem beq_pcomp_rT (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (H t g T : Nat) :
    Nat.beq t (pcomp n w (mask w) g T) = (Nat.beq (Nat.shiftRight t (Nat.mul n w)) 0 &&
      allN n (fun i => Nat.beq (rdT w H t i) (rdT w H g (rdT w H T i)))) := by
  rw [beq_pcomp_r hn hw]
  simp only [rd_eq, rdT_eq]

theorem beq_pcomp_pcompT (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (H a b c d : Nat) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) c d) =
      allN n (fun i => Nat.beq (rdT w H a (rdT w H b i)) (rdT w H c (rdT w H d i))) := by
  rw [beq_pcomp_pcomp hn hw]
  simp only [rd_eq, rdT_eq]

end CFSG.KS.PtC

end
