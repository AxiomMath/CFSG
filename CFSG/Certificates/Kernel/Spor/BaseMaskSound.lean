module

public import Certificates.Data.Kernel.Spor.BaseMask
public import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BaseMask

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH

theorem bsort_inj {n w m b c cnt : Nat} {T KS KSI : Nat → Nat}
    (hs : ∀ i < cnt, bsortPtK n w m b c cnt T KS KSI i = true) :
    ∀ a < cnt, ∀ a' < cnt, bkeyK n w m b c (T a) = bkeyK n w m b c (T a') → a = a' := by
  refine inj_of_sortH (T := fun i => bkeyK n w m b c (T i)) (S := r32 KS) (SI := r32 KSI)
    fun i hi => ?_
  have h := hs i hi
  unfold bsortPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h3
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
  simp only [Nat.blt_eq.mpr hc, ↓reduceIte] at h3
  exact Nat.blt_eq.mp h3

theorem bmS_shl (k : Nat) : Nat.shiftLeft (nat_lit 1) k = 2 ^ k := Nat.one_shiftLeft k

theorem bmS_testBit_lor_shl (M q p : Nat) :
    (Nat.lor M (Nat.shiftLeft (nat_lit 1) q)).testBit p = (M.testBit p || decide (q = p)) := by
  change (M ||| 1 <<< q).testBit p = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem bmS_beq_pair {x y x' y' : Nat}
    (h : Bool.rec (motive := fun _ => Bool) false (Nat.beq x' y') (Nat.beq x y) = true) :
    x = y ∧ x' = y' := by
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem mulKeyK_spec {w m b c : Nat} {T : Nat → Nat} {i j q : Nat}
    (h : mulKeyK w m b c T i j q = true) :
    pg w m (T i) (pg w m (T j) b) = pg w m (T q) b ∧
      pg w m (T i) (pg w m (T j) c) = pg w m (T q) c :=
  bmS_beq_pair h

theorem commKeyK_spec {w m b c : Nat} {T : Nat → Nat} {s g : Nat}
    (h : commKeyK w m b c T s g = true) :
    pg w m (T s) (pg w m (T g) b) = pg w m (T g) (pg w m (T s) b) ∧
      pg w m (T s) (pg w m (T g) c) = pg w m (T g) (pg w m (T s) c) :=
  bmS_beq_pair h

theorem conjMemK_spec {w m b c : Nat} {T A D : Nat → Nat} {y len : Nat}
    (h : conjMemK w m b c T A D y len = true) : ∀ e < len,
    pg w m (T y) (pg w m (T (r32 A e)) b) = pg w m (T (r32 D e)) (pg w m (T y) b) ∧
      pg w m (T y) (pg w m (T (r32 A e)) c) = pg w m (T (r32 D e)) (pg w m (T y) c) :=
  fun e he => bmS_beq_pair (allN_spec h e he)

theorem bmS_or_foldr (J : Nat → Nat) (q : Nat) : ∀ (l : List Nat) (s : Nat),
    (l.foldr (fun e M => Nat.lor M (Nat.shiftLeft (nat_lit 1) (J e))) s).testBit q = true ↔
      s.testBit q = true ∨ ∃ e ∈ l, J e = q
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldr_cons, bmS_testBit_lor_shl, Bool.or_eq_true, bmS_or_foldr J q l s,
      decide_eq_true_iff]
    constructor
    · rintro ((h | ⟨e, he, rfl⟩) | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, rfl⟩
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
    · rintro (h | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inr rfl
        · exact Or.inl (Or.inr ⟨e, he, rfl⟩)

theorem bmS_maskK (I : Nat → Nat) (o len q : Nat) :
    (maskK I o len).testBit q = true ↔ ∃ e < len, r32 I (o + e) = q := by
  unfold maskK
  rw [Orb.foldN_eq, bmS_or_foldr (fun e => r32 I (Nat.add o e)), Nat.zero_testBit]
  simp only [List.mem_range, Bool.false_eq_true, false_or]
  rfl

theorem bmS_dist (cnt : Nat) (J : Nat → Nat) (F : Nat → Nat → Nat)
    (hF : ∀ e M, F e M = if M.testBit (J e) = true then Nat.lor M (Nat.shiftLeft (nat_lit 1) cnt)
      else Nat.lor M (Nat.shiftLeft (nat_lit 1) (J e))) :
    ∀ l : List Nat, l.foldr F 0 < Nat.shiftLeft (nat_lit 1) cnt →
      (∀ e ∈ l, J e < cnt) ∧ (∀ e ∈ l, ∀ e' ∈ l, J e = J e' → e = e') ∧
        ∀ q, (l.foldr F 0).testBit q = true ↔ ∃ e ∈ l, J e = q
  | [], _ => by simp
  | a :: l, h => by
    rw [List.foldr_cons, hF] at h ⊢
    have hle : ∀ X Y : Nat, X ≤ Nat.lor X Y := fun X Y =>
      Nat.le_of_testBit fun i hi => by
        change (X ||| Y).testBit i = true
        rw [Nat.testBit_or, hi, Bool.true_or]
    have hle' : ∀ X Y : Nat, Y ≤ Nat.lor X Y := fun X Y =>
      Nat.le_of_testBit fun i hi => by
        change (X ||| Y).testBit i = true
        rw [Nat.testBit_or, hi, Bool.or_true]
    by_cases hb : (l.foldr F 0).testBit (J a) = true
    · rw [if_pos hb] at h
      exact absurd (Nat.lt_of_le_of_lt (hle' _ _) h) (Nat.lt_irrefl _)
    · rw [if_neg hb] at h ⊢
      obtain ⟨ih1, ih2, ih3⟩ := bmS_dist cnt J F hF l (Nat.lt_of_le_of_lt (hle _ _) h)
      have ha : J a < cnt := by
        by_contra hc
        have h1 : Nat.shiftLeft (nat_lit 1) cnt ≤ Nat.shiftLeft (nat_lit 1) (J a) := by
          rw [bmS_shl, bmS_shl]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans h1 (hle' _ _)) h) (Nat.lt_irrefl _)
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact ha
        · exact ih1 e he
      · intro e he e' he' hee
        rcases List.mem_cons.1 he with rfl | hl1 <;> rcases List.mem_cons.1 he' with rfl | hl2
        · rfl
        · exact absurd ((ih3 _).2 ⟨e', hl2, hee.symm⟩) hb
        · exact absurd ((ih3 _).2 ⟨e, hl1, hee⟩) hb
        · exact ih2 e hl1 e' hl2 hee
      · intro q
        rw [bmS_testBit_lor_shl, Bool.or_eq_true, ih3, decide_eq_true_iff]
        constructor
        · rintro (⟨e, he, rfl⟩ | rfl)
          · exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩
          · exact ⟨a, List.mem_cons_self, rfl⟩
        · rintro ⟨e, he, rfl⟩
          rcases List.mem_cons.1 he with rfl | he
          · exact Or.inr rfl
          · exact Or.inl ⟨e, he, rfl⟩

theorem bmS_and_foldr (G : Nat → Nat) (q : Nat) : ∀ (l : List Nat) (s : Nat),
    (l.foldr (fun j C => Nat.land C (G j)) s).testBit q = true ↔
      s.testBit q = true ∧ ∀ j ∈ l, (G j).testBit q = true
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldr_cons]
    change ((List.foldr _ s l) &&& G a).testBit q = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, bmS_and_foldr G q l s]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem bmS_cover (M : Nat) (X : Nat → Nat) (F : Nat → Nat → Nat)
    (hF : ∀ h U, F h U = if Nat.beq (Nat.land M (X h)) M = true then Nat.lor U (X h) else U)
    (q : Nat) : ∀ l : List Nat, (l.foldr F 0).testBit q = true →
      ∃ h ∈ l, Nat.land M (X h) = M ∧ (X h).testBit q = true
  | [], hq => by simp at hq
  | a :: l, hq => by
    rw [List.foldr_cons, hF] at hq
    split_ifs at hq with hb
    · change (List.foldr F 0 l ||| X a).testBit q = true at hq
      rw [Nat.testBit_or, Bool.or_eq_true] at hq
      rcases hq with hq | hq
      · obtain ⟨h, hl, h1, h2⟩ := bmS_cover M X F hF q l hq
        exact ⟨h, List.mem_cons_of_mem _ hl, h1, h2⟩
      · exact ⟨a, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, hq⟩
    · obtain ⟨h, hl, h1, h2⟩ := bmS_cover M X F hF q l hq
      exact ⟨h, List.mem_cons_of_mem _ hl, h1, h2⟩

theorem memberK_spec {w m b c cnt : Nat} {T I : Nat → Nat} {o k : Nat}
    (h : memberK w m b c cnt T I o k = true) :
    r32 I o = 0 ∧ (∀ e < 2 ^ k, r32 I (o + e) < cnt) ∧
      (∀ e < 2 ^ k, ∀ e' < 2 ^ k, r32 I (o + e) = r32 I (o + e') → e = e') ∧
      ∀ e < 2 ^ k, ∀ j < k, mulKeyK w m b c T (r32 I (o + e)) (r32 I (o + 2 ^ j))
        (r32 I (o + (e ^^^ 2 ^ j))) = true := by
  unfold memberK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold distinctK at h2
  rw [Nat.blt_eq, Orb.foldN_eq] at h2
  obtain ⟨hd1, hd2, -⟩ := bmS_dist cnt (fun e => r32 I (o + e)) _
    (fun e M => by rw [Orb.strictN_eq, Orb.nIf_eq, Orb.hasBit_eq]; rfl) _ h2
  have hr : ∀ e < 2 ^ k, e ∈ List.range (Nat.shiftLeft (nat_lit 1) k) := fun e he =>
    List.mem_range.2 (by rw [bmS_shl]; exact he)
  refine ⟨Nat.eq_of_beq_eq_true h1, fun e he => hd1 e (hr e he),
    fun e he e' he' hee => hd2 e (hr e he) e' (hr e' he') hee, ?_⟩
  intro e he j hj
  have h4 := allN_spec h3 e (by rw [bmS_shl]; exact he)
  beta_reduce at h4
  rw [Orb.strictB_eq] at h4
  have h5 := allN_spec h4 j hj
  rw [← bmS_shl]
  exact h5

theorem involMaskK_spec {w m b c cnt : Nat} {T IV : Nat → Nat} {niv : Nat}
    (h : involMaskK w m b c cnt T IV niv = true) :
    maskK IV 0 niv < 2 ^ cnt ∧ ∀ i < cnt,
      (hasBit (maskK IV 0 niv) i = true ↔ i ≠ 0 ∧ mulKeyK w m b c T i i 0 = true) := by
  unfold involMaskK at h
  rw [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.blt_eq] at h1
  refine ⟨by rw [← bmS_shl]; exact h1, fun i hi => ?_⟩
  have hx := allN_spec h2 i hi
  beta_reduce at hx
  generalize hasBit (maskK IV 0 niv) i = bb at hx ⊢
  generalize mulKeyK w m b c T i i 0 = kk at hx ⊢
  cases hz : Nat.beq i (nat_lit 0)
  · have hi0 : i ≠ 0 := Nat.ne_of_beq_eq_false hz
    rw [hz] at hx
    cases bb <;> cases kk <;> simp_all
  · have hi0 : i = 0 := Nat.eq_of_beq_eq_true hz
    rw [hz] at hx
    cases bb <;> cases kk <;> simp_all

theorem cmaskK_spec {w m b c : Nat} {T IV : Nat → Nat} {niv IM C g : Nat}
    (h : cmaskK w m b c T IV niv IM C g = true) :
    Nat.land C IM = C ∧ ∀ t < niv,
      (hasBit C (r32 IV t) = true ↔ commKeyK w m b c T (r32 IV t) g = true) := by
  unfold cmaskK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun t ht => ?_⟩
  have hx := allN_spec h2 t ht
  beta_reduce at hx
  rw [Orb.strictB_eq] at hx
  generalize hasBit C (r32 IV t) = bb at hx ⊢
  generalize commKeyK w m b c T (r32 IV t) g = kk at hx ⊢
  cases bb <;> cases kk <;> simp_all

theorem extK_spec {I GS CM : Nat → Nat} {IM o go k on nc : Nat}
    (h : extK I GS CM IM o go k on nc = true) {s : Nat} (hs : hasBit IM s = true)
    (hsM : hasBit (maskK I o (2 ^ k)) s = false)
    (hc : ∀ j < k, hasBit (CM (r32 GS (go + j))) s = true) :
    ∃ hh < nc, (∀ q, hasBit (maskK I o (2 ^ k)) q = true →
        hasBit (maskK I (on + hh * 2 ^ (k + 1)) (2 ^ (k + 1))) q = true) ∧
      hasBit (maskK I (on + hh * 2 ^ (k + 1)) (2 ^ (k + 1))) s = true := by
  unfold extK at h
  simp only [Orb.strictB_eq] at h
  set M := maskK I o (Nat.shiftLeft (nat_lit 1) k) with hM
  have e := Nat.eq_of_beq_eq_true h
  rw [← bmS_shl, Orb.hasBit_eq] at hsM
  rw [Orb.hasBit_eq] at hs
  have hCs : (foldN k (fun j C => Nat.land C (CM (r32 GS (Nat.add go j))))
      (Nat.xor IM (Nat.land IM M))).testBit s = true := by
    rw [Orb.foldN_eq, bmS_and_foldr]
    refine ⟨?_, fun j hj => ?_⟩
    · change (IM ^^^ (IM &&& M)).testBit s = true
      rw [Nat.testBit_xor, Nat.testBit_and, hs, hsM]
      rfl
    · rw [← Orb.hasBit_eq]
      exact hc j (List.mem_range.1 hj)
  have hUs : (coverK I on nc (Nat.succ k) M).testBit s = true := by
    have e2 := congrArg (fun x => Nat.testBit x s) e
    change Nat.testBit ((_ : Nat) &&& (_ : Nat)) s = _ at e2
    rw [Nat.testBit_and, hCs, Bool.true_and] at e2
    exact e2
  unfold coverK at hUs
  rw [Orb.foldN_eq] at hUs
  obtain ⟨hh, hmem, h1, h2⟩ := bmS_cover M
    (fun h => maskK I (Nat.add on (Nat.mul h (Nat.shiftLeft (nat_lit 1) (Nat.succ k))))
      (Nat.shiftLeft (nat_lit 1) (Nat.succ k))) _
    (fun h U => by rw [Orb.strictN_eq, Orb.nIf_eq]) s _ hUs
  refine ⟨hh, List.mem_range.1 hmem, fun q hq => ?_, ?_⟩
  · rw [← bmS_shl, Orb.hasBit_eq] at hq
    rw [← bmS_shl, Orb.hasBit_eq]
    have e3 := congrArg (fun x => Nat.testBit x q) h1
    change (M &&& _).testBit q = M.testBit q at e3
    rw [Nat.testBit_and, hq, Bool.true_and] at e3
    exact e3
  · rw [← bmS_shl, Orb.hasBit_eq]
    exact h2

end CFSG.KS.BaseMask

end
