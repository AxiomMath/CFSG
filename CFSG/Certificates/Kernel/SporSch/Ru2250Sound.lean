module

public import Certificates.Data.Kernel.SporSch.Ru2250K
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.RawAgree

public section

namespace CFSG.KS.Ru2250

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier Finset

variable {n w : Nat}

theorem allN_iff {k : Nat} {f : Nat → Bool} : allN k f = true ↔ ∀ i < k, f i = true :=
  ⟨allN_spec, PackFld.allN_of_forall⟩

theorem allLt_eq_allN {k : Nat} {f g : Nat → Bool} (e : ∀ i < k, f i = g i) :
    allLt k f = allN k g := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.Monster.B.Co2.allLt_iff, allN_iff]
  exact ⟨fun h i hi => (e i hi) ▸ h i hi, fun h i hi => (e i hi).symm ▸ h i hi⟩

theorem nIf_eq (c : Bool) (a b : Nat) :
    Bool.rec (motive := fun _ => Nat) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem cntK_eq (TR : Nat → Nat) (o0 o1 c1 : Nat) (P : Nat → Nat → Nat → Nat → Bool)
    (lo len : Nat) : cntK TR o0 o1 c1 P lo len = ∑ i ∈ range len, ∑ b ∈ range c1,
      if P (lo + i) b (TR (o0 + (lo + i))) (TR (o1 + b)) = true then 1 else 0 := by
  unfold cntK
  rw [CFSG.KS.SporSch.MBT.foldN_add' (g := fun i => ∑ b ∈ range c1,
      if P (lo + i) b (TR (o0 + (lo + i))) (TR (o1 + b)) = true then 1 else 0), Nat.zero_add]
  intro i s
  rw [PackFld.strictN_eqP, PackFld.strictN_eqP,
    CFSG.KS.SporSch.MBT.foldN_add' (g := fun b => if P (lo + i) b (TR (o0 + (lo + i))) (TR (o1 + b)) = true
      then 1 else 0), Nat.zero_add]
  · rfl
  · intro b s'
    rw [PackFld.strictN_eqP, nIf_eq]
    rfl

theorem cntK_blocks (TR : Nat → Nat) (o0 o1 c1 : Nat) (P : Nat → Nat → Nat → Nat → Bool)
    (B : Nat) : ∀ q, cntK TR o0 o1 c1 P 0 (B * q) =
      ∑ k ∈ range q, cntK TR o0 o1 c1 P (B * k) B
  | 0 => by rw [Nat.mul_zero, cntK_eq]; rfl
  | q + 1 => by
    rw [sum_range_succ, ← cntK_blocks TR o0 o1 c1 P B q, cntK_eq, cntK_eq, cntK_eq,
      Nat.mul_succ, sum_range_add]
    simp only [Nat.zero_add]

theorem rowK_spec {TR : Nat → Nat} {o0 o1 : Nat} {P : Nat → Nat → Nat → Nat → Bool}
    {a blo blen : Nat} (h : rowK TR o0 o1 P a blo blen = true) :
    ∀ i < blen, P a (blo + i) (TR (o0 + a)) (TR (o1 + (blo + i))) = true := by
  intro i hi
  rw [rowK, PackFld.strictB_eqP] at h
  have h1 := allN_spec h i hi
  rw [PackFld.strictB_eqP, PackFld.strictB_eqP] at h1
  exact h1

theorem rowK_halves {TR : Nat → Nat} {o0 o1 c0 : Nat} {P : Nat → Nat → Nat → Nat → Bool}
    (h : ∀ k < 2 * c0, rowK TR o0 o1 P (k / 2) (4 * (k % 2)) 4 = true) :
    ∀ a < c0, ∀ b < 8, P a b (TR (o0 + a)) (TR (o1 + b)) = true := by
  intro a ha b hb
  have hk : 2 * a + b / 4 < 2 * c0 := by omega
  have := rowK_spec (h _ hk) (b % 4) (Nat.mod_lt b (by norm_num))
  have e1 : (2 * a + b / 4) / 2 = a := by omega
  have e2 : 4 * ((2 * a + b / 4) % 2) + b % 4 = b := by omega
  rwa [e1, e2] at this

section Levels

variable {kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hb : Binds n w PS kS nb BP S base)
  (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
  (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
include hb hh hl

omit hb hh in
theorem tr_lt {i : Nat} (hi : i < nb) {k : Nat} (hk : k < rcnt (LR i)) :
    ∀ x < n, pg w (mask w) (TR (Nat.add (roff n (n * w) (LR i)) k)) x < n := by
  obtain ⟨-, -, -, -, -, hperm⟩ := Orb.levelK_facts (hl i hi)
  exact fun x hx => Nat.blt_eq.mp (allN_spec (range_of_permOK (hperm k hk)) x hx)

theorem prod2A_eq (h2 : 2 ≤ nb) {a b : Nat} (ha : a < rcnt (LR 0)) (hb' : b < rcnt (LR 1)) :
    prod2A n (rawLevels n S base) a b = compA n (unpack n w (TR (Nat.add (roff n (n * w) (LR 0)) a)))
      (unpack n w (TR (Nat.add (roff n (n * w) (LR 1)) b))) := by
  unfold prod2A
  rw [(levelTr_sound hb hh hl (i := 0) (by omega)).2 a ha,
    (levelTr_sound hb hh hl (i := 1) (by omega)).2 b hb']

theorem count2_eq (h2 : 2 ≤ nb) {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Bool}
    (hP : ∀ a < rcnt (LR 0), ∀ b < rcnt (LR 1),
      p (compA n (unpack n w (TR (Nat.add (roff n (n * w) (LR 0)) a)))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 1)) b)))) =
      P a b (TR (Nat.add (roff n (n * w) (LR 0)) a)) (TR (Nat.add (roff n (n * w) (LR 1)) b))) :
    count2 n (rawLevels n S base) p =
      cntK TR (roff n (n * w) (LR 0)) (roff n (n * w) (LR 1)) (rcnt (LR 1)) P 0 (rcnt (LR 0)) := by
  rw [cntK_eq, count2, (levelTr_sound hb hh hl (i := 0) (by omega)).1,
    (levelTr_sound hb hh hl (i := 1) (by omega)).1]
  refine sum_congr rfl fun a ha => sum_congr rfl fun b hb' => ?_
  rw [mem_range] at ha hb'
  rw [prod2A_eq hb hh hl h2 ha hb', hP a ha b hb', Nat.zero_add]
  rfl

theorem all2_of_forall (h2 : 2 ≤ nb) {p : Array Nat → Bool}
    (hP : ∀ a < rcnt (LR 0), ∀ b < rcnt (LR 1),
      p (compA n (unpack n w (TR (Nat.add (roff n (n * w) (LR 0)) a)))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 1)) b)))) = true) :
    all2 n (rawLevels n S base) p = true := by
  unfold all2
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro a ha
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro b hb'
  rw [(levelTr_sound hb hh hl (i := 0) (by omega)).1] at ha
  rw [(levelTr_sound hb hh hl (i := 1) (by omega)).1] at hb'
  rw [prod2A_eq hb hh hl h2 ha hb']
  exact hP a ha b hb'

end Levels

section Tests

variable {T0 T1 : Nat} (h0 : ∀ x < n, pg w (mask w) T0 x < n)
  (h1 : ∀ x < n, pg w (mask w) T1 x < n)

omit h0 in
include h1 in
theorem comp_get {x : Nat} (hx : x < n) :
    (compA n (unpack n w T0) (unpack n w T1))[x]! = tv w (mask w) T0 T1 x := by
  rw [CFSG.Monster.B.Co2.compA_get hx, Orb.unpack_get hx, Orb.unpack_get (h1 x hx)]
  rfl

include h0 h1 in
theorem tv_lt {x : Nat} (hx : x < n) : tv w (mask w) T0 T1 x < n := h0 _ (h1 x hx)

include h0 h1 in
theorem sq_eq : eqA n (compA n (compA n (unpack n w T0) (unpack n w T1))
      (compA n (unpack n w T0) (unpack n w T1))) (idA n) =
    allN n (fun x => Nat.beq (tv w (mask w) T0 T1 (tv w (mask w) T0 T1 x)) x) := by
  unfold eqA
  refine allLt_eq_allN fun x hx => ?_
  rw [CFSG.Monster.B.Co2.compA_get hx, comp_get h1 hx, comp_get h1 (tv_lt h0 h1 hx),
    CFSG.Monster.B.Co2.idA_get hx]
  cases e : Nat.beq (tv w (mask w) T0 T1 (tv w (mask w) T0 T1 x)) x
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

include h1 in
theorem id_eq : eqA n (compA n (unpack n w T0) (unpack n w T1)) (idA n) =
    allN n (fun x => Nat.beq (tv w (mask w) T0 T1 x) x) := by
  unfold eqA
  refine allLt_eq_allN fun x hx => ?_
  rw [comp_get h1 hx, CFSG.Monster.B.Co2.idA_get hx]
  cases e : Nat.beq (tv w (mask w) T0 T1 x) x
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

include h0 h1 in
theorem invol_eq : (eqA n (compA n (compA n (unpack n w T0) (unpack n w T1))
      (compA n (unpack n w T0) (unpack n w T1))) (idA n) &&
      !eqA n (compA n (unpack n w T0) (unpack n w T1)) (idA n)) = invK n w (mask w) T0 T1 := by
  rw [sq_eq h0 h1, id_eq h1, invK]
  cases allN n (fun x => Nat.beq (tv w (mask w) T0 T1 (tv w (mask w) T0 T1 x)) x) <;>
    cases allN n (fun x => Nat.beq (tv w (mask w) T0 T1 x) x) <;> rfl

theorem length_filter_range (q : Nat → Bool) :
    ∀ k, ((List.range k).filter q).length = ∑ i ∈ range k, if q i = true then 1 else 0
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range q k,
      sum_range_succ]
    cases h : q k <;> simp [List.filter, h]

include h1 in
theorem fixedList_length :
    (fixedList n (compA n (unpack n w T0) (unpack n w T1))).length = fixK n w (mask w) T0 T1 := by
  unfold fixedList fixK
  rw [CFSG.KS.SporSch.MBT.foldN_add' (g := fun x => if Nat.beq (tv w (mask w) T0 T1 x) x = true then 1 else 0)
    (fun x s => by rw [nIf_eq]; rfl), Nat.zero_add, length_filter_range]
  refine sum_congr rfl fun x hx => ?_
  rw [comp_get h1 (mem_range.mp hx)]
  cases e : Nat.beq (tv w (mask w) T0 T1 x) x
  · have : tv w (mask w) T0 T1 x ≠ x := fun h => by rw [h, Nat.beq_refl] at e; exact absurd e (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true e]

include h0 h1 in
theorem comm_eq {X : Nat} (hX : ∀ x < n, pg w (mask w) X x < n) :
    eqA n (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w X))
      (compA n (unpack n w X) (compA n (unpack n w T0) (unpack n w T1))) =
    cmK n w (mask w) T0 T1 X := by
  unfold eqA cmK
  refine allLt_eq_allN fun x hx => ?_
  rw [CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.compA_get hx, Orb.unpack_get hx,
    comp_get h1 (hX x hx), comp_get h1 hx, Orb.unpack_get (tv_lt h0 h1 hx)]
  cases e : Nat.beq (tv w (mask w) T0 T1 (pg w (mask w) X x)) (pg w (mask w) X (tv w (mask w) T0 T1 x))
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

include h0 h1 in
theorem pair_eq {X Y : Nat} (hX : ∀ x < n, pg w (mask w) X x < n) :
    (!eqA n (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w X))
      (compA n (unpack n w Y) (compA n (unpack n w T0) (unpack n w T1)))) =
    prK n w (mask w) T0 T1 X Y := by
  have e : eqA n (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w X))
      (compA n (unpack n w Y) (compA n (unpack n w T0) (unpack n w T1))) =
      allN n (fun x => Nat.beq (tv w (mask w) T0 T1 (pg w (mask w) X x))
        (pg w (mask w) Y (tv w (mask w) T0 T1 x))) := by
    unfold eqA
    refine allLt_eq_allN fun x hx => ?_
    rw [CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.compA_get hx, Orb.unpack_get hx,
      comp_get h1 (hX x hx), comp_get h1 hx, Orb.unpack_get (tv_lt h0 h1 hx)]
    cases e : Nat.beq (tv w (mask w) T0 T1 (pg w (mask w) X x))
      (pg w (mask w) Y (tv w (mask w) T0 T1 x))
    · simp only [beq_eq_false_iff_ne]
      exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
    · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)
  rw [e, prK]
  cases allN n (fun x => Nat.beq (tv w (mask w) T0 T1 (pg w (mask w) X x))
    (pg w (mask w) Y (tv w (mask w) T0 T1 x))) <;> rfl

end Tests

end CFSG.KS.Ru2250

end
