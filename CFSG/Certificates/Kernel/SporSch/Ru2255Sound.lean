module

public import Certificates.Data.Kernel.SporSch.Ru2255K
public import CFSG.Certificates.Kernel.SporSch.Ru2250Sound
public import CFSG.Sporadic.Schreier.PairWords
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit

public section

namespace CFSG.KS.Ru2255

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co2Mem CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.KS.SporSch Finset

variable {n w : Nat}

theorem cnt3K_eq (TR : Nat → Nat) (o0 o1 o2 c1 c2 : Nat) (P : Nat → Nat → Nat → Bool)
    (lo len : Nat) : cnt3K TR o0 o1 o2 c1 c2 P lo len = ∑ i ∈ range len, ∑ b ∈ range c1,
      ∑ c ∈ range c2, if P (TR (o0 + (lo + i))) (TR (o1 + b)) (TR (o2 + c)) = true then 1
        else 0 := by
  unfold cnt3K
  rw [MBT.foldN_add' (g := fun i => ∑ b ∈ range c1, ∑ c ∈ range c2,
      if P (TR (o0 + (lo + i))) (TR (o1 + b)) (TR (o2 + c)) = true then 1 else 0), Nat.zero_add]
  intro i s
  rw [PackFld.strictN_eqP, MBT.foldN_add' (g := fun b => ∑ c ∈ range c2,
      if P (TR (o0 + (lo + i))) (TR (o1 + b)) (TR (o2 + c)) = true then 1 else 0), Nat.zero_add]
  · rfl
  · intro b s'
    rw [PackFld.strictN_eqP, MBT.foldN_add' (g := fun c =>
        if P (TR (o0 + (lo + i))) (TR (o1 + b)) (TR (o2 + c)) = true then 1 else 0), Nat.zero_add]
    · rfl
    · intro c s''
      rw [PackFld.strictN_eqP, Ru2250.nIf_eq]
      rfl

theorem cnt3K_blocks (TR : Nat → Nat) (o0 o1 o2 c1 c2 : Nat) (P : Nat → Nat → Nat → Bool)
    (B : Nat) : ∀ q, cnt3K TR o0 o1 o2 c1 c2 P 0 (B * q) =
      ∑ k ∈ range q, cnt3K TR o0 o1 o2 c1 c2 P (B * k) B
  | 0 => by rw [Nat.mul_zero, cnt3K_eq]; rfl
  | q + 1 => by
    rw [sum_range_succ, ← cnt3K_blocks TR o0 o1 o2 c1 c2 P B q, cnt3K_eq, cnt3K_eq, cnt3K_eq,
      Nat.mul_succ, sum_range_add]
    simp only [Nat.zero_add]

section Levels

variable {kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hb : Binds n w PS kS nb BP S base)
  (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
  (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
include hb hh hl

theorem prod3A_eq (h3 : 3 ≤ nb) {a b c : Nat} (ha : a < rcnt (LR 0)) (hb' : b < rcnt (LR 1))
    (hc : c < rcnt (LR 2)) :
    prod3A n (rawLevels n S base) a b c =
      compA n (compA n (unpack n w (TR (Nat.add (roff n (n * w) (LR 0)) a)))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 1)) b))))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 2)) c))) := by
  unfold prod3A
  rw [(levelTr_sound hb hh hl (i := 0) (by omega)).2 a ha,
    (levelTr_sound hb hh hl (i := 1) (by omega)).2 b hb',
    (levelTr_sound hb hh hl (i := 2) (by omega)).2 c hc]

theorem count3_eq (h3 : 3 ≤ nb) {p : Array Nat → Bool} {P : Nat → Nat → Nat → Bool}
    (hP : ∀ a < rcnt (LR 0), ∀ b < rcnt (LR 1), ∀ c < rcnt (LR 2),
      p (compA n (compA n (unpack n w (TR (Nat.add (roff n (n * w) (LR 0)) a)))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 1)) b))))
        (unpack n w (TR (Nat.add (roff n (n * w) (LR 2)) c)))) =
      P (TR (Nat.add (roff n (n * w) (LR 0)) a)) (TR (Nat.add (roff n (n * w) (LR 1)) b))
        (TR (Nat.add (roff n (n * w) (LR 2)) c))) :
    count3 n (rawLevels n S base) p =
      cnt3K TR (roff n (n * w) (LR 0)) (roff n (n * w) (LR 1)) (roff n (n * w) (LR 2))
        (rcnt (LR 1)) (rcnt (LR 2)) P 0 (rcnt (LR 0)) := by
  rw [cnt3K_eq, count3, (levelTr_sound hb hh hl (i := 0) (by omega)).1,
    (levelTr_sound hb hh hl (i := 1) (by omega)).1, (levelTr_sound hb hh hl (i := 2) (by omega)).1]
  refine sum_congr rfl fun a ha => sum_congr rfl fun b hb' => sum_congr rfl fun c hc => ?_
  rw [mem_range] at ha hb' hc
  rw [prod3A_eq hb hh hl h3 ha hb' hc, hP a ha b hb' c hc, Nat.zero_add]
  rfl

end Levels

section Sq

variable {T0 T1 T2 Z : Nat} (h1 : ∀ x < n, pg w (mask w) T1 x < n)
  (h2 : ∀ x < n, pg w (mask w) T2 x < n)

include h1 h2 in
theorem comp3_get {x : Nat} (hx : x < n) :
    (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w T2))[x]! =
      tv3 w (mask w) T0 T1 T2 x := by
  rw [compA_get hx, Orb.unpack_get hx, Ru2250.comp_get h1 (h2 x hx)]
  rfl

include h1 h2 in
theorem tv3_lt (h0 : ∀ x < n, pg w (mask w) T0 x < n) {x : Nat} (hx : x < n) :
    tv3 w (mask w) T0 T1 T2 x < n := h0 _ (h1 _ (h2 x hx))

include h1 h2 in
theorem sq_eq (h0 : ∀ x < n, pg w (mask w) T0 x < n) :
    (allLt n fun x =>
      (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w T2))[
        (compA n (compA n (unpack n w T0) (unpack n w T1)) (unpack n w T2))[x]!]! ==
        (unpack n w Z)[x]!) = sqK n w (mask w) T0 T1 T2 Z := by
  unfold sqK
  refine Ru2250.allLt_eq_allN fun x hx => ?_
  rw [comp3_get h1 h2 hx, comp3_get h1 h2 (tv3_lt h1 h2 h0 hx), Orb.unpack_get hx]
  cases e : Nat.beq (tv3 w (mask w) T0 T1 T2 (tv3 w (mask w) T0 T1 T2 x)) (pg w (mask w) Z x)
  · simp only [beq_eq_false_iff_ne]
    exact fun h => absurd (Nat.beq_eq.mpr h) (by simp [e])
  · exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true e)

end Sq

abbrev bs4 : List Nat := [0, 1, 2, 3]

theorem iterK_spec {f : Nat → Nat} {X : Equiv.Perm (Fin n)} (hf : ∀ x : Fin n, f x = X x) :
    ∀ e (x : Fin n), iterK f e x = ((X ^ e) x : Nat)
  | 0, x => rfl
  | e + 1, x => by
    change f (iterK f e x) = _
    rw [iterK_spec hf e x, hf, pow_succ', Equiv.Perm.mul_apply]

theorem fixBK_iff (hn : 4 ≤ n) {f : Nat → Nat} {X : Equiv.Perm (Fin n)}
    (hf : ∀ x : Fin n, f x = X x) (e : Nat) :
    fixBK f e = true ↔ ∀ x : Fin n, (x : Nat) ∈ bs4 → (X ^ e) x = x := by
  unfold fixBK
  rw [Ru2250.allN_iff]
  constructor
  · intro h x hx
    have hx4 : (x : Nat) < 4 := by simp [bs4] at hx; omega
    have := Nat.eq_of_beq_eq_true (h x hx4)
    rw [iterK_spec hf e x] at this
    exact Fin.ext this
  · intro h b hb
    have hb4 : b < 4 := hb
    have e1 := h ⟨b, by omega⟩ (by simp [bs4]; omega)
    exact Nat.beq_eq.mpr ((iterK_spec hf e ⟨b, by omega⟩).trans (congrArg Fin.val e1))

theorem fixBK_iff_eq_one (hn : 4 ≤ n) {H : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H bs4)
    {f : Nat → Nat} {X : Equiv.Perm (Fin n)} (hf : ∀ x : Fin n, f x = X x) (hX : X ∈ H) (e : Nat) :
    fixBK f e = true ↔ X ^ e = 1 := by
  rw [fixBK_iff hn hf]
  constructor
  · exact hH _ (H.pow_mem hX e)
  · intro h x _
    rw [h]
    rfl

theorem bIf_not (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

theorem ordK_iff (hn : 4 ≤ n) {H : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H bs4)
    {f : Nat → Nat} {X : Equiv.Perm (Fin n)} (hf : ∀ x : Fin n, f x = X x) (hX : X ∈ H) :
    ordK f = true ↔ X ^ 14 = 1 ∧ X ^ 7 ≠ 1 ∧ X ^ 2 ≠ 1 := by
  unfold ordK
  rw [bAnd_iff, bAnd_iff, bIf_not, bIf_not, Bool.not_eq_true', Bool.not_eq_true',
    fixBK_iff_eq_one hn hH hf hX, ← Bool.not_eq_true, ← Bool.not_eq_true,
    fixBK_iff_eq_one hn hH hf hX, fixBK_iff_eq_one hn hH hf hX]

theorem fibK_iff (hn : 4 ≤ n) {H : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H bs4)
    {AG T0 T1 T2 : Nat} {A R : Equiv.Perm (Fin n)} (hA : Orb.PRep n w AG A)
    (hR : ∀ x : Fin n, tv3 w (mask w) T0 T1 T2 x = R x) (hAm : A ∈ H) (hRm : R ∈ H) :
    fibK w (mask w) AG T0 T1 T2 = true ↔ (A * R) ^ 13 = 1 ∧ (A * R * A * (R * R)) ^ 29 = 1 := by
  unfold fibK
  have f1 : ∀ x : Fin n, pg w (mask w) AG (tv3 w (mask w) T0 T1 T2 x) = (A * R) x := fun x => by
    rw [hR x, hA (R x)]
    rfl
  have f2 : ∀ x : Fin n, pg w (mask w) AG (tv3 w (mask w) T0 T1 T2 (pg w (mask w) AG
      (tv3 w (mask w) T0 T1 T2 (tv3 w (mask w) T0 T1 T2 x)))) = (A * R * A * (R * R)) x :=
    fun x => by
      rw [hR x, hR (R x), hA (R (R x)), hR (A (R (R x))), hA (R (A (R (R x))))]
      rfl
  rw [bAnd_iff, fixBK_iff_eq_one hn hH f1 (H.mul_mem hAm hRm),
    fixBK_iff_eq_one hn hH f2 (H.mul_mem (H.mul_mem (H.mul_mem hAm hRm) hAm) (H.mul_mem hRm hRm))]

theorem conjK_sound {G X Y : Nat} {g y : Equiv.Perm (Fin n)} (hG : Orb.PRep n w G g)
    (hY : Orb.PRep n w Y y) (h : conjK n w (mask w) G X Y = true) :
    ∀ x : Fin n, pg w (mask w) X x = (g * y * g⁻¹) x := by
  intro x
  have e := Nat.eq_of_beq_eq_true (allN_spec h _ (g⁻¹ x).2)
  have hx : g (g⁻¹ x) = x := by simp
  rw [hG (g⁻¹ x), hY (g⁻¹ x), hG (y (g⁻¹ x)), hx] at e
  rw [e]
  rfl

theorem conjRK_sound {G X Y : Nat} {g xp : Equiv.Perm (Fin n)} (hG : Orb.PRep n w G g)
    (hX : Orb.PRep n w X xp) (h : conjRK n w (mask w) G X Y = true) :
    Orb.PRep n w Y (g⁻¹ * xp * g) := by
  intro x
  obtain ⟨hlt, e⟩ := (bAnd_iff _ _).1 (allN_spec h _ x.2)
  have hlt' : pg w (mask w) Y x < n := Nat.blt_eq.mp hlt
  have e' := Nat.eq_of_beq_eq_true e
  rw [hG x, hX (g x)] at e'
  have e2 : g ⟨pg w (mask w) Y x, hlt'⟩ = xp (g x) := Fin.ext (by rw [← hG]; exact e')
  have : (⟨pg w (mask w) Y x, hlt'⟩ : Fin n) = (g⁻¹ * xp * g) x := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e2]
    simp
  exact congrArg Fin.val this

end CFSG.KS.Ru2255

end
