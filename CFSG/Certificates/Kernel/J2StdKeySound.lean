module

public import Certificates.Data.Kernel.J2StdOrbK
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests

public section

namespace CFSG.KC.J2StdOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.RankThree.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.RankTwoClassical.J2Std CFSG.KS.Raw.Orb
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)

theorem f9_eq (P i : Nat) : f9 P i = pg 9 (mask 9) P i := rfl

variable {PS PSI LR TR TRI : Nat → Nat} {kS kO BP : Nat} {D : List (List Int)}

theorem lev_prep (hb : Binds 315 9 PS kS 3 BP autStrong autBase)
    (hh : headK 315 9 (mask 9) (315 * 9) (pidn 315 9) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS 3 BP) {i k : Nat} (hi : i < 3) (hk : k < rcnt (LR i)) :
    autLevels[i]!.tr[k]! = unpack 315 9 (trK LR TR i k) ∧
      PRep 315 9 (trK LR TR i k) (permOfArr 315 (unpack 315 9 (trK LR TR i k))) ∧
      PRep 315 9 (trK LR TRI i k) (permOfArr 315 (unpack 315 9 (trK LR TR i k)))⁻¹ := by
  have hp := (Orb.head_facts hh).1
  have hbl := Orb.base_lt_of_levels hb hl
  obtain ⟨-, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  exact ⟨(levelTr_sound hb hh hl hi).2 k hk, (P k hk).1, (P k hk).2⟩

private theorem keyAt_keyPts (y : Array Nat) :
    keyAt keyPts y = y[0]! + 512 * (y[4]! + 512 * (y[3]! + 512 * 0)) := by
  simp only [keyAt, keyPts, List.foldr]

private theorem inv3_apply {α : Type} (A B C : Equiv.Perm α) (q : α) :
    (A * B * C)⁻¹ q = C⁻¹ (B⁻¹ (A⁻¹ q)) := by
  rw [mul_inv_rev, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem keyW1_eq (hb : Binds 315 9 PS kS 3 BP autStrong autBase)
    (hh : headK 315 9 (mask 9) (315 * 9) (pidn 315 9) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS 3 BP)
    (hsz : rcnt (LR 0) = 315 ∧ rcnt (LR 1) = 160 ∧ rcnt (LR 2) = 12)
    {X : Nat} {x : Array Nat} (hx : x = unpack 315 9 X) (hv : validA 315 x = true) {w : Nat}
    (hw : w < 604800) : keyAt keyPts (conjW w x) = keyW1 LR TR TRI X w := by
  obtain ⟨h0, h1, h2⟩ := hsz
  set a := w / 1920
  set b := w / 12 % 160
  set c := w % 12
  obtain ⟨tA, pA, pAI⟩ := lev_prep hb hh hl (i := 0) (k := a) (by norm_num) (by rw [h0]; omega)
  obtain ⟨tB, pB, pBI⟩ := lev_prep hb hh hl (i := 1) (k := b) (by norm_num) (by rw [h1]; omega)
  obtain ⟨tC, pC, pCI⟩ := lev_prep hb hh hl (i := 2) (k := c) (by norm_num) (by rw [h2]; omega)
  set A := permOfArr 315 (unpack 315 9 (trK LR TR 0 a))
  set B := permOfArr 315 (unpack 315 9 (trK LR TR 1 b))
  set C := permOfArr 315 (unpack 315 9 (trK LR TR 2 c))
  have rT : Rep 315 (prod3 315 autLevels a b c) (A * B * C) := by
    intro p
    rw [prod3, getElem!_ofFn_nat _ p.2, tr3, tC, Orb.unpack_get p.2, pC p, tB,
      Orb.unpack_get (C p).2, pB (C p), tA, Orb.unpack_get (B (C p)).2, pA (B (C p)),
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hvT := CFSG.RankThree.Native.F2.validA_of_rep rT
  have rx := rep_of_validA hv
  set g := permOfArr 315 x
  have pX : PRep 315 9 X g := Orb.prep_of_rep (hx ▸ rx)
  have rc : Rep 315 (conjW w x) ((A * B * C) * g * (A * B * C)⁻¹) := by
    have := rep_conjA hvT rx
    rwa [permOfArr_eq_of_rep rT] at this
  have hc : ∀ p (hp : p < 315), (conjW w x)[p]! = cAt (trK LR TR 0 a) (trK LR TR 1 b)
      (trK LR TR 2 c) (trK LR TRI 0 a) (trK LR TRI 1 b) (trK LR TRI 2 c) X p := by
    intro p hp
    rw [rc.apply hp, cAt]
    have hAI : pg 9 (mask 9) (trK LR TRI 0 a) p = (A⁻¹ ⟨p, hp⟩).val := pAI ⟨p, hp⟩
    simp only [f9_eq]
    rw [hAI, pBI, pCI, pX, pC, pB, pA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv3_apply]
  unfold keyW1 keyC key3
  rw [keyAt_keyPts, hc 0 (by norm_num), hc 4 (by norm_num), hc 3 (by norm_num)]
  rfl

theorem conjW_size' (w : Nat) (x : Array Nat) : (conjW w x).size = 315 := by
  simp [conjW, conjA, compA]

private theorem keyAt_keyPts2 (y : Array Nat) :
    keyAt keyPts2 y = y[0]! + 512 * (y[4]! + 512 * (y[3]! + 512 * (y[315]! + 512 * (y[319]! +
      512 * (y[318]! + 512 * 0))))) := by
  simp only [keyAt, keyPts2, List.foldr]

private theorem key2_arith (a b c d e f : Nat) :
    a + 512 * (b + 512 * (c + 512 * (d + 512 * (e + 512 * (f + 512 * 0))))) =
      (a + 512 * (b + 512 * (c + 512 * 0))).add
        (Nat.mul 134217728 (d + 512 * (e + 512 * (f + 512 * 0)))) := by
  change _ = Nat.add _ (Nat.mul 134217728 _)
  simp only [Nat.add_eq, Nat.mul_eq]
  ring

theorem keyW2_eq (hb : Binds 315 9 PS kS 3 BP autStrong autBase)
    (hh : headK 315 9 (mask 9) (315 * 9) (pidn 315 9) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS 3 BP)
    (hsz : rcnt (LR 0) = 315 ∧ rcnt (LR 1) = 160 ∧ rcnt (LR 2) = 12)
    {X Y : Nat} {x y : Array Nat} (hx : x = unpack 315 9 X) (hvx : validA 315 x = true)
    (hy : y = unpack 315 9 Y) (hvy : validA 315 y = true) {w : Nat} (hw : w < 604800) :
    keyAt keyPts2 (conjW w x ++ conjW w y) = keyW2 LR TR TRI X Y w := by
  have e1 := keyW1_eq hb hh hl hsz hx hvx hw
  have e2 := keyW1_eq hb hh hl hsz hy hvy hw
  have hs := conjW_size' w x
  have get2 : ∀ i < 315, (conjW w x ++ conjW w y)[315 + i]! = (conjW w y)[i]! := by
    intro i hi
    rw [getElem!_pos _ _ (by simp [hs, conjW_size']; omega),
      getElem!_pos _ _ (by rw [conjW_size']; exact hi), Array.getElem_append_right (by omega)]
    simp [hs]
  have get1 : ∀ i < 315, (conjW w x ++ conjW w y)[i]! = (conjW w x)[i]! := by
    intro i hi
    rw [getElem!_pos _ _ (by simp [hs, conjW_size']; omega), getElem!_pos _ _ (by rw [hs]; exact hi),
      Array.getElem_append_left]
  rw [keyAt_keyPts] at e1 e2
  rw [keyAt_keyPts2, get1 0 (by norm_num), get1 4 (by norm_num), get1 3 (by norm_num),
    get2 0 (by norm_num), get2 4 (by norm_num), get2 3 (by norm_num)]
  unfold keyW2
  rw [← e1, ← e2]
  exact key2_arith _ _ _ _ _ _

end CFSG.KC.J2StdOrb

end
