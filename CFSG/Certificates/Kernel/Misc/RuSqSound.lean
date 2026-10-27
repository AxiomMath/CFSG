module

public import Certificates.Data.Kernel.Misc.RuSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SquaresInputs
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.RuSq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu

private theorem sqFix_of {T0 T1 x : Nat} {σ0 σ1 : Equiv.Perm (Fin 4060)}
    (h0 : CFSG.KS.Raw.Orb.PRep 4060 12 T0 σ0) (h1 : CFSG.KS.Raw.Orb.PRep 4060 12 T1 σ1)
    (hx : x < 4060)
    (he : pg 12 (mask 12) T0 (pg 12 (mask 12) T1 (pg 12 (mask 12) T0 (pg 12 (mask 12) T1 x))) =
      x) :
    ∃ y : Fin 4060, (σ0 * σ1 * (σ0 * σ1)) y = y := by
  refine ⟨⟨x, hx⟩, Fin.ext ?_⟩
  have e1 : pg 12 (mask 12) T1 x = σ1 ⟨x, hx⟩ := h1 ⟨x, hx⟩
  rw [e1, h0 (σ1 ⟨x, hx⟩), h1 (σ0 (σ1 ⟨x, hx⟩)), h0 (σ1 (σ0 (σ1 ⟨x, hx⟩)))] at he
  simpa [Equiv.Perm.mul_apply] using he

theorem fix2K_sound {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {H : Nat} (hb : Binds 4060 12 PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP)
    (h : fix2K 4060 12 (mask 12) (4060 * 12) LR TR H = true) :
    all2 4060 (rawLevels 4060 S base) ruSquareTest = true := by
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨A0, P0⟩ := CFSG.KS.Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) (i := 0)
    (by norm_num) (hl 0 (by norm_num))
  obtain ⟨A1, P1⟩ := CFSG.KS.Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) (i := 1)
    (by norm_num) (hl 1 (by norm_num))
  have e0 : (rawLevels 4060 S base)[0]! = CFSG.Certificates.ChainArrays.lev 4060 S base 0 := rfl
  have e1 : (rawLevels 4060 S base)[1]! = CFSG.Certificates.ChainArrays.lev 4060 S base 1 := rfl
  unfold fix2K at h
  simp only [CFSG.KS.PackFld.strictB_eqP] at h
  unfold all2
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro a ha
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro b hb'
  have hcnt0 : a < (CFSG.Certificates.ChainArrays.lev 4060 S base 0).pts.size := by
    rw [← e0]
    exact ha
  have hcnt1 : b < (CFSG.Certificates.ChainArrays.lev 4060 S base 1).pts.size := by
    rw [← e1]
    exact hb'
  have ha' : a < rcnt (LR 0) := by
    rw [A0.cnt]
    exact hcnt0
  have hb'' : b < rcnt (LR 1) := by
    rw [A1.cnt]
    exact hcnt1
  have hab := CFSG.KS.allN_spec (CFSG.KS.allN_spec h a ha') b hb''
  simp only [sqFixK, CFSG.KS.PackFld.strictB_eqP, CFSG.KS.bAnd_iff, Nat.blt_eq,
    Nat.beq_eq] at hab
  obtain ⟨y, hy⟩ := sqFix_of (P0 a ha').1 (P1 b hb'').1 hab.1 hab.2
  have hR : CFSG.Monster.B.Co2.Rep 4060 (prod2A 4060 (rawLevels 4060 S base) a b) (_ * _) :=
    CFSG.Monster.B.Co2.rep_compA (A0.tr a hcnt0).1 (A1.tr b hcnt1).1
  have hR2 := CFSG.Monster.B.Co2.rep_compA hR hR
  have hpos : 0 < ruFixCount (CFSG.Monster.B.Co2.Native.compA 4060
      (prod2A 4060 (rawLevels 4060 S base) a b) (prod2A 4060 (rawLevels 4060 S base) a b)) := by
    unfold ruFixCount CFSG.Certificates.Native.fixedList
    refine List.length_pos_of_mem (a := (y : ℕ)) ?_
    simp only [List.mem_filter, List.mem_range]
    refine ⟨y.isLt, ?_⟩
    rw [hR2 y, hy, beq_self_eq_true]
  unfold ruSquareTest
  rw [Bool.or_eq_true]
  exact Or.inr (decide_eq_true hpos)

end CFSG.KC.Misc.RuSq

end
