module

public import Certificates.Data.Kernel.G2Three.Y2LNG
public import CFSG.Certificates.Kernel.G2Three.Tables

public section

namespace CFSG.KC.G2Three

open CFSG.KD.G2Three CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec2

variable (hc : consts3OK 14 5 196 LO RM CI ONE UP = true) {G : ℕ → ℕ}
  (hG : ∀ s < 4, canon14 ([x0c, x1c, y0c, y1c].getD s one14) = true ∧
    pk ([x0c, x1c, y0c, y1c].getD s one14) = G s)
  (hone : pk one14 = ONE)

include hG hone in
theorem ngGen_data (i : ℕ) : canon14 (y2l_ngGen i) = true ∧ pk (y2l_ngGen i) = ngGenK G i := by
  rw [y2l_ngGen, ngGenK]
  by_cases hi : i < 4
  · rw [Nat.blt_eq.mpr hi, cond_true]
    exact hG i hi
  · have e : Nat.blt i 4 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hi (Nat.blt_eq.mp h)
    rw [e, cond_false, List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨canon14_one14, hone⟩

include hc hG hone in
theorem ngFoldl_data : ∀ (w c : List ℕ) (C : ℕ), canon14 c = true ∧ pk c = C →
    canon14 (w.foldl (fun acc i => mul14 acc (y2l_ngGen i)) c) = true ∧
      pk (w.foldl (fun acc i => mul14 acc (y2l_ngGen i)) c) =
        w.foldl (fun acc i => MUL acc (ngGenK G i)) C
  | [], _, _, h => h
  | i :: w, _, _, h => ngFoldl_data w _ _ (mulE hc h (ngGen_data hG hone i))

include hc hG hone in
theorem ngWord_beq (w : List ℕ) : (y2l_ngWord w == one14) = Nat.beq (ngWordK G w) ONE := by
  obtain ⟨hcw, hpw⟩ := ngFoldl_data hc hG hone w one14 ONE ⟨canon14_one14, hone⟩
  rw [y2l_ngWord, ngWordK]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    rw [← hpw, h, hone]
  · intro h
    exact pk_inj hcw canon14_one14 (hpw.trans (h.trans hone.symm))

include hc hG hone in
theorem ngCheck_eq : y2l_ngCheck () = ngCheckK G := by
  simp only [y2l_ngCheck, ngCheckK, bne, ngWord_beq hc hG hone]

end CFSG.KC.G2Three

end
