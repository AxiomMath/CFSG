module

public import CFSG.Certificates.Kernel.ThDemp.OrbUnfoldBase

public import CFSG.Certificates.Kernel.ThDemp.Action
public import CFSG.Certificates.Kernel.ThDemp.Batches
public import CFSG.Certificates.Kernel.ThDemp.Sound
public import Mathlib.Algebra.BigOperators.Intervals

public section

namespace CFSG.Certificates.ThDemp.Unfold

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes

variable {D : DempData} {O : OrbData}

theorem invChk_sound (h : invChk D O = true) :
    ∀ l < 3, ∀ i < D.oszL l, i < 64 → D.mul (D.T l i) (O.TI l i) = D.ONE := by
  have key : ∀ n, Nat.rec (motive := fun _ => Bool) true
      (fun l ih => andB (allBelow (D.oszL l) 1 (fun i =>
        Nat.beq (D.mul (D.T l i) (O.TI l i)) D.ONE)) ih) n = true →
      ∀ l < n, ∀ i < D.oszL l, i < 64 → D.mul (D.T l i) (O.TI l i) = D.ONE := by
    intro n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl i hi hi64
      obtain ⟨h1, h2⟩ := andB_split hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl i hi hi64
      · exact Nat.eq_of_beq_eq_true (allBelow_spec' h1 i hi (by omega))
  exact key 3 h


variable (hF : DempFacts D)
include hF

theorem pkMat_stepY (l y : ℕ) (hl : l < 6) : pkMat (D.stepY l y D.ONE) = pkMat (D.T l y) := by
  have hk := hF.consts
  unfold DempData.stepY
  cases hb : Nat.beq y 0
  · change pkMat (D.mul (D.T l y) D.ONE) = _
    rw [DempData.mul, pkMat_mulB hk, pkMat_one hk, Matrix.mul_one]
  · have hy : y = 0 := Nat.eq_of_beq_eq_true hb
    subst hy
    change pkMat D.ONE = _
    rw [T_of_zero (hF.tr0 l (by rw [hF.L6]; exact hl))]

theorem c_eq : D.c = rep 1 256 248 := (consts_spec hF.consts).1

theorem rm_eq : D.rm = 2 ^ 248 - 1 := (consts_spec hF.consts).2.1

theorem pkMat_chainEl (e : ℕ) :
    pkMat (chainEl D e) = pkMat (D.T 5 (bitsN e 40 8)) * pkMat (D.T 4 (bitsN e 32 8)) *
      pkMat (D.T 3 (bitsN e 24 8)) * pkMat (D.T 2 (bitsN e 16 8)) * pkMat (D.T 1 (bitsN e 8 8)) *
      pkMat (D.T 0 (bitsN e 0 8)) := by
  have hk := hF.consts
  have e1 : chainEl D e = D.mul (D.mul (D.mul (D.mul (D.mul (D.mul D.ONE
      (D.stepY 5 (bitsN e 40 8) D.ONE)) (D.stepY 4 (bitsN e 32 8) D.ONE))
      (D.stepY 3 (bitsN e 24 8) D.ONE)) (D.stepY 2 (bitsN e 16 8) D.ONE))
      (D.stepY 1 (bitsN e 8 8) D.ONE)) (D.stepY 0 (bitsN e 0 8) D.ONE) := by
    unfold chainEl
    simp only [strictN_eq]
  rw [e1]
  simp only [DempData.mul, pkMat_mulB hk, pkMat_one hk, Matrix.one_mul]
  rw [pkMat_stepY hF 5 _ (by omega), pkMat_stepY hF 4 _ (by omega), pkMat_stepY hF 3 _ (by omega),
    pkMat_stepY hF 2 _ (by omega), pkMat_stepY hF 1 _ (by omega), pkMat_stepY hF 0 _ (by omega)]

theorem sp_wordR : ∀ (w : List ℕ) (X : ℕ),
    sp (wordR D (cR 5) X w) = mapM ((w.map fun r => pkMat (D.RB r)).prod) (sp X)
  | [], X => by
    change sp X = mapM 1 (sp X)
    rw [mapM_one]
  | r :: w, X => by
    have e : wordR D (cR 5) X (r :: w) = wordR D (cR 5) (mulB (cR 5) D.rm X (D.RB r)) w := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e, sp_wordR w, rm_eq hF, cR, sp_mulB, List.map_cons, List.prod_cons, mapM_mul]

theorem lil_wordR : ∀ (w : List ℕ) (X : ℕ), (∀ r ∈ w, ∃ M', pkMat (D.RB r) * M' = 1) →
    Key.LIL (rowsOf (2 ^ 248 - 1) X) → Key.LIL (rowsOf (2 ^ 248 - 1) (wordR D (cR 5) X w))
  | [], X, _, hX => hX
  | r :: w, X, hw, hX => by
    have e : wordR D (cR 5) X (r :: w) = wordR D (cR 5) (mulB (cR 5) D.rm X (D.RB r)) w := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e]
    refine lil_wordR w _ (fun r' hr' => hw r' (by simp [hr'])) ?_
    obtain ⟨M', hM'⟩ := hw r (by simp)
    rw [rm_eq hF, cR]
    exact lil_mulB hM' hX

end CFSG.Certificates.ThDemp.Unfold

end
