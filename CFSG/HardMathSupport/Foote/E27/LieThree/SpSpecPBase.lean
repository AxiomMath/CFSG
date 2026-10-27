
module

public import CFSG.HardMathSupport.Foote.E27.LieThree.SpModelP
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

@[expose] public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native TauCeti

theorem JFin_finSum' {p : ℕ} (r : ℕ) (x y : Fin r ⊕ Fin r) :
    JFin r (ZMod p) (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.J (Fin r) (ZMod p) x y := by
  have := congrFun (congrFun (JFin_submatrix r (R := ZMod p)) x) y
  simpa using this

theorem JFin_apply_p (p r : ℕ) (i j : Fin (r + r)) :
    JFin r (ZMod p) i j =
      if i.val + r = j.val then -1 else if j.val + r = i.val then 1 else 0 := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [JFin_finSum']
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.J,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply,
      Fin.coe_castAdd, Fin.coe_natAdd]
  · have hc1 : ¬ (a.val + r = b.val) := by
      have := a.isLt
      have := b.isLt
      omega
    have hc2 : ¬ (b.val + r = a.val) := by
      have := a.isLt
      have := b.isLt
      omega
    simp [hc1, hc2]
  · by_cases hab : a = b
    · subst hab
      have e : a.val + r = r + a.val := Nat.add_comm _ _
      simp [e]
    · have h1 : ¬ (a.val + r = r + b.val) := by
        have : a.val ≠ b.val := fun e => hab (Fin.ext e)
        omega
      have h2 : ¬ (r + b.val + r = a.val) := by
        have := a.isLt
        omega
      simp [hab, h1, h2]
  · by_cases hab : a = b
    · subst hab
      have h1 : ¬ (r + a.val + r = a.val) := by omega
      have e : a.val + r = r + a.val := Nat.add_comm _ _
      simp [h1, e]
    · have h1 : ¬ (r + a.val + r = b.val) := by
        have := b.isLt
        omega
      have h2 : ¬ (b.val + r = r + a.val) := by
        have : a.val ≠ b.val := fun e => hab (Fin.ext e)
        omega
      simp [hab, h1, h2]
  · have hc1 : ¬ (r + a.val + r = r + b.val) := by
      have := a.isLt
      have := b.isLt
      omega
    have hc2 : ¬ (r + b.val + r = r + a.val) := by
      have := a.isLt
      have := b.isLt
      omega
    simp [hc1, hc2]

theorem jAMp_spec (p r : ℕ) [NeZero p] : toMat p (r + r) (jAMp p r) = JFin r (ZMod p) := by
  ext i j
  rw [toMat_apply, JFin_apply_p]
  unfold jAMp
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (NeZero.ne p)
  split_ifs
  · rw [Nat.cast_sub hp1, ZMod.natCast_self, zero_sub, Nat.cast_one]
  · simp
  · simp

theorem symplAP_spec {p r : ℕ} [NeZero p] {X : AM} (h : symplAP p r X = true) :
    ∃ x : SpJP p r, matJP p r x = toMat p (r + r) X := by
  apply exists_of_symplP
  unfold symplAP at h
  have := matEqB_true h
  rwa [toMat_mulM, toMat_mulM, toMat_trA', jAMp_spec] at this

theorem card_spJP_three : Nat.card (SpJP 3 3) = 3 ^ 9 * 465920 := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.symplectic_higher_order_and_Sylow
    (K := ZMod 3) 3 3 (Nat.card_zmod 3) (r := 3) (by norm_num)).1
  rw [Nat.card_congr (CFSG.LieType.Universal.Symplectic.equivStatedSp 3 (ZMod 3)).toEquiv, h]
  decide

section Certificates

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

end Certificates

end CFSG.HardMathSupport.Foote.E27
