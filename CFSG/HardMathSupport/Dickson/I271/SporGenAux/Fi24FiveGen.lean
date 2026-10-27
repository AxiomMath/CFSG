module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenKit
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi24FiveGenData
public import Certificates.Certificate17255

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.F3.Native CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem canonRows_powW {M : Array W} (hM : canonRows 781 M = true) (e : ℕ) :
    canonRows 781 (powW 781 M e) = true := by
  induction e with
  | zero => exact canonRows_idW
  | succ e ih =>
    rw [Native.powW]
    exact canonRows_mulW ih hM

theorem canonRows_seeds :
    canonRows 781 (matA ()) = true ∧ canonRows 781 (matB ()) = true :=
  ⟨canonRows_of matA_size rowsWF_matA (zeroFrom_rowsOfSeed 781 le_rfl _),
    canonRows_of matB_size rowsWF_matB (zeroFrom_rowsOfSeed 781 le_rfl _)⟩

@[expose] def Fi24Sim (X : Array W) (g : J) : Prop :=
  canonRows 781 X = true ∧ matW 781 781 X = mat g


theorem fi24Sim_one : Fi24Sim fi24Ops.one 1 := by
  dsimp only [fi24Ops]
  exact ⟨canonRows_idW, by rw [matW_idW (by norm_num), mat_one]⟩

theorem fi24Sim_mul {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h) :
    Fi24Sim (fi24Ops.mul X Y) (g * h) := by
  dsimp only [fi24Ops]
  have hXw := RowsWF.of_canonRows hX.1
  have hYw := RowsWF.of_canonRows hY.1
  have hYs : Y.size ≤ 781 := (canonRows_spec hY.1).1.le
  exact ⟨canonRows_mulW hX.1 hY.1, by
    rw [matW_mulW (m := 781) (by norm_num) hXw hYw hYs, hX.2, hY.2, mat_mul]⟩

theorem fi24Sim_pow {X : Array W} {g : J} (e : ℕ) (hX : Fi24Sim X g) :
    Fi24Sim (fi24Ops.pow X e) (g ^ e) := by
  dsimp only [fi24Ops]
  have hXw := RowsWF.of_canonRows hX.1
  have hXs : X.size ≤ 781 := (canonRows_spec hX.1).1.le
  exact ⟨canonRows_powW hX.1 e, by rw [matW_powW (by norm_num) hXw hXs e, hX.2, mat_pow]⟩

theorem fi24Sim_eq {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h)
    (hXY : fi24Ops.eqb X Y = true) : g = h := by
  dsimp only [fi24Ops] at hXY
  apply mat_injective
  rw [← hX.2, ← hY.2, (eq_of_eqRows hXY).2]

theorem fi24Sim_ne {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h)
    (hXY : fi24Ops.neb X Y = true) : g ≠ h := by
  dsimp only [fi24Ops] at hXY
  intro hgh
  have hXY' : X = Y := eq_of_matW_eq hX.1 hY.1 (by rw [hX.2, hY.2, hgh])
  have hs : X.size = 781 := (canonRows_spec hX.1).1
  have : eqRows 781 X Y = true := by
    unfold eqRows
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hs, hXY'⟩
  rw [this] at hXY
  exact Bool.false_ne_true hXY

theorem fi24Sim_a : Fi24Sim (matA ()) a :=
  ⟨canonRows_seeds.1, by rw [matW_matA, mat_a]⟩

theorem fi24Sim_b : Fi24Sim (matB ()) b :=
  ⟨canonRows_seeds.2, by rw [matW_matB, mat_b]⟩

theorem fi24J_card_five : (Nat.card J).factorization 5 = 2 :=
  factorization_sq_of_eq Nat.prime_five
    (by rw [card_J]; norm_num : Nat.card J = 5 ^ 2 * 50208228367626468851712) (by norm_num)

noncomputable def fi24EquivCarrier : NativeSporadic.Carrier .Fi24Prime ≃* J := fi24EquivJ


theorem centGen_fi24J_five : CentGen 5 J :=
  Certificates.certificate17255

theorem sporPair_Fi24Prime_five
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) : SporPair .Fi24Prime 5 := by
  have h1 := sporPair_five_of_model (name := .Fi24Prime) (M := J) hSpM hOut hBr
  have h2 := h1 fi24EquivCarrier
  have h3 := h2 fi24J_card_five
  exact h3 centGen_fi24J_five

end CFSG.HardMathSupport.Dickson.I271
