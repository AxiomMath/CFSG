module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LowerClass

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Cit3

@[expose] def LowerTwinR (r n : ℕ) : Prop :=
  (5 ≤ r → Thm1RTwinBelowR (r - 1) n) ∧ (r = 4 → TL4.TightBelowRPlus 3 n)

theorem LowerTwinR.mono {r m n : ℕ} (h : m ≤ n) (H : LowerTwinR r n) : LowerTwinR r m :=
  ⟨fun hr => (H.1 hr).mono h, fun hr => (H.2 hr).mono h⟩

theorem thm1RTwinBelowR_of_casesL {r : ℕ} (hr : 3 ≤ r) (hA : ∀ n, TwinCoreConnR r n)
    (hB : ∀ n, TwinCoreDiscPerpR r n) (hC : ∀ n, LowerTwinR r n → TwinCorePerpR r n) :
    ∀ n, CIT3Below n → TightBelowR r n → LowerTwinR r n → Thm1RTwinBelowR r n := by
  intro n
  induction n with
  | zero => exact fun _ _ _ => thm1RTwinBelowR_zero r
  | succ n ih =>
    intro hBelow hT hL
    have hBelow' : CIT3Below n := cit3Below_mono (Nat.le_succ n) hBelow
    have hT' : TightBelowR r n := TL4.Induct.tightBelowR_mono (Nat.le_succ n) hT
    have hL' : LowerTwinR r n := hL.mono (Nat.le_succ n)
    have hTw := ih hBelow' hT' hL'
    exact thm1RTwinBelowR_succ hr hTw
      (thm1RTwinCoreAtR_of_cases (hA n) (hB n) (hC n hL') hBelow' hT' hTw)

theorem thm1RTwinBelowR_tower (hA : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreConnR r n)
    (hB : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreDiscPerpR r n)
    (hC : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerTwinR r n → TwinCorePerpR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, CIT3Below n → TightBelowR r n → LowerClassR r n →
      Thm1RTwinBelowR r n := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro n hA' hT hL
    exact thm1RTwinBelowR_of_casesL (by norm_num) (hA 4 le_rfl) (hB 4 le_rfl) (hC 4 le_rfl) n hA'
      hT ⟨fun h => absurd h (by norm_num), fun _ => hL.2⟩
  | succ r hr ih =>
    intro n hA' hT hL
    have hTr : TightBelowR r n := hL.1 r hr (Nat.lt_succ_self r)
    have hLr : LowerClassR r n := ⟨fun r' h1 h2 => hL.1 r' h1 (Nat.lt_succ_of_lt h2), hL.2⟩
    have hTw : Thm1RTwinBelowR r n := ih n hA' hTr hLr
    have hTw' : Thm1RTwinBelowR (r + 1 - 1) n := by rwa [Nat.add_sub_cancel]
    exact thm1RTwinBelowR_of_casesL (by omega) (hA (r + 1) (by omega)) (hB (r + 1) (by omega))
      (hC (r + 1) (by omega)) n hA' hT ⟨fun _ => hTw', fun h => absurd h (by omega)⟩

theorem r4CentTwin_of_casesL (hA : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreConnR r n)
    (hB : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreDiscPerpR r n)
    (hC : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerTwinR r n → TwinCorePerpR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, LowerClassR r n → TightCentTwinLiftR r n :=
  fun r hr n hL hA' hb =>
    tightCentTwinLiftR_at (thm1RTwinBelowR_tower hA hB hC r hr n hA' hb hL) hA' hb

theorem r4TwistAllTwin_of_casesL (hA : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreConnR r n)
    (hB : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreDiscPerpR r n)
    (hC : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerTwinR r n → TwinCorePerpR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, LowerClassR r n → TightTwistAllTwinR r n :=
  fun r hr n hL hA' hb =>
    tightTwistAllTwinR_at (thm1RTwinBelowR_tower hA hB hC r hr n hA' hb hL) hA' hb

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
