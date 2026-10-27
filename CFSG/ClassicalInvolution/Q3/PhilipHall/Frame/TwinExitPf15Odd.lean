module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14

open scoped MatrixGroups

namespace TwinDisc

theorem not_isPGroup_two_sl2_three : ¬ IsPGroup 2 SL(2, ZMod 3) := by
  intro h
  obtain ⟨x, hx, hne⟩ : ∃ x : SL(2, ZMod 3), x ^ 3 = 1 ∧ x ≠ 1 := by
    refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> decide
    · intro e
      have := congrArg (fun g : SL(2, ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1) e
      simp at this
  have h3 : orderOf x = 3 := orderOf_eq_prime hx hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h x
  rw [h3] at hk
  have h32 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
  omega

section Sec

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem q8Section_tight (hS : Q8Section X Φ) : ∀ K ∈ Φ, tightCore K = K := by
  intro K hK
  rcases hS.hyp.omega2 K hK with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd ((hS.two K hK).of_equiv e) not_isPGroup_two_sl2_three

theorem twinE4_of_exitSec_sec (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hno : ¬ TightInO2 z) {W : Subgroup X} (hKW : K ≤ W)
    (hWs : IsSubnormal W ⊤) (hex : Thm4Twin.F2.ExitSec W K hKW z hz) : TwinE4 X := by
  have hWtop : W = ⊤ := ExitE4.eq_top_of_subnormal hS.gen htrans hK hWs rfl hKW
  have hΦ : Φ = CoreAssembly.conjClass K := by
    ext L
    constructor
    · intro hL
      exact htrans K hK L hL
    · rintro ⟨g, rfl⟩
      exact hS.hyp.conjInvariant g K hK
  have key : TwinE4 ↥(⊤ : Subgroup X) → TwinE4 X := fun h => ExitE4.twinE4_of_top h
  rcases hex with hE | ⟨S, hnoW, htx⟩
  · exact key (hWtop ▸ hE)
  · have hedge' : ¬ TightEdgeless (K.subgroupOf W) := by
      subst hWtop
      exact not_tightEdgeless_top hS.hyp hΦ (q8Section_tight hS K hK) hedge
    rcases htx with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hnoW
    · exact absurd h hedge'
    · exact absurd h hedge'
    · exact key (hWtop ▸ TightE4.twinE4 h)

theorem oddCent_dichotomy_sec (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) :
    (∃ P : Subgroup X, P.Normal ∧ IsPGroup 2 P ∧ ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u → u ∈ P) ∨
      (∀ w : X, w * w = 1 → oddCoreIn (Subgroup.centralizer ({w} : Set X)) = ⊥) := by
  have htight := q8Section_tight hS
  by_cases hO2 : ∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z
  · obtain ⟨K', hK', z', hz', P, hPn, hP2, hz'P⟩ := hO2
    refine Or.inl ⟨P, hPn, hP2, ?_⟩
    intro L hL u hu
    obtain ⟨g, hg⟩ := htrans K' hK' L hL
    have h1 : IsUniqueInvolution (conjSub g K') (g * z' * g⁻¹) := hz'.conj g
    rw [hg] at h1
    rw [← h1.eq hu]
    exact hPn.conj_mem z' hz'P g
  · push Not at hO2
    refine Or.inr ?_
    by_cases hEx : ∃ K' ∈ Φ, ∃ (z' : X) (hz' : IsUniqueInvolution K' z') (W : Subgroup X)
        (hKW : K' ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : X) K') = W ∧
          Thm4Twin.F2.ExitSec W K' hKW z' hz'
    · obtain ⟨K', hK', z', hz', W, hKW, hWs, -, hexit⟩ := hEx
      have hE4 := twinE4_of_exitSec_sec hS htrans hedge hK' hz' (hO2 K' hK' z' hz') hKW hWs hexit
      intro w hw
      exact oddCent_bot_of_twinE4 hSp hD4 hS.oddFree hE4 hw
    · push Not at hEx
      have hno : TwinExitPf11.NoExitRest X Φ := fun K' hK' z' hz' =>
        ⟨hO2 K' hK' z' hz', fun W hKW hWs hWg => hEx K' hK' z' hz' W hKW hWs hWg⟩
      have hl := TwinExitPf11.hasLifts_of_noExitRest hP hlt hS htight hno
      obtain ⟨M, hM, -⟩ := hedge
      intro w hw
      exact TwinExitPf10.oddCent_bot_of_hasLifts hcit hS.hyp hlt hS.oddFree hS.gen hl ⟨M, hM⟩ w hw

end Sec

theorem oddCentEdge_proved (n : ℕ) : OddCentEdge n := by
  intro hcit hP X _ _ hlt Φ hS htrans hedge K hK z hz
  rcases oddCent_dichotomy_sec TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert hcit hP hlt
      hS htrans hedge with ⟨P, hPn, hP2, hmem⟩ | hall
  · exact oddCoreIn_centralizer_eq_bot_of_mem_normal hS.oddFree hPn hP2 (hmem K hK z hz)
  · exact hall z hz.sq

theorem nonTightTwin_proved (n : ℕ) : NonTightTwin n :=
  fun X _ _ _ Φ hS hnt => absurd (q8Section_tight
    ⟨hS.hyp, hS.two, hS.q8, hS.oddFree, hS.aEmpty, hS.gen⟩) hnt

theorem nonExactTwin_proved {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    NonExactTwin n :=
  nonExactTwin_of_nonTight_proved hcit hP (nonTightTwin_proved n)

theorem dstarExitQ8_proved {n : ℕ} (hmodel : ExitE4.E4ModelDStar) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) : DStarExitQ8 n :=
  dstarExitQ8_of_exactness hmodel hcit hP (nonExactTwin_proved hcit hP)

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
