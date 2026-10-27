module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11Lifts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Ae5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitTight
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf8Exit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12

namespace TwinDisc

section Sec

@[expose] def NoExitSec (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  ∀ K ∈ Φ, ∀ (z : X) (hz : IsUniqueInvolution K z),
    ∀ (W : Subgroup X) (hKW : K ≤ W), IsSubnormal W ⊤ → (⨆ x : W, conjSub (x : X) K) = W →
      ¬ Thm4Twin.F2.ExitSec W K hKW z hz

theorem oddCent_bot_of_noExitSec {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (htight : ∀ K ∈ Φ, tightCore K = K) (hno : NoExitSec X Φ) :
    ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  intro K hK z hz
  by_cases hO2 : ∃ K' ∈ Φ, ∃ z' : X, IsUniqueInvolution K' z' ∧ TightInO2 z'
  · obtain ⟨K', hK', z', hz', P, hPn, hP2, hz'P⟩ := hO2
    obtain ⟨g, hg⟩ := htrans K' hK' K hK
    have hz'' : IsUniqueInvolution (conjSub g K') (g * z' * g⁻¹) := hz'.conj g
    rw [hg] at hz''
    have hzeq : g * z' * g⁻¹ = z := hz''.eq hz
    have hzP : z ∈ P := by rw [← hzeq]; exact hPn.conj_mem z' hz'P g
    exact oddCoreIn_centralizer_eq_bot_of_mem_normal hS.oddFree hPn hP2 hzP
  · push Not at hO2
    have hr : NoExitRest X Φ := fun K hK z hz => ⟨hO2 K hK z hz, hno K hK z hz⟩
    exact (noExit_of_noExitRest hcit hP hlt hS htight hr K hK z hz).1

end Sec

section Exact

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem q8TwinSection_q8_of_exact (hS : Q8TwinSection X Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) :
    ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2) := fun J hJ =>
  hS.q8 J hJ J ⟨le_rfl, h2 J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩

theorem dstarConnected_of_o2_exact {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8TwinSection X Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hO2 : TightInO2 z) : T3.DStarConnected Φ := by
  have hq8 := q8TwinSection_q8_of_exact hS h2
  have F : ExitO2.Q8Fam X Φ :=
    { hyp := hS.hyp
      two := h2
      q8 := hq8
      aEmpty := hS.aEmpty
      gen := by
        have := hS.gen
        unfold omegaGen at this
        exact this
      trans := hS.trans
      oddFree := hS.oddFree
      inO2 := by
        intro L hL u hu
        obtain ⟨g, rfl⟩ := hS.trans K hK L hL
        obtain ⟨P, hPn, hP2, hzP⟩ := hO2
        refine ⟨P, hPn, hP2, ?_⟩
        have hgu : g * z * g⁻¹ = u := (hz.conj g).eq hu
        rw [← hgu]
        exact hPn.conj_mem z hzP g }
  obtain ⟨K₀, hK₀, K', ⟨hK', -⟩, hne, -⟩ := hS.triple
  have htt := hS.triple
  rcases F.thmDConcl hD hlt with h1 | ⟨W, hW⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm, ⟨I⟩⟩ | I29
  · exact absurd (h1 K' hK' K₀ hK₀) hne
  · exact ExitO2.fam_dstarConnected_of_wSet F hW
  · exact ExitO2.fam_dstarConnected_of_e8 F hE
  · obtain ⟨I⟩ := I64
    exact ExitO2.fam_dstarConnected_of_e64 F I
  · rcases Nat.lt_or_ge m 6 with h6 | h6
    · obtain rfl : m = 5 := by omega
      exact (ExitO2.fam_false_of_ae5 F I htt).elim
    · exact ExitO2.fam_dstarConnected_of_aeIdent F h6 I
  · obtain ⟨I⟩ := I29
    exact ExitO2.fam_dstarConnected_of_e29 F I

theorem dstarConnected_of_exitSec_exact (hmodel : ExitE4.E4ModelDStar) (hS : Q8TwinSection X Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hno : ¬ TightInO2 z) {W : Subgroup X} (hKW : K ≤ W)
    (hWs : IsSubnormal W ⊤) (hex : Thm4Twin.F2.ExitSec W K hKW z hz) : T3.DStarConnected Φ := by
  have hq8 := q8TwinSection_q8_of_exact hS h2
  rcases hex with hE | ⟨S, hnoW, hex⟩
  · exact ExitE4.dstarConnected_of_twinE4 hmodel hS.hyp h2 hq8 hS.gen hS.trans hK hz hno hKW hWs hE
  · have hWtop : W = ⊤ := ExitE4.eq_top_of_subnormal hS.gen hS.trans hK hWs rfl hKW
    have hΦ : Φ = CoreAssembly.conjClass K := by
      ext J
      constructor
      · intro hJ
        exact hS.trans K hK J hJ
      · rintro ⟨g, rfl⟩
        exact hS.hyp.conjInvariant g K hK
    have hedge : ¬ TightEdgeless (K.subgroupOf W) := by
      subst hWtop
      obtain ⟨K₀, hK₀, -, -, -, J, hJ, -⟩ := hS.triple
      have h2R : IsPGroup 2 ↥(K.subgroupOf (⊤ : Subgroup X)) := (h2 K hK).comap_subtype
      unfold TightEdgeless
      rw [tightCore_eq_self_of_isPGroup h2R]
      exact ExitE4.not_dEdgeless_top (h2 K hK) hΦ hK₀ hJ
    rcases hex with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hnoW
    · exact absurd h hedge
    · exact absurd h hedge
    · exact ExitE4.dstarConnected_of_twinE4 hmodel hS.hyp h2 hq8 hS.gen hS.trans hK hz hno hKW hWs
        (TightE4.twinE4 h)

end Exact

@[expose] def TwoConstrained (X : Type) [Group X] : Prop :=
  ∃ P : Subgroup X, P.Normal ∧ IsPGroup 2 P ∧ Subgroup.centralizer (P : Set X) ≤ P

@[expose] def NonExactTwin (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), Q8TwinSection X Φ →
    ¬ (∀ J ∈ Φ, IsPGroup 2 J) → ¬ TwoConstrained X →
      ¬ ((∀ K ∈ Φ, tightCore K = K) ∧ NoExitSec X Φ) → T3.DStarConnected Φ

theorem dstarExitQ8_of_exactness {n : ℕ} (hmodel : ExitE4.E4ModelDStar) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hN : NonExactTwin n) : DStarExitQ8 n := by
  intro X _ _ hlt Φ hΩ h2' hq hO hA hgen htrans htt hex
  have hS : Q8TwinSection X Φ := ⟨hΩ, h2', hq, hO, hA, hgen, htrans, htt⟩
  have hS' : Q8Section X Φ := ⟨hS.hyp, hS.two, hS.q8, hS.oddFree, hS.aEmpty, hS.gen⟩
  obtain ⟨K, hK, z, hz, hcase⟩ := hex
  by_cases hex2 : ∀ J ∈ Φ, IsPGroup 2 J
  · have htight : ∀ J ∈ Φ, tightCore J = J := fun J hJ => tightCore_eq_self_of_isPGroup (hex2 J hJ)
    by_cases hO2 : ∃ K' ∈ Φ, ∃ z' : X, IsUniqueInvolution K' z' ∧ TightInO2 z'
    · obtain ⟨K', hK', z', hz', hO2'⟩ := hO2
      exact dstarConnected_of_o2_exact hP.thmD.d2 hlt hS hex2 hK' hz' hO2'
    · push Not at hO2
      by_cases hEx : ∃ K' ∈ Φ, ∃ (z' : X) (hz' : IsUniqueInvolution K' z') (W : Subgroup X)
          (hKW : K' ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : X) K') = W ∧
            Thm4Twin.F2.ExitSec W K' hKW z' hz'
      · obtain ⟨K', hK', z', hz', W, hKW, hWs, -, hexit⟩ := hEx
        exact dstarConnected_of_exitSec_exact hmodel hS hex2 hK' hz' (hO2 K' hK' z' hz') hKW hWs
          hexit
      · push Not at hEx
        have hno : NoExitSec X Φ := fun K' hK' z' hz' W hKW hWs hWg =>
          hEx K' hK' z' hz' W hKW hWs hWg
        have hodd := oddCent_bot_of_noExitSec hcit hP hlt hS' hS.trans htight hno
        exfalso
        rcases hcase with h | h | ⟨W, hKW, hWs, hWg, hexit⟩
        · exact h (hodd K hK z hz)
        · exact hO2 K hK z hz h
        · exact hEx K hK z hz W hKW hWs hWg hexit
  · by_cases hall : (∀ K ∈ Φ, tightCore K = K) ∧ NoExitSec X Φ
    · exfalso
      apply hex2
      intro J hJ
      obtain ⟨zJ, hzJ⟩ := (hS.hyp.omega1 J hJ).1
      exact isPGroup_of_oddCent hS.hyp hJ hzJ
        (oddCent_bot_of_noExitSec hcit hP hlt hS' hS.trans hall.1 hall.2 J hJ zJ hzJ) (hS.two J hJ)
    · by_cases hc : TwoConstrained X
      · exfalso
        obtain ⟨P, hPn, hP2, hPc⟩ := hc
        apply hex2
        intro J hJ
        obtain ⟨zJ, hzJ⟩ := (hS.hyp.omega1 J hJ).1
        exact isPGroup_of_oddCent hS.hyp hJ hzJ
          (oddCoreIn_centralizer_eq_bot_of_centralizer_le hPn hP2 hPc
            (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hzJ.sq))
          (hS.two J hJ)
      · exact hN X hlt Φ hS hex2 hc hall

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
