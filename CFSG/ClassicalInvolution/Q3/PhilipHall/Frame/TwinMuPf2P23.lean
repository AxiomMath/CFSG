module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf2Mu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUConnE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section MuP23

variable {n : ℕ}

theorem conn_o2_classify_mu {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}
    (hD : TC.Thin.ThmDAbsBelow 3 n) (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥)
    (hO2 : TightInO2 z) (hne : ∃ A ∈ Φ, ∃ B ∈ Φ, A ≠ B)
    (hMu : TwinPerpV3.SecMuExcl X Φ) :
    (∃ V : Subgroup X, WSet Φ = {V}) ∨ Nonempty (TC.Thin.AEIdent Φ 5) ∨
      Nonempty (TC.Thin.AEIdent Φ 6) := by
  have F := TwinDisc.ExitU.q8Fam_of_q8Section hS htrans hK hz hodd hO2
  rcases F.thmDConcl hD hlt with h1 | ⟨W', hW⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm5, ⟨I⟩⟩ | I29
  · exfalso
    obtain ⟨A, hA, B, hB, hAB⟩ := hne
    exact hAB (h1 A hA B hB)
  · exact Or.inl ⟨W', hW⟩
  · by_cases hWc : ∃ V : Subgroup X, WSet Φ = {V}
    · exact Or.inl hWc
    · exact absurd ⟨E, hE⟩ (hMu.noE8 ⟨K, hK, z, hz, hO2⟩ hWc)
  · by_cases hWc : ∃ V : Subgroup X, WSet Φ = {V}
    · exact Or.inl hWc
    · exact absurd I64 (hMu.noE64 ⟨K, hK, z, hz, hO2⟩ hWc)
  · by_cases hm6 : m ≤ 6
    · rcases (show m = 5 ∨ m = 6 by omega) with rfl | rfl
      · exact Or.inr (Or.inl ⟨I⟩)
      · exact Or.inr (Or.inr ⟨I⟩)
    · by_cases hWc : ∃ V : Subgroup X, WSet Φ = {V}
      · exact Or.inl hWc
      · exact absurd ⟨I⟩ (hMu.noAE ⟨K, hK, z, hz, hO2⟩ hWc m (by omega))
  · by_cases hWc : ∃ V : Subgroup X, WSet Φ = {V}
    · exact Or.inl hWc
    · exact absurd I29 (hMu.noE29 ⟨K, hK, z, hz, hO2⟩ hWc)

@[expose] def P23E4Mu (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      T3.DStarConnected (TwinDisc.secFam (Om R) e) →
      TwinPerpV3.SecMuExcl (SecQ R e) (TwinDisc.secFam (Om R) e)

theorem p23E4Exit_of_mu (hT : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hAe5 : P23E4Ae5 n) (hW : P23E4W n)
    (hMu : P23E4Mu n) : P23E4Exit n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno
  obtain ⟨hedge, htw, hdich⟩ := e_exit_frame3 (hT n hcit hP) hc
  rcases hdich with htrans | hcase1
  swap
  · exact Or.inl hcase1
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have hlt := secQ_card_lt hc.std.perp hc.data.he1
  have hodd := oddCent_exit_gen2 hD4 hcit hP hc.std.perp hc.data.he2 hc.data.he1 htrans hedge htw
  have hdist : ∃ A ∈ TwinDisc.secFam (Om R) e, ∃ B ∈ TwinDisc.secFam (Om R) e, A ≠ B := by
    obtain ⟨A, hA, B, hB, hBA⟩ := htw
    exact ⟨A, hA, B, hB.1, hBA.symm⟩
  have hcls : ∀ hconn : T3.DStarConnected (TwinDisc.secFam (Om R) e),
      (∃ K ∈ TwinDisc.secFam (Om R) e, ∃ z : SecQ R e, IsUniqueInvolution K z ∧ TightInO2 z) →
      ECase1 R W e ∨ SecAE R e 6 := by
    intro hconn ⟨K, hK, z, hz, hO⟩
    rcases conn_o2_classify_mu hP.thmD.d2 hlt hS htrans hK hz (hodd K hK z hz) hO hdist
        (hMu hcit hP Y R S t K' W u e g hc hno hconn) with hWc | h5 | h6
    · exact Or.inl (hW hcit hP Y R S t K' W u e g hc hno hWc)
    · exact hAe5 hcit hP Y R S t K' W u e g hc hno h5
    · exact Or.inr h6
  by_cases hconn : T3.DStarConnected (TwinDisc.secFam (Om R) e)
  · rcases TwinDisc.ExitU.noExit_or_o2_or_e4 hS htrans hedge hodd with h | ho | hE
    · exact absurd h hno
    · exact hcls hconn ho
    · by_cases hO2 : ∃ K ∈ TwinDisc.secFam (Om R) e, ∃ z : SecQ R e,
          IsUniqueInvolution K z ∧ TightInO2 z
      · exact hcls hconn hO2
      · exact absurd hE ((hMu hcit hP Y R S t K' W u e g hc hno hconn).noE4 hO2)
  · rcases TwinDisc.ExitU.noExit_or_ae5 hmodel hP.thmD.d2 hlt hS htrans hedge hodd hconn with
      h | ⟨-, I⟩
    · exact absurd h hno
    · exact hAe5 hcit hP Y R S t K' W u e g hc hno I

end MuP23

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
