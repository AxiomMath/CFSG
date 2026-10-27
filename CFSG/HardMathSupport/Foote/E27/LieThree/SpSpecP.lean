
module


public import CFSG.HardMathSupport.Foote.E27.LieThree.SpQuot
public import Certificates.Certificate131008

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native TauCeti

section Certificates

theorem sp63_S0 : ∃ S : Subgroup (SpJP 3 3),
    Nat.card S = 3 ^ (Nat.card (SpJP 3 3)).factorization 3 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set (SpJP 3 3))) :=
  Certificates.certificate131008

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_psp_three_three (h : E27Config X K R T z) (hz : z ∈ K) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 3) (eK : ↥K ≃* StatedProj (StatedSp 3 F)) : False := by
  obtain ⟨S, hS, hprop⟩ := sp63_S0
  exact h.false_of_psp_three hz (by norm_num) hF eK S hS hprop

end Certificates

end CFSG.HardMathSupport.Foote.E27
