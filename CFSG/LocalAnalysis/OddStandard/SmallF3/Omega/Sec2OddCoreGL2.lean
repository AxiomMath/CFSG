module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def glDiag : GL (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1]
    (by rw [Matrix.det_fin_two_of]; decide)

@[expose] def glSwap : GL (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; decide)

theorem glDiag_mul_self : glDiag * glDiag = 1 := by decide +kernel

theorem glSwap_mul_self : glSwap * glSwap = 1 := by decide +kernel

theorem pow_two_eq_one_of_commute_glDiag :
    ∀ g : GL (Fin 2) (ZMod 3), g * glDiag = glDiag * g → g ^ (2 ^ 1) = 1 := by
  decide +kernel

theorem pow_two_eq_one_of_commute_glSwap :
    ∀ g : GL (Fin 2) (ZMod 3), g * glSwap = glSwap * g → g ^ (2 ^ 1) = 1 := by
  decide +kernel

theorem pow_eight_eq_one_of_commute_glDiag_mul_glSwap :
    ∀ g : GL (Fin 2) (ZMod 3), g * (glDiag * glSwap) = (glDiag * glSwap) * g →
      g ^ (2 ^ 3) = 1 := by
  decide +kernel

theorem oddCore_gl2_zmod3 : oddCore (GL (Fin 2) (ZMod 3)) = ⊥ :=
  oddCore_eq_bot_of_three_involutions glDiag_mul_self glSwap_mul_self
    (oddCore_eq_bot_of_isPGroup_two
      (isPGroup_two_centralizer_of_pow_eq_one 1 pow_two_eq_one_of_commute_glDiag))
    (oddCore_eq_bot_of_isPGroup_two
      (isPGroup_two_centralizer_of_pow_eq_one 1 pow_two_eq_one_of_commute_glSwap))
    (oddCore_eq_bot_of_isPGroup_two
      (isPGroup_two_centralizer_of_pow_eq_one 3 pow_eight_eq_one_of_commute_glDiag_mul_glSwap))

@[expose] noncomputable def glTwoEquivZMod3 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 3) : GL (Fin 2) (ZMod 3) ≃* GL (Fin 2) F := by
  haveI := Fintype.ofFinite F
  exact Units.mapEquiv (RingEquiv.mapMatrix (ZMod.ringEquivOfPrime F Nat.prime_three
    (by rw [← Nat.card_eq_fintype_card, hF]))).toMulEquiv

theorem oddCore_gl2_eq_bot (F : Type) [Field F] [Finite F] (hF : Nat.card F = 3) :
    oddCore (GL (Fin 2) F) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (glTwoEquivZMod3 F hF) oddCore_gl2_zmod3

end CFSG.OddStandard.SmallF3.Omega
