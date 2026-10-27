module

public import CFSG.LocalAnalysis.OddStandard.Solomon75OddCoreCert
public import CFSG.Sporadic.Recognition.LyonsFinalCert

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def OddCoreElevenThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 → IsDoubleCoverOfAlt (CentQuot t) 11 →
      ¬ 3 ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))

section Aschbacher


theorem solomon44OddCore_eleven_of_leaf
    (h : OddCoreElevenThree) : Solomon44OddCore 11 := by
  intro G _ _ _ hnonab t ht hcov
  exact oddCore_eleven_eq_bot_of_certificate hnonab ht hcov (h G hnonab t ht hcov)


theorem solomon44Ly_of_leaf
    (h : OddCoreElevenThree) : Solomon44Ly :=
  solomon44Ly_of_lyRecognition Sporadic.Recognition.LyonsSims.LyFinal.lyRecognition
    (solomon44OddCore_eleven_of_leaf h)

end Aschbacher

end CFSG.OddStandard.Solomon75
