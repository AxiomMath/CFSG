module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.Sporadic.Recognition.LyonsSimsRecognition

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Solomon44LyTrivialCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ →
      IsDoubleCoverOfAlt
        (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) 11 →
      Nonempty (G ≃* Blueprint.NativeSporadic.Ly)

@[expose] def Solomon44OddCore (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 →
      IsDoubleCoverOfAlt
        (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) n →
      pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥

theorem solomon44LyTrivialCore_of_lyRecognition
    (h : CFSG.Sporadic.Recognition.LyonsSims.LyRecognition) : Solomon44LyTrivialCore := by
  intro G _ _ _ hnonab t ht hbot hcov
  let C := ↥(centralizer ({t} : Set G))
  let e : C ⧸ pPrimeCore 2 C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hC : IsDoubleCoverOfAlt C 11 :=
    CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e hcov
  obtain ⟨hq, hc, ⟨φ⟩⟩ := hC
  have htC : (⟨t, self_mem_centralizer t⟩ : C) ∈ center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have hZ : center C = zpowers (⟨t, self_mem_centralizer t⟩ : C) := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact zpowers_le.2 htC
    · rw [hc, Nat.card_zpowers, Subgroup.orderOf_mk, ht]
  exact h G inferInstance hnonab t ht hq.1 hZ
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ.symm).trans φ⟩

theorem solomon44Ly_of_lyRecognition (h : CFSG.Sporadic.Recognition.LyonsSims.LyRecognition)
    (hO : Solomon44OddCore 11) : Solomon44Ly := by
  intro G _ _ _ hnonab t ht hcov
  exact solomon44LyTrivialCore_of_lyRecognition h G hnonab t ht (hO G hnonab t ht hcov) hcov

end CFSG.OddStandard.Solomon75
