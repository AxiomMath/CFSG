module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4General
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58S

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

section Certified


theorem harris82Theorem1KProper_of_inputs (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hID : Harris81Lemma35IdentFact)
    (hLo : RowLieOther) (hAlt : RowAlt) (hSpor : RowSpor)
    (h410 : Harris82Lemma410Rest) (hU1 : Harris82Lemma411U1) (hU4 : Harris82Lemma411U4)
    (h51e : Harris82Lemma51e) (h54 : Harris82Lemma54) (h58 : Harris82Lemma58b)
    (h3 : Harris82Theorem1FieldThree) (hSol : Solomon74SpinSevenAsUsed) :
    Harris82Theorem1KProper := by
  have hI : C3Inputs := ⟨hCI, hGA, hID, knownRow_of_rows hLo hAlt hSpor, hSol, h410, hU1,
    harris82Lemma411U2_holds, harris82Lemma411U3_holds, hU4, h51e,
    harris82Lemma58Spin7_of_51e h51e⟩
  intro G _ _ _ hnonab hK hcat z hz L hL hzL p hp hp2 hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' := hM
  rcases hM' with ⟨-, ⟨τ, n, f, hlie⟩, -, -⟩ | ⟨-, ⟨e⟩⟩
  · have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := mem_center_of_le_centralizer hL.1 hzL
    have hz' : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
    by_cases hpsl : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) .PSL 2 p f
    ·
      have hcen : center (↥L ⧸ pPrimeCore 2 ↥L) ≠ ⊥ := by
        intro hbot
        have h1 : (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
            center (↥L ⧸ pPrimeCore 2 ↥L) := mk_mem_center_of_mem_center hzc
        rw [hbot, mem_bot] at h1
        exact mk_ne_one_of_orderOf_two hz' h1
      obtain ⟨-, -, hsl⟩ := T23.slTwo_of_lieModel hGA hL.2.2 hp hp2 hpsl hcen
      exact false_of_intrinsic_slTwo hCI hnonab hcat hz hL hzL hp hp2 hsl
    · have hf : 1 ≤ f := (N36.admissible_of_lieModel' hlie).2.1
      by_cases h3' : p ^ f = 3
      ·
        obtain ⟨rfl, rfl⟩ := (Nat.prime_three.pow_eq_iff).mp h3'
        exact h3 G hnonab hK hcat z hz L hL hzL hM τ n hlie
      · exact false_of_general hI h54 h58 hnonab hK hcat hz hL hzL hp hp2 hM hlie
          (CatLeafProof.OddInner.five_le_pow hp hp2 hf h3') hpsl
  ·
    have := hL.2.2.1
    exact TBLit.not_isPerfect_sl2Three (Group.IsPerfect.ofSurjective (f := e.toMonoidHom)
      e.surjective)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
