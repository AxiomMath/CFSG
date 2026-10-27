module

public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusOrthPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusSymplectic
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusTypeAPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SG

open CFSG.Open CFSG.StandardType

private theorem labelAll_torusLift_four {lab : GLALabel} {r : ℕ} (hr : 4 ≤ r)
    (h : CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 r R) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 4 R := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, ggTorusLift_mono Nat.prime_three hq.2 hr⟩)
    (h Q hQ)


theorem labelAll_torusLift_cls {lab : GLALabel} (hlab2 : GLAInLambda2 lab)
    (ht : (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 9 ≤ lab.rank) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 6 ≤ lab.rank) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 6 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 5 ≤ lab.rank)) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 4 R := by
  rcases ht with ⟨htag, h3, hr⟩ | ⟨htag, h3, hr⟩ | ⟨htag, h3, hr⟩ | ⟨htag, hr⟩ |
    ⟨htag, h3, hr⟩ | ⟨htag, h3, hr⟩ | ⟨htag, h3, hr⟩ | ⟨htag, h3, hr⟩
  ·
    exact labelAll_torusLift_four (by omega)
      (largeEvenLabelAll_torusLift_typeA Nat.prime_three htag (by omega) h3)
  ·
    exact labelAll_torusLift_four (by norm_num)
      (SCFourCover.largeEvenLabelAll_torusLift_typeAPlus_threeFive htag h3 (by omega))
  ·
    exact labelAll_torusLift_four (by unfold ggUnitaryTorusRank; split_ifs <;> omega)
      (largeEvenLabelAll_torusLift_twA hlab2 htag Nat.prime_three h3)
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    intro Q hQ
    rcases htag with rfl | rfl <;>
    · dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
      exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_mono Nat.prime_three
        (SCFourCover.ggTorusLift_three_symplectic (K := K) k) (by omega)⟩
  ·
    exact labelAll_torusLift_four hr
      (largeEvenLabelAll_torusLift_D htag hlab2 hr Nat.prime_three h3)
  ·
    exact labelAll_torusLift_four (by norm_num)
      (SCFourCover.largeEvenLabelAll_torusLift_orthPlus_threeFive htag h3 hr)
  ·
    exact labelAll_torusLift_four (by omega)
      (largeEvenLabelAll_torusLift_twD htag hlab2 (by omega) Nat.prime_three h3)
  ·
    exact fun Q hQ => largeEvenRawDatum_mono
      (fun _ _ _ _ hq => ⟨hq.1, ggTorusLift_mono Nat.prime_three hq.2.2 (by omega)⟩)
      (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three
        ⟨by omega, Or.inl ⟨htag, h3⟩⟩ Q hQ)

end CFSG.LocalAnalysis.GLTheoremA.S265.SG

end
