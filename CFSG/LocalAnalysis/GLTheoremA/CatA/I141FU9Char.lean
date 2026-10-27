module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem u9_char_two {Γ : Type} [Group Γ] [Finite Γ] {A K : Subgroup Γ} (hI : S10.InnDiagOn 3 A K)
    {d : TauCeti.ValidLieTypeIndex} (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    d.1.characteristic = 2 ∨ Nat.card (PSimple 3 K) ≤ 25920 := by
  by_cases hd2 : d.1.characteristic = 2
  · exact Or.inl hd2
  right
  obtain ⟨hperf, lab, hlam, hraw⟩ := hI.2
  have hLl : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot 3 K) (· = lab) :=
    ⟨hperf, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hLl
  obtain ⟨t, n, p, f, hp, hL⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char d
  have hLX : CFSG.Models.LieModel (PSimple 3 K) t n p f := CFSG.Models.LieModel.of_mulEquiv e.symm hL
  have hBX : CFSG.Blueprint.LieModel (PSimple 3 K) t n p f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hLX
  have hpprime : p.Prime := by rw [hp]; exact d.characteristic_prime
  have hp2 : p ≠ 2 := by rw [hp]; exact hd2
  have hodd : CFSG.Blueprint.OddLieType (PSimple 3 K) :=
    ⟨t, n, p, f, hpprime, hp2, hBX.admissible, hBX⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  by_cases hc : CFSG.StandardType.markChar lab = 2
  · have hM2 : CFSG.Blueprint.LieModel (PSimple 3 K) (CFSG.StandardType.markTag lab)
        (CFSG.StandardType.markRank lab) 2 (CFSG.StandardType.markDeg lab) := by
      unfold CFSG.StandardType.MarkedModel at hM
      rwa [hc] at hM
    obtain ⟨-, hcard, -⟩ := hO (PSimple 3 K) _ _ 2 _ hM2.admissible hM2
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hM2 hodd with
      ⟨ht, hn, hf⟩ | ⟨ht, hn, hf⟩ | ⟨ht, hn, hf⟩
    · rw [ht, hn, hf] at hcard
      simp [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
        Nat.even_iff] at hcard
      omega
    · rw [ht, hn, hf] at hcard
      simp [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
        Nat.even_iff] at hcard
      omega
    · rw [ht, hn, hf] at hcard
      simp [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
        Nat.even_iff] at hcard
      omega
  ·
    obtain ⟨-, hcard, -⟩ := hO (PSimple 3 K) _ _ _ _ hM.admissible hM
    obtain ⟨tag, rank, nn⟩ := lab
    cases tag
    all_goals first | exact absurd rfl hc | skip
    case B2der =>
      simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markDeg,
        CFSG.StandardType.markChar, CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
        Nat.even_iff] at hcard
      omega
    case G2der =>
      simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markDeg,
        CFSG.StandardType.markChar, CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, Finset.prod_Icc_succ_top,
        Nat.even_iff] at hcard
      omega

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
