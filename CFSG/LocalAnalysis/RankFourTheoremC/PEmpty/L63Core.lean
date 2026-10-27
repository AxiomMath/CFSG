module

import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem normalizerRank_of_le_core (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p X}
    {B T : Subgroup X} (hBP : B ≤ (P : Subgroup X)) (hT : IsMaxTwoInvariantIn B ⊤ T)
    (hTD : T ≤ primeComplementCore (G := X) p) :
    Open.pRank p (P : Subgroup X) ≤ Open.pRank p (normalizer (T : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  have hDtop : normalizer (D : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hBD : B ≤ normalizer (D : Set X) := by rw [hDtop]; exact le_top
  have hPD : (P : Subgroup X) ≤ normalizer (D : Set X) := by rw [hDtop]; exact le_top
  have hB3 : IsPGroup p B := P.isPGroup'.to_le hBP
  obtain ⟨⟨-, hT2, hBT⟩, hmax⟩ := hT
  obtain ⟨R, hRsyl, hTR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_two hB3 hD3 hBD hTD hT2 hBT
  have hRT : R = T := hmax R ⟨le_top, hRsyl.2.1, hBR⟩ hTR
  have hTsyl : fusionIsSylowIn 2 T D := hRT ▸ hRsyl
  have hbotp : IsPGroup p (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  have hbot2 : IsPGroup 2 (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup X) ≤ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hSsyl, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_two P.isPGroup' hD3 hPD bot_le hbot2 hPbot
  obtain ⟨c, -, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    hp Nat.prime_two hbotp hD3 bot_le hSsyl hTsyl bot_le bot_le
  have hle : (P : Subgroup X).map (MulAut.conj c).toMonoidHom ≤ normalizer (T : Set X) := by
    rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPS
  calc Open.pRank p (P : Subgroup X)
      = Open.pRank p ((P : Subgroup X).map (MulAut.conj c).toMonoidHom) :=
        (pRank_map_automorphism p hp.one_lt _ _).symm
    _ ≤ Open.pRank p (normalizer (T : Set X)) := CFSG.SectionRank.pRank_mono hp.one_lt hle

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
