module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3ConjGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Type
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_of_not_two_dvd {A B : Subgroup G} (hB : ¬ 2 ∣ Nat.card B) (hA2 : IsPGroup 2 A)
    (hA : A ≤ B) : Nat.card A ≤ 2 := by
  obtain ⟨n, hn⟩ := hA2.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hA
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hn]; norm_num
  · exact absurd ((dvd_pow_self 2 hpos.ne').trans (hn ▸ hdvd)) hB

theorem lemma44_card_of_generic (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {u : G} (hgen : IsGenericPoint 3 P M u) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) (hA : A ≤ GLBPrimeCore 3 M ⊓ centralizer ({u} : Set G)) :
    Nat.card A ≤ 2 := by
  obtain ⟨J', hJ'C, hCJ', hperf', hlt', hmin', hnot', Q', _, ψ', hψ', hker', hQ'⟩ :=
    exists_isPrimeThreeType_of_generic hS hU0 K1 K2 K3 K4 hno hp hM hgen rfl
  rcases hQ' with hA6 | hU3 | hM11 | hL34 | hL28
  · exact card_le_two_of_not_two_dvd (a6_not_two_dvd_card hS hU0 hD1 hA1 hA3 hp hM hgen
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hA6⟩) hA2 hA
  · exact card_le_two_of_not_two_dvd (u3_not_two_dvd_card hS hU0 hD1 u3SylowData_proved
      u3BorelCore_proved hp hM hgen
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hU3⟩) hA2 hA
  · have hJ : IsM11Normal M u J' :=
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hM11⟩
    exact card_le_two_of_not_two_dvd (m11_not_two_dvd_card hS hU0 hD1 hKM hp hM hgen hJ
      (m11_reducedCentralizer_isPGroup hS hU0 hKM hKA hp hM hgen hJ)) hA2 hA
  · exact l34_lemma44_card hS hU0 hD1 hL.twoSignalizer hL.three hL.unitary hp hM hgen
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hL34⟩ A hA2 hA
  · exact card_le_two_of_not_two_dvd (l28_not_two_dvd_card hS hU0 hD1 hE1 hE3 hp hM hgen
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hL28⟩) hA2 hA

theorem card_pCore_inf_centralizer_le_two (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {y : G}
    (hy : IsLargeObstruction 3 M y) :
    Nat.card (pCoreOf 2 M ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hmM, -, hgen⟩ := exists_conj_isGenericPoint hS hU0 hp hM hy
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hcop : Nat.Coprime 3 (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hT₀le : T₀ ≤ GLBPrimeCore 3 M :=
    CFSG.AGLEmbedding.le_glbPrimeCore (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 M) hMT₀
      hcop
  set A : Subgroup G := T₀ ⊓ centralizer ({y} : Set G) with hA
  have hA2 : IsPGroup 2 A := hT₀2.to_le inf_le_left
  have hle : A.map (MulAut.conj m).toMonoidHom ≤
      GLBPrimeCore 3 M ⊓ centralizer ({MulAut.conj m y} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨hT₀le ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMT₀ hmM) a).mp ha.1
    · rw [centralizer_singleton_conj]
      exact mem_map_of_mem _ ha.2
  have h := lemma44_card_of_generic hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM
    hgen (hA2.map _) hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj m).injective] at h

end CFSG.LocalAnalysis.RankThreeTheoremC
