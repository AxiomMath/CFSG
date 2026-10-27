module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsAll
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSixSurvivor
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactUnitaryThreeSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Case
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCharCases
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorBridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem D2AlmostSimple.xSurvivor_of_cases {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (hRA : (R : Subgroup X) = A) (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hcyc : ∀ q hq, Nonempty (K ≃* (TauCeti.CFSGIndex.cyclic q hq).Group) → False)
    (hspor : ∀ s, Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
      D2XSurvivor (R : Subgroup X) A X₀)
    (hlie : ∀ d : TauCeti.ValidLieTypeIndex, p ≠ d.1.characteristic →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → D2XSurvivor (R : Subgroup X) A X₀) :
    D2XSurvivor (R : Subgroup X) A X₀ := by
  obtain ⟨i, hi⟩ := hK.catalog
  cases i with
  | cyclic q hq => exact (hcyc q hq hi).elim
  | alternating n hn =>
    exact d2XSurvivorAt_alt_of d2AltSurvivorFacts d2XSurvivorAt_altSix n hn _ p trivial R _ _
      K hK hRA hi
  | sporadic s => exact hspor s hi
  | lie d =>
    by_cases hchar : p = d.1.characteristic
    · obtain ⟨e⟩ := hi
      obtain ⟨q, hqp, hq⟩ := hK.lieChar_cases hrank hL3 d e hchar
      rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd⟩
      · obtain ⟨e'⟩ :=
          nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 2) ⟨q, hd, hqp, hq2⟩
        exact ⟨fun W hW hWn => hK.dichotomy_of_psl2 (e.trans e') hW hWn,
          fun x hx => hRA ▸ hK.centralizer_A_le_of_psl2 (e.trans e') hx.2⟩
      · exfalso
        have hsmall : IsD2LieCharSmall p d.1 := ⟨q, hqp, Or.inr ⟨hq1, Or.inr hd⟩⟩
        have hRK := hK.sylow_le_of_not_dvd_card_outer
          (kFactLieCharOut K d ⟨e⟩ p hK.prime hK.ne_two hsmall)
        have h3 := kFactUnitaryThreeSylow K d ⟨e⟩ p hK.prime hK.ne_two ⟨q, hqp, hq1, hd⟩
          (R.subtype hRK)
        rw [Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hRA,
          hK.card_A] at h3
        have := Nat.pow_right_injective hK.prime.two_le h3
        omega
    · exact hlie d hchar hi

theorem d2SurvivorsAll_of_leaves (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1)
    (hSpor : D2SporadicCase) : D2SurvivorsAll := by
  intro G _ _ hglob hD1 p P M A H hesc hmax hβ
  have : Fact p.Prime := ⟨hesc.prime⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := hesc.almostSimple hglob.toAGLGlobal
  have hX := hK.xSurvivor_of_cases hRbar hrank hL3
    (fun q hq hi => d2IndexCase_cyclic q hq G hglob hD1 p P M A H A hesc hmax hβ Rbar K hRbar hK hi)
    (fun s hi => (hSpor s G hglob hD1 p P M A H A hesc hmax hβ Rbar K hRbar hK hi).elim)
    fun d hchar ⟨e⟩ => by
      by_cases hexcp : IsD2SeitzException p d.1
      · exact (hexc d G hglob hD1 p hexcp P M A H A hesc hmax hβ Rbar K hRbar hK ⟨e⟩).elim
      · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim
  obtain ⟨hD, hC⟩ := hX
  exact hesc.survivorData_of_reduced hglob.toAGLGlobal hD (hRbar ▸ hC)

end CFSG.AGLEmbeddingD2
