module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapAll
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven

theorem three_le_pRank_psu_four_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 4 2 K))) := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have hζq : ζ ^ (2 + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ])
  exact three_le_pRank_torus (by norm_num) hζ (i₀ := (0 : Fin 4)) (i₁ := 1) (i₂ := 2) (i₃ := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun j => torusDiag_mem_SU (by norm_num) (prod_torusVec ζ j _)
      (by rw [torusVec_pow, hζq, torusVec_one])

theorem three_le_pRank_psp_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {r : ℕ}
    (hr : 3 ≤ r) : 3 ≤ Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp r K))) := by
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact psp_three_le_pRank_three hr

theorem kFactSeitzRankThreeExceptions : KFactSeitzRankThreeExceptions := by
  intro K _ _ d ⟨⟨p, k, hpp, hkpos⟩, hqp, hq1, hd⟩ ⟨e⟩
  dsimp only at hqp hq1
  subst hqp hq1
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  rcases hd with rfl | rfl | rfl
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 _ hv e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eF]
    exact three_le_pRank_psu_four_two (by rw [hF]; rfl)
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 _ hv rfl le_rfl e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eF]
    exact three_le_pRank_psp_two (by rw [hF]; rfl) le_rfl
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 _ hv rfl (by norm_num) e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eF]
    exact three_le_pRank_psp_two (by rw [hF]; rfl) (by norm_num)

end CFSG.AGLEmbeddingD2
