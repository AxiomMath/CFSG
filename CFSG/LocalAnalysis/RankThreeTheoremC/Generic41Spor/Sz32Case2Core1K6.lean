module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Fin

variable {Y : Type} [Group Y] [Finite Y]

theorem szh1k_pRank_le (L : Subgroup Y) :
    CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) := by
  have h5 : Nat.Prime 5 := by norm_num
  rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 5 h5 L.subtype L.subtype_injective ⊤]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 5 h5 le_top

theorem szh1k_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem szh1k_central_coprime_eq_one {G : Type*} [Group G] [Finite G]
    (hcore : primeComplementCore (G := G) 5 = ⊥) {z : G} (hz : z ∈ Subgroup.center G)
    (hcop : Nat.Coprime (orderOf z) 5) : z = 1 := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hz
  have hnormal : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc := Subgroup.mem_center_iff.mp (hle hn) g
    rw [hnc, mul_inv_cancel_right]
    exact hn
  have hc : Nat.Coprime 5 (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]
    exact hcop.symm
  have hlecore := normal_coprime_le_primeComplementCore 5 (Subgroup.zpowers z) hnormal hc
  rw [hcore] at hlecore
  exact Subgroup.mem_bot.mp (hlecore (Subgroup.mem_zpowers z))

theorem szh1_center_bot (hI6103 : KFactI6103Five) (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (hcore : primeComplementCore (G := Y) 5 = ⊥) (hrank : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 3)
    (S : Sylow 5 Y)
    (hOm : ∀ g ∈ (S : Subgroup Y), ∀ h ∈ (S : Subgroup Y), g ^ 5 = 1 → h ^ 5 = 1 → g * h = h * g)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : Subgroup.center ↥L = ⊥ := by
  have h5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨h5⟩
  have hcoreL : primeComplementCore (G := ↥L) 5 = ⊥ :=
    cfsg_subnormal_primeComplementCore_eq_bot 5 L hL.2.1 hcore
  have hnd : ¬ 5 ∣ Nat.card (Subgroup.center ↥L) := by
    intro hdvd
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    have hcatL : IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
      hcat L (Subgroup.center ↥L) inferInstance inferInstance
        (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hL.2.2)
    obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
      (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
        Subgroup.IsSubnormal.top)
    have hmem : ∀ x : ↥L, x ∈ (Q : Subgroup ↥L) → (x : Y) ∈ (S : Subgroup Y) := by
      intro x hx
      have hx' : (x : Y) ∈ Subgroup.map L.subtype (Q : Subgroup ↥L) := ⟨x, hx, rfl⟩
      rw [hQ] at hx'
      exact hx'.1
    rcases hI6103 ↥L (szh1k_quasisimple hL.2.2) hcatL hdvd Q with hr | hnc
    · have := hr.trans (szh1k_pRank_le L)
      omega
    · refine hnc (Subgroup.isMulCommutative_closure ?_)
      intro g hg h hh _
      have hg5 : (g : Y) ^ 5 = 1 := by
        have := map_pow L.subtype g 5
        rw [hg.2, map_one] at this
        exact this.symm
      have hh5 : (h : Y) ^ 5 = 1 := by
        have := map_pow L.subtype h 5
        rw [hh.2, map_one] at this
        exact this.symm
      exact Subtype.ext (hOm (g : Y) (hmem g hg.1) (h : Y) (hmem h hh.1) hg5 hh5)
  have hcopZ : Nat.Coprime 5 (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd h5).mpr hnd
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact szh1k_central_coprime_eq_one hcoreL hz
    (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hz) hcopZ.symm)

end Fin

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
