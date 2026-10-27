module

import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.mem_layer_quotient (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hD : ¬ IsMulCommutative D) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hHtop : H ≠ ⊤) (hcon : ¬ HasPrimeConstraint (G := H) p)
    {z : G} (hzH : z ∈ H) (hzD : z ∈ D) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      rankThreeLayer (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨K, hKc, -, -, hKp, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H hHtop p
      hprime hcon
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hdvd : p ∣ Nat.card (rankThreeLayer (⊤ : Subgroup (H ⧸ O))) :=
    hKp.trans (Subgroup.card_dvd_of_le (le_sSup hKc))
  have hEbn : (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvd
  set L : Subgroup G := ((rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map H.subtype with hL
  have hHL : H ≤ normalizer (L : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hSL : (P : Subgroup G) ⊓ L ≠ ⊥ := by
    intro hbot
    apply hinf
    rw [eq_bot_iff]
    rintro t ⟨htP, htL⟩
    have htP' : (t : G) ∈ (P : Subgroup G) := by
      rw [Sylow.coe_subtype] at htP
      exact htP
    have : (t : G) ∈ (P : Subgroup G) ⊓ L := ⟨htP', t, htL, rfl⟩
    rw [hbot, mem_bot] at this
    exact mem_bot.2 (Subtype.ext this)
  have hzL : z ∈ L :=
    hext.mem_of_inf_ne_bot_of_not_isMulCommutative hprime hodd hD (hPH.trans hHL) hSL hzD hzc hzp
  obtain ⟨h, hh, hhz⟩ := hzL
  have : h = ⟨z, hzH⟩ := Subtype.ext hhz
  rw [this] at hh
  exact hh

end CFSG.LocalAnalysis.RankThreeTheoremC
