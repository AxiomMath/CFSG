module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF13
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF15a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrF15b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrPres
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem pres11_iff (fr : Frame G) : Pres11 fr ↔ (GFrame.ofFrame fr).P11 := Iff.rfl

theorem lf_sigma (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) :
    ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ →
      (frameWith s g).Fact13 ∧ (frameWith s g).Fact15 ∧ Pres11 (frameWith s g) := by
  intro g hg2 hg
  let P : Subgroup G := (frameWith s g).Sσ
  have hP : P ≤ normalizer (L : Set G) := s3_Sσ_le_normalizer hS hZ s hg
  let j : ↥P →* MulAut (L ⧸ center L) := jOn L hP
  have hjinj : Function.Injective j := s3_jOn_Sσ_injective hS hZ hOut s hg2 hg hP
  have ha₁ : s.fr.a₁ ∈ P := Subgroup.subset_closure (by simp [frameWith])
  have hb₁ : s.fr.b₁ ∈ P := Subgroup.subset_closure (by simp [frameWith])
  have ha₂ : s.fr.a₂ ∈ P := Subgroup.subset_closure (by simp [frameWith])
  have hb₂ : s.fr.b₂ ∈ P := Subgroup.subset_closure (by simp [frameWith])
  have hh₀ : s.fr.h₀ ∈ P := Subgroup.subset_closure (by simp [frameWith])
  have hgP : g ∈ P := Subgroup.subset_closure (by simp [frameWith])
  let gP : GFrame ↥P :=
    ⟨⟨s.fr.a₁, ha₁⟩, ⟨s.fr.b₁, hb₁⟩, ⟨s.fr.a₂, ha₂⟩, ⟨s.fr.b₂, hb₂⟩,
      ⟨s.fr.h₀, hh₀⟩, ⟨g, hgP⟩⟩
  have hmapj : gP.map j = GFrame.ofFrame s.fr' := by
    change GFrame.mk (j gP.a₁) (j gP.b₁) (j gP.a₂) (j gP.b₂) (j gP.h₀) (j gP.σ) =
      GFrame.mk s.fr'.a₁ s.fr'.b₁ s.fr'.a₂ s.fr'.b₂ s.fr'.h₀ s.fr'.σ
    rw [GFrame.mk.injEq]
    exact ⟨actsAs_unique L (jOn_actsAs L hP gP.a₁) (s3_actsAs_gens s).1,
      actsAs_unique L (jOn_actsAs L hP gP.b₁) (s3_actsAs_gens s).2.1,
      actsAs_unique L (jOn_actsAs L hP gP.a₂) (s3_actsAs_gens s).2.2.1,
      actsAs_unique L (jOn_actsAs L hP gP.b₂) (s3_actsAs_gens s).2.2.2.1,
      actsAs_unique L (jOn_actsAs L hP gP.h₀) (s3_actsAs_gens s).2.2.2.2.1,
      actsAs_unique L (jOn_actsAs L hP gP.σ) hg⟩
  have e1 : GFrame.ofFrame (frameWith s g) = gP.map P.subtype := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [fact13_iff, e1, f13_map_iff P.subtype_injective gP,
      ← f13_map_iff (f := j) hjinj gP, hmapj]
    exact (fact13_iff s.fr').mp (s.facts.2.2.1)
  · rw [fact15_iff, e1]
    rw [show (gP.map P.subtype).F15 ↔ gP.F15 from
      and_congr (f15a_map_iff P.subtype_injective gP)
        (f15b_map_iff P.subtype_injective gP)]
    rw [show gP.F15 ↔ (gP.map j).F15 from
      (and_congr (f15a_map_iff hjinj gP) (f15b_map_iff hjinj gP)).symm]
    rw [hmapj]
    exact (fact15_iff s.fr').mp (s.facts.2.2.2.2.1)
  · rw [pres11_iff, e1, p11_map_iff P.subtype_injective gP,
      ← p11_map_iff (f := j) hjinj gP, hmapj]
    exact (pres11_iff s.fr').mp (s.facts.1.1)

end CFSG.OddStandard.HigherRank.YamadaG23
