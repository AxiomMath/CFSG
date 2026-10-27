module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding.KFactProofs

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81NineThreeRankCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → Open.pRank p (d1PlusCore p H K) ≤ 1

variable (G) in
@[expose] def AGL81TenSixTwelveCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), I₀ ≤ d1PlusCore p H K →
      ∀ b ∈ d1LiftX p H Q K, ∀ x ∈ I₀, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 H

def commModTwoCore (H A : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ b ∈ A, b * g * b⁻¹ * g⁻¹ ∈ pCoreOf 2 H}
  one_mem' := ⟨H.one_mem, fun b _ => by simp [(pCoreOf 2 H).one_mem]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
    refine ⟨H.mul_mem hg hh, fun b hb => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 H hg) _).mp (hhA b hb)
    have e : b * (g * h) * b⁻¹ * (g * h)⁻¹ =
        (b * g * b⁻¹ * g⁻¹) * (g * (b * h * b⁻¹ * h⁻¹) * g⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem (hgA b hb) h1
  inv_mem' := by
    rintro g ⟨hg, hgA⟩
    refine ⟨H.inv_mem hg, fun b hb => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 H (H.inv_mem hg)) _).mp
      ((pCoreOf 2 H).inv_mem (hgA b hb))
    have e : b * g⁻¹ * b⁻¹ * g⁻¹⁻¹ = g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem agl81ElevenSevenCfgThree_of (h1031 : AGL81TenThreeOneAt G) (h10C : AGL81TenOneCZero G)
    (h91 : AGL81TenNineOneCfg G) (h93r : AGL81NineThreeRankCfg G)
    (h1013 : AGL81TenThirteenAt G) (h106 : AGL81TenSixX G) (h1062 : AGL81TenSixTwelveCfg G) :
    AGL81ElevenSevenCfgThree G := by
  intro hS P M H Q K hσ hd hnc L hL hLn hno
  have h1 : ∀ I₀ ∈ cZero (H ⊓ L),
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K := by
    intro I₀ hI₀
    rcases h1013 hS 3 P M H Q K hσ hd L hL I₀ hI₀ with h | ⟨hp3, hA, hI⟩
    · exact h
    · exact absurd ⟨hp3, hA, I₀, hI₀, hI⟩ hno
  have hJX : jOne H L ≤ d1PlusCore 3 H K := iSup₂_le h1
  obtain ⟨I₀, hI₀⟩ := h10C hS 3 P M H Q K hd L hL (h91 hS 3 P M H Q K hd L hL)
  have h3J : 3 ∣ Nat.card (jOne H L) := (h1031 hS 3 P M H Q K hd L hL I₀ hI₀).trans
    (Subgroup.card_dvd_of_le (IsCZeroMember.oUpperTwo_le_jOne hI₀))
  have h2 : Open.pRank 3 (d1PlusCore 3 H K) = 1 :=
    le_antisymm (h93r hS 3 P M H Q K hd)
      (GLBCoreNormalizer.one_le_pRank_of_dvd Nat.prime_three
        (h3J.trans (Subgroup.card_dvd_of_le hJX)))
  have h3 : jZero H L ≤ d1PlusCore 3 H K ∨ IsLinThreeFour K := by
    by_cases hall : ∀ I₀ ∈ cZero (H ⊓ L), I₀ ≤ d1PlusCore 3 H K
    · exact Or.inl (iSup₂_le hall)
    · push Not at hall
      obtain ⟨I₀, hI₀, hn⟩ := hall
      exact Or.inr ((h106 hS 3 P M H Q K hd L hL I₀ hI₀ (h1 I₀ hI₀)).resolve_left hn).2
  refine ⟨h1, h2, h3, fun hJ0 b hb x hx => ?_⟩
  have hbQ : b ∈ Q := d1LiftX_le 3 H Q K hb
  have hJS : jZero H L ≤ commModTwoCore H (d1LiftX 3 H Q K) := iSup₂_le fun I₀ hI₀ y hy =>
    ⟨(hI₀.le.trans inf_le_left) hy, fun b' hb' =>
      h1062 hS 3 P M H Q K hd L hL I₀ hI₀ ((IsCZeroMember.le_jZero hI₀).trans hJ0) b' hb' y hy⟩
  have hT : b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 H := (hJS hx).2 b hb
  have hbN : b ∈ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hd.le_H hbQ)) y
    have e2 := Subgroup.mem_normalizer_iff.mp (hMn (hd.base.1 hbQ)) y
    exact ⟨fun hy => ⟨e1.mp hy.1, e2.mp hy.2⟩, fun hy => ⟨e1.mpr hy.1, e2.mpr hy.2⟩⟩
  have hJ : b * x * b⁻¹ * x⁻¹ ∈ jZero H L :=
    (jZero H L).mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_jZero H L hbN) x).mp hx)
      ((jZero H L).inv_mem hx)
  exact inf_pCoreOf_le ((jZero_le H L).trans inf_le_left) ⟨hJ, hT⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
