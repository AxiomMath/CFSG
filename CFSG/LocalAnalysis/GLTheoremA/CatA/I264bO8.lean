module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bR23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Prime3

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_o8p2 (hR : Rank23At Y) {K B : Subgroup Y} (h : KHyp 3 K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < 3 ^ 3)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isD4two) : False := by
  have hlist : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isList94 := by
    obtain ⟨i, hi, e⟩ := hcat
    exact ⟨i, Or.inr (Or.inr (Or.inl hi)), e⟩
  obtain ⟨hZP, hZ, hRb⟩ := rank23_data hR h hlist
  have hcatK : catalogIs ↥K S9.isD4two := ys03_catalogIs_of_mulEquiv (mulEquivQuotCenter hZ).symm hcat
  by_cases hin : ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹
  · obtain ⟨E₀, hE₀el, hE₀c⟩ := D4XF.d4two_rank4 hcatK
    refine false_of_inner h hZ hin hRb ⟨E₀.map K.subtype, Subgroup.map_subtype_le E₀,
      S9.l94t_isElemAbelian_map _ hE₀el, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE₀c]
    norm_num
  · obtain ⟨b, hb, hbn⟩ : ∃ b ∈ B, ∀ k ∈ K, ¬ ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹ := by
      by_contra hcon
      apply hin
      intro b hb
      by_contra hne
      exact hcon ⟨b, hb, fun k hk hall => hne ⟨k, hk, hall⟩⟩
    have hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1 := by
      intro k hk hk'
      have hmem : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hk' g g.2)
      rw [hZ, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have hBK : B ≤ Subgroup.normalizer (K : Set Y) := fun g _ => by
      rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
      exact Subgroup.mem_top g
    exact D4T.noTriality_core (D4XF.d4TwoFacts_of_residual D4YB.d4TwoAutNormInn_holds hcatK) hKc h.elem
      hBK ⟨b, hb, hbn⟩ (Or.inl fun P hP => h.maxrank P le_top hP)

end Prime3

theorem card_o8p2 {S : Type} [Group S] (h : catalogIs S S9.isD4two) : Nat.card S = 3 ^ 5 * 716800 := by
  have := (CFSG.Timmesfeld.card_statedClassicalModel_two (D4XF.statedModel_of_d4two h)).2.2.2.1 rfl
  rw [this]
  simp only [CFSG.Open.ordD]
  decide

end CFSG.LocalAnalysis.GLTheoremA
