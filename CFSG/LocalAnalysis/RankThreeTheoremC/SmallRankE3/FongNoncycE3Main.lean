module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGNonMain
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNon

@[expose] def KGStep6NoncycE3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (Kb Sb Bb Mb : Subgroup A) (z : A),
    KQCfg A p Kb Sb Bb Mb z → KGStep4Concl A Kb Sb → Sb ⊓ Kb = ⊥ → ¬ IsCyclic ↥Sb →
      CFSG.Open.pRank 3 Kb ≤ 3 → False

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem false_of_cent_nc3 (h : KGNoncycCentE3) (c : KQCfg A p Kb Sb Bb Mb z)
    (hc : KGStep4Concl A Kb Sb) (hbot : Sb ⊓ Kb = ⊥) (hnc : ¬ IsCyclic ↥Sb)
    (hK3 : CFSG.Open.pRank 3 Kb ≤ 3) : False := by
  have hinj := act_injective c
  have hSp : IsPGroup 2 ↥(act Sb c.S_le_K).range :=
    c.S_two.of_surjective (act Sb c.S_le_K).rangeRestrict
      (act Sb c.S_le_K).rangeRestrict_surjective
  have hSc : ¬ IsCyclic ↥(act Sb c.S_le_K).range := by
    intro hcyc
    exact hnc (isCyclic_of_injective (act Sb c.S_le_K).rangeRestrict
      (fun a b hab => hinj (congrArg Subtype.val hab)))
  have hBp : IsPGroup p ↥(act Bb c.B_le_K).range :=
    (IsPGroup.of_card (n := 2) c.B_card).of_surjective (act Bb c.B_le_K).rangeRestrict
      (act Bb c.B_le_K).rangeRestrict_surjective
  have hK3' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Kb) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Kb]
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, h1, h2, hcS₁, hcS₂, hcB₁, hcB₂, hgen⟩ :=
    h ↥Kb p c.prime c.five_le c.simple c.nonab hc.1 hK3' (act Sb c.S_le_K).range
      (act Bb c.B_le_K).range hSp hSc (inf_inner_eq_bot c hbot) hBp (act_range_le_normalizer c)
  obtain ⟨s₁, rfl⟩ := hσ₁
  obtain ⟨s₂, rfl⟩ := hσ₂
  have key : ∀ s : ↥Sb, act Sb c.S_le_K s ≠ 1 →
      (∀ τ ∈ (act Sb c.S_le_K).range, τ * act Sb c.S_le_K s = act Sb c.S_le_K s * τ) →
      (∀ τ ∈ (act Bb c.B_le_K).range, τ * act Sb c.S_le_K s = act Sb c.S_le_K s * τ) →
      ∀ k : ↥Kb, act Sb c.S_le_K s k = k → (k : A) ∈ Mb := by
    intro s hs1 hS hB k hk
    have hs1' : (s : A) ≠ 1 := fun h' => hs1 (by
      have : s = 1 := Subtype.ext h'
      rw [this, map_one])
    refine mem_Mb_of_commute c s.2 hs1' (fun t ht => ?_) (fun b hb => ?_)
      ((act_apply_eq_iff c.S_le_K).mp hk).symm
    · exact mul_comm_of_act_mul_comm c (s := s) (t := ⟨t, ht⟩) (hS _ ⟨⟨t, ht⟩, rfl⟩)
    · exact comm_of_act_comm c (b := ⟨b, hb⟩) (s := s) (hB _ ⟨⟨b, hb⟩, rfl⟩)
  have hcl : Subgroup.closure ({k : ↥Kb | act Sb c.S_le_K s₁ k = k} ∪
      {k : ↥Kb | act Sb c.S_le_K s₂ k = k}) ≤ Mb.comap Kb.subtype := by
    rw [Subgroup.closure_le]
    rintro k (hk | hk)
    · exact key s₁ h1 hcS₁ hcB₁ k hk
    · exact key s₂ h2 hcS₂ hcB₂ k hk
  rw [hgen] at hcl
  exact c.not_le fun k hk => hcl (Subgroup.mem_top ⟨k, hk⟩)

theorem kgStep6NoncycE3_of_inputs (h : KGNoncycCentE3) : KGStep6NoncycE3 := by
  intro A _ _ p Kb Sb Bb Mb z c hc hbot hnc hK3
  exact false_of_cent_nc3 h c hc hbot hnc hK3

theorem pRank_three_img_le {H D : Subgroup A} [(D.subgroupOf H).Normal] (L : Subgroup A)
    (hD2 : IsPGroup 2 D) (hH : CFSG.Open.pRank 3 H ≤ 3) :
    CFSG.Open.pRank 3 (KGC.img H D L) ≤ 3 := by
  have h1 : CFSG.Open.pRank 3 (KGC.img H D L) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (KGC.QA H D)) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  have hD2' : IsPGroup 2 (D.subgroupOf H) := hD2.comap_subtype
  have hD3 : ¬ 3 ∣ Nat.card (D.subgroupOf H) :=
    CFSG.QuasithinUnique.K1.not_dvd_card_of_isPGroup_two hD2' Nat.prime_three (by norm_num)
  have h2 := CFSG.QuasithinUnique.K1.pRank_top_quotient_le H (D.subgroupOf H) Nat.prime_three hD3
  exact h1.trans (h2.trans hH)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
