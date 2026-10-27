module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGNonLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGNonDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNon

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem mem_normalizer_zpowers_of_commute {a b : A} (h : b * a = a * b) :
    b ∈ normalizer (zpowers a : Set A) :=
  KGB.mem_normalizer_of_commute fun t ht => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (show Commute b a from h) i).eq

theorem mem_Mb_of_commute (c : KQCfg A p Kb Sb Bb Mb z) {s : A} (hs : s ∈ Sb) (hs1 : s ≠ 1)
    (hS : ∀ t ∈ Sb, t * s = s * t) (hB : ∀ b ∈ Bb, b * s = s * b) {x : A}
    (hx : x * s = s * x) : x ∈ Mb :=
  c.cover (zpowers s) (zpowers_le.mpr hs) (fun h => hs1 (zpowers_eq_bot.mp h))
    (fun t ht => mem_normalizer_zpowers_of_commute (hS t ht))
    (fun b hb => mem_normalizer_zpowers_of_commute (hB b hb))
    (mem_normalizer_zpowers_of_commute hx)

theorem act_range_le_normalizer (c : KQCfg A p Kb Sb Bb Mb z) :
    (act Bb c.B_le_K).range ≤ normalizer ((act Sb c.S_le_K).range : Set (MulAut ↥Kb)) := by
  have key : ∀ (b : ↥Bb) {τ : MulAut ↥Kb}, τ ∈ (act Sb c.S_le_K).range →
      act Bb c.B_le_K b * τ * (act Bb c.B_le_K b)⁻¹ ∈ (act Sb c.S_le_K).range := by
    intro b τ hτ
    obtain ⟨s, rfl⟩ := hτ
    refine ⟨⟨(b : A) * s * (b : A)⁻¹, (mem_normalizer_iff.mp (c.B_le_S b.2) s).mp s.2⟩, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    exact act_conj c b s
  rintro _ ⟨b, rfl⟩
  rw [mem_normalizer_iff]
  intro τ
  refine ⟨key b, fun hτ => ?_⟩
  have h := key b⁻¹ hτ
  rw [map_inv, inv_inv] at h
  have e : (act Bb c.B_le_K b)⁻¹ * (act Bb c.B_le_K b * τ * (act Bb c.B_le_K b)⁻¹) *
      act Bb c.B_le_K b = τ := by group
  rwa [e] at h

theorem false_of_cent (h : KGNoncycCent) (c : KQCfg A p Kb Sb Bb Mb z)
    (hc : KGStep4Concl A Kb Sb) (hbot : Sb ⊓ Kb = ⊥) (hnc : ¬ IsCyclic ↥Sb) : False := by
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
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, h1, h2, hcS₁, hcS₂, hcB₁, hcB₂, hgen⟩ :=
    h ↥Kb p c.prime c.five_le c.simple c.nonab hc.1 (act Sb c.S_le_K).range
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

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNon

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kgStep6Noncyc_of_inputs (h : KGNoncycCent) : KGStep6Noncyc := by
  intro A _ _ p Kb Sb Bb Mb z c hc hbot hnc
  exact KGNon.false_of_cent h c hc hbot hnc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
