module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Lemma47

variable {G : Type} [Group G] [Finite G]

theorem isElemTwo_sup {E₁ E₂ : Subgroup G} (h₁ : GrSLit.IsElemTwo E₁)
    (h₂ : GrSLit.IsElemTwo E₂) (hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) :
    GrSLit.IsElemTwo (E₁ ⊔ E₂) := by
  obtain ⟨-, hset⟩ := GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc
  have hmem : ∀ g ∈ E₁ ⊔ E₂, ∃ a ∈ E₁, ∃ b ∈ E₂, g = a * b := by
    intro g hg
    have hg' : g ∈ ((E₁ ⊔ E₂ : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hg
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem g' hg'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h₁.1 a ha a' ha', h₂.1 b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hc a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hg
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hc a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h₁.2 a ha, h₂.2 b hb, one_mul]

omit [Finite G] in
theorem center_le_zStarIn (K : Subgroup G) :
    (center ↥K).map K.subtype ≤ GrSLit.zStarIn K := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  show y ∈ Open.fusionZStar ↥K
  rw [GSThmB.OddQuot.mem_fusionZStar_iff]
  intro m
  have hy' : y ∈ center ↥K := hy
  rw [commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hy') m).symm]
  exact one_mem _

theorem exists_elemTwo_gt_sixteen {K₁ K₂ : Subgroup G} (hK₁ : IsComponent K₁)
    (hK₂ : IsComponent K₂) (hne : K₁ ≠ K₂) {x : G} (hx2 : x * x = 1)
    {E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ K₁ ⊓ centralizer {x}) (hE₂ : E₂ ≤ K₂ ⊓ centralizer {x})
    (hE₁e : GrSLit.IsElemTwo E₁) (hE₂e : GrSLit.IsElemTwo E₂)
    (hZ₁ : Nat.card ↥(E₁ ⊓ GrSLit.zStarIn K₁) = 4)
    (hc₁ : (x ∈ GrSLit.withKernel K₁ → Nat.card E₁ = 16) ∧
      (x ∉ GrSLit.withKernel K₁ → Nat.card E₁ = 8))
    (hc₂ : (x ∈ GrSLit.withKernel K₂ → Nat.card E₂ = 16) ∧
      (x ∉ GrSLit.withKernel K₂ → Nat.card E₂ = 8)) :
    ∃ E : Subgroup G, E ≤ centralizer {x} ∧ GrSLit.IsElemTwo E ∧ 16 < Nat.card E := by
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hne
  have hK21 : K₂ ≤ centralizer (K₁ : Set G) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hK21 (hE₂ hb).1) a (hE₁ ha).1)
  have hE := isElemTwo_sup hE₁e hE₂e hc
  obtain ⟨hprod, -⟩ := GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc
  have hinf : E₁ ⊓ E₂ ≤ E₁ ⊓ GrSLit.zStarIn K₁ := by
    refine le_inf inf_le_left fun y hy => ?_
    have hyK₁ : y ∈ K₁ := (hE₁ hy.1).1
    refine center_le_zStarIn K₁ ⟨⟨y, hyK₁⟩, ?_, rfl⟩
    show (⟨y, hyK₁⟩ : ↥K₁) ∈ center ↥K₁
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp (hK21 (hE₂ hy.2).1)) g g.2)
  have hle4 : Nat.card ↥(E₁ ⊓ E₂) ≤ 4 := hZ₁ ▸ Subgroup.card_le_of_le hinf
  have hpos : 0 < Nat.card ↥(E₁ ⊓ E₂) := Nat.card_pos
  have hEt : E₁ ⊔ E₂ ≤ centralizer {x} := sup_le (hE₁.trans inf_le_right) (hE₂.trans inf_le_right)
  by_cases hw₁ : x ∈ GrSLit.withKernel K₁
  · refine ⟨E₁ ⊔ E₂, hEt, hE, ?_⟩
    have h1 := hc₁.1 hw₁
    have h2 : 8 ≤ Nat.card E₂ := by
      by_cases hw₂ : x ∈ GrSLit.withKernel K₂
      · rw [hc₂.1 hw₂]; norm_num
      · rw [hc₂.2 hw₂]
    rw [h1] at hprod
    nlinarith
  by_cases hw₂ : x ∈ GrSLit.withKernel K₂
  · refine ⟨E₁ ⊔ E₂, hEt, hE, ?_⟩
    have h1 := hc₂.1 hw₂
    have h2 := hc₁.2 hw₁
    rw [h1, h2] at hprod
    nlinarith
  have h1 := hc₁.2 hw₁
  have h2 := hc₂.2 hw₂
  have hx : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) fun h0 =>
    hw₁ (h0 ▸ one_mem _)
  have hK₂core : K₂ ≤ coreActionKernel K₁ := fun g hg => by
    refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
    · exact (Subgroup.centralizer_le_normalizer (K₁ : Set G)) (hK21 hg)
    · have hjg : j * g = g * j := (mem_centralizer_iff.mp (hK21 hg)) j hj
      rw [show j⁻¹ * g⁻¹ * j * g = 1 by
        calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
          _ = j⁻¹ * g⁻¹ * (g * j) := by rw [hjg]
          _ = 1 := by group]
      exact one_mem _
  have hxE : x ∉ E₁ ⊔ E₂ := fun hxE =>
    hw₁ ((sup_le_sup (hE₁.trans inf_le_left) ((hE₂.trans inf_le_left).trans hK₂core)) hxE)
  have hxc : ∀ a ∈ E₁ ⊔ E₂, a * x = x * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (hEt ha)
  refine ⟨(E₁ ⊔ E₂) ⊔ zpowers x, sup_le hEt ?_, isElemTwo_sup_zpowers hE hxc hx2, ?_⟩
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  · rw [card_sup_zpowers hxc hx hxE]
    rw [h1, h2] at hprod
    nlinarith

end Lemma47

end CFSG.ComponentClassification.HarrisLit
