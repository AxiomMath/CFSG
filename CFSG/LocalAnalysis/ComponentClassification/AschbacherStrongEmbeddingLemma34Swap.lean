module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

@[expose] def Permutes (A₁ A₂ : Subgroup G) (g : G) : Prop :=
  (rightConjugate A₁ g = A₁ ∧ rightConjugate A₂ g = A₂) ∨
    (rightConjugate A₁ g = A₂ ∧ rightConjugate A₂ g = A₁)

@[expose] def pairStabilizer (A₁ A₂ : Subgroup G) : Subgroup G where
  carrier := {g | Permutes A₁ A₂ g}
  mul_mem' := by
    intro a b ha hb
    change Permutes A₁ A₂ a at ha
    change Permutes A₁ A₂ b at hb
    change Permutes A₁ A₂ (a * b)
    unfold Permutes at *
    simp only [← rightConjugate_mul]
    rcases ha with ⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩ <;> rcases hb with ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩
    · exact Or.inl ⟨by rw [ha₁, hb₁], by rw [ha₂, hb₂]⟩
    · exact Or.inr ⟨by rw [ha₁, hb₁], by rw [ha₂, hb₂]⟩
    · exact Or.inr ⟨by rw [ha₁, hb₂], by rw [ha₂, hb₁]⟩
    · exact Or.inl ⟨by rw [ha₁, hb₂], by rw [ha₂, hb₁]⟩
  one_mem' := Or.inl ⟨rightConjugate_one A₁, rightConjugate_one A₂⟩
  inv_mem' := by
    intro a ha
    change Permutes A₁ A₂ a at ha
    change Permutes A₁ A₂ a⁻¹
    unfold Permutes at *
    rcases ha with ⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩
    · refine Or.inl ⟨?_, ?_⟩
      · conv_lhs => rw [← ha₁]
        exact rightConjugate_inv_cancel A₁ a
      · conv_lhs => rw [← ha₂]
        exact rightConjugate_inv_cancel A₂ a
    · refine Or.inr ⟨?_, ?_⟩
      · conv_lhs => rw [← ha₂]
        exact rightConjugate_inv_cancel A₂ a
      · conv_lhs => rw [← ha₁]
        exact rightConjugate_inv_cancel A₁ a

theorem mem_pairStabilizer_iff {A₁ A₂ : Subgroup G} {g : G} :
    g ∈ pairStabilizer A₁ A₂ ↔ Permutes A₁ A₂ g :=
  Iff.rfl

theorem rightConjugate_le_iff {X Y : Subgroup G} {g : G} :
    rightConjugate X g ≤ Y ↔ ∀ x ∈ X, g⁻¹ * x * g ∈ Y := by
  constructor
  · intro h x hx
    apply h
    rw [mem_rightConjugate_iff]
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hx
  · intro h y hy
    rw [mem_rightConjugate_iff] at hy
    have := h _ hy
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using this

theorem mem_normalizer_of_conj_subset [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [← rightConjugate_eq_self_iff]
  exact Subgroup.eq_of_le_of_card_ge (rightConjugate_le_iff.mpr h)
    (rightConjugate_card A g).ge

theorem mem_pairStabilizer_of_mem_one {A₁ A₂ : Subgroup G} (hc : ⁅A₁, A₂⁆ = ⊥) {a : G}
    (ha : a ∈ A₁) : a ∈ pairStabilizer A₁ A₂ := by
  refine Or.inl ⟨(rightConjugate_eq_self_iff A₁ a).mpr (Subgroup.le_normalizer ha), ?_⟩
  rw [rightConjugate_eq_self_iff, Subgroup.mem_normalizer_iff'']
  intro b
  have hab : ∀ b ∈ A₂, a⁻¹ * b * a = b := fun b hb => by
    rw [mul_assoc, ← (commute_of_comm hc ha hb).eq, inv_mul_cancel_left]
  constructor
  · intro hb
    rw [hab b hb]
    exact hb
  · intro hb
    have h1 : a⁻¹ * b * a ∈ A₂ := hb
    have h2 := hab _ h1
    have : b = a⁻¹ * b * a := by
      calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * (a⁻¹ * b * a) * a) * a⁻¹ := by rw [h2]
        _ = a⁻¹ * b * a := by group
    rw [this]
    exact h1

theorem mem_pairStabilizer_of_mem_two {A₁ A₂ : Subgroup G} (hc : ⁅A₁, A₂⁆ = ⊥) {a : G}
    (ha : a ∈ A₂) : a ∈ pairStabilizer A₁ A₂ := by
  have hc' : ⁅A₂, A₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc
  rcases mem_pairStabilizer_of_mem_one hc' ha with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₂, h₁⟩
  · exact Or.inr ⟨h₂, h₁⟩

theorem exists_mem_normalizer_of_four_le [Finite G] {A₁ A₂ Y : Subgroup G}
    (hY : Y ≤ pairStabilizer A₁ A₂) (hcard : 4 ≤ Nat.card Y) :
    ∃ y ∈ Y, y ≠ 1 ∧ y ∈ Subgroup.normalizer (A₁ : Set G) := by
  have hne : Y ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    omega
  obtain ⟨a, haY, ha1⟩ := (Subgroup.bot_or_exists_ne_one Y).resolve_left hne
  obtain ⟨b, hbY, hb⟩ : ∃ b ∈ Y, b ∉ ({1, a, a⁻¹} : Set G) := by
    by_contra hcon
    have hsub : (Y : Set G) ⊆ {1, a, a⁻¹} := fun b hb => by
      by_contra h
      exact hcon ⟨b, hb, h⟩
    have h1 : Nat.card Y ≤ ({1, a, a⁻¹} : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a, a⁻¹} : Set G).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]
    omega
  have hb1 : b ≠ 1 := fun h => hb (by simp [h])
  have hba : b ≠ a⁻¹ := fun h => hb (by simp [h])
  have hrel : ∀ g ∈ Y, g ∉ Subgroup.normalizer (A₁ : Set G) →
      rightConjugate A₁ g = A₂ ∧ rightConjugate A₂ g = A₁ := by
    intro g hg hgN
    rcases hY hg with ⟨h₁, -⟩ | h
    · exact absurd ((rightConjugate_eq_self_iff A₁ g).mp h₁) hgN
    · exact h
  by_cases haN : a ∈ Subgroup.normalizer (A₁ : Set G)
  · exact ⟨a, haY, ha1, haN⟩
  by_cases hbN : b ∈ Subgroup.normalizer (A₁ : Set G)
  · exact ⟨b, hbY, hb1, hbN⟩
  refine ⟨a * b, Y.mul_mem haY hbY, fun h => hba (eq_inv_of_mul_eq_one_right h), ?_⟩
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, (hrel a haY haN).1,
    (hrel b hbY hbN).2]

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem Hyp.sylow_le_normalizer_of_le (h : Hyp S A₁ A₂) (h21 : A₂ ≤ A₁) :
    (S : Subgroup G) ≤ Subgroup.normalizer (A₁ : Set G) := by
  by_contra hcon
  let N := (S : Subgroup G) ⊓ Subgroup.normalizer (A₁ : Set G)
  have hNS : N ≤ S := inf_le_left
  have hNne : N ≠ S := fun heq => hcon (heq ▸ inf_le_right)
  obtain ⟨s, hsS, hsN, hsnorm⟩ :=
    exists_mem_normalizer_not_mem S.isPGroup' hNS hNne
  have hA₁N : A₁ ≤ N := le_inf h.le_one (Subgroup.le_normalizer)
  have hconjN : ∀ a ∈ A₁, s⁻¹ * a * s ∈ N := fun a ha =>
    (Subgroup.mem_normalizer_iff''.mp hsnorm a).mp (hA₁N ha)
  obtain ⟨a₀, ha₀, ha₀1⟩ := (Subgroup.bot_or_exists_ne_one A₁).resolve_left h.ne_bot_one
  obtain ⟨-, hsub⟩ := h.conj_subset_of_normalizer (X := (A₁ : Set G))
    Set.subset_union_left (fun a ha => (hconjN a ha).1) ha₀ ha₀1 (Or.inl (hconjN a₀ ha₀).2)
  apply hsN
  refine ⟨hsS, mem_normalizer_of_conj_subset fun a ha => ?_⟩
  rcases hsub a ha with h' | h'
  · exact h'
  · exact h21 h'

theorem Hyp.conj_mem_of_le (h : Hyp S A₁ A₂) (h21 : A₂ ≤ A₁) {a g : G} (ha : a ∈ A₁)
    (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : g⁻¹ * a * g ∈ A₁ := by
  rcases h.conj_mem_of_mem_normalizer (Or.inl ha) hS
    (Or.inl (h.sylow_le_normalizer_of_le h21 hS)) with h' | h'
  · exact h'
  · exact h21 h'

theorem Hyp.sylow_le_pairStabilizer (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) :
    (S : Subgroup G) ≤ pairStabilizer A₁ A₂ := by
  by_contra hcon
  let N := (S : Subgroup G) ⊓ pairStabilizer A₁ A₂
  have hNS : N ≤ S := inf_le_left
  have hNne : N ≠ S := fun heq => hcon (heq ▸ inf_le_right)
  obtain ⟨s, hsS, hsN, hsnorm⟩ :=
    exists_mem_normalizer_not_mem S.isPGroup' hNS hNne
  have key : ∀ {B : Subgroup G}, B ≤ S → (∀ b ∈ B, b ∈ pairStabilizer A₁ A₂) →
      (B : Set G) ⊆ (A₁ : Set G) ∪ A₂ → 4 ≤ Nat.card B →
      rightConjugate B s ≤ A₁ ∨ rightConjugate B s ≤ A₂ := by
    intro B hBS hBstab hBU hBcard
    have hconjN : ∀ b ∈ B, s⁻¹ * b * s ∈ N := fun b hb =>
      (Subgroup.mem_normalizer_iff''.mp hsnorm b).mp ⟨hBS hb, hBstab b hb⟩
    have hYstab : rightConjugate B s ≤ pairStabilizer A₁ A₂ :=
      rightConjugate_le_iff.mpr fun b hb => (hconjN b hb).2
    obtain ⟨y, hyB, hy1, hyN⟩ := exists_mem_normalizer_of_four_le hYstab
      ((rightConjugate_card B s).symm ▸ hBcard)
    rw [mem_rightConjugate_iff] at hyB
    have hy1' : s * y * s⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    have hyeq : s⁻¹ * (s * y * s⁻¹) * s = y := by group
    obtain ⟨-, hsub⟩ := h.conj_subset_of_normalizer (X := (B : Set G)) hBU
      (fun b hb => (hconjN b hb).1) hyB hy1' (Or.inl (by rw [hyeq]; exact hyN))
    apply le_or_le_of_subset_union
    intro x hx
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hx
    have := hsub _ hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * s = x by group] at this
  have hcard₁ : 4 ≤ Nat.card A₁ := by
    obtain ⟨E, hE, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A₁
    have h4 : 4 ≤ Nat.card E := by
      rw [hEcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ pRank 2 A₁ := Nat.pow_le_pow_right (by norm_num) h.rank_one
    exact h4.trans (Subgroup.card_le_of_le hE)
  have hcard₂ : 4 ≤ Nat.card A₂ := by
    obtain ⟨E, hE, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A₂
    have h4 : 4 ≤ Nat.card E := by
      rw [hEcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ pRank 2 A₂ := Nat.pow_le_pow_right (by norm_num) h.rank_two
    exact h4.trans (Subgroup.card_le_of_le hE)
  have k₁ := key h.le_one (fun b hb => mem_pairStabilizer_of_mem_one h.comm hb)
    Set.subset_union_left hcard₁
  have k₂ := key h.le_two (fun b hb => mem_pairStabilizer_of_mem_two h.comm hb)
    Set.subset_union_right hcard₂
  have hc₁ := rightConjugate_card A₁ s
  have hc₂ := rightConjugate_card A₂ s
  apply hsN
  refine ⟨hsS, ?_⟩
  rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂
  ·
    exfalso
    have he : rightConjugate A₁ s = A₁ := Subgroup.eq_of_le_of_card_ge k₁ hc₁.ge
    apply h21
    intro x hx
    have hx' : s⁻¹ * x * s ∈ rightConjugate A₂ s := by
      rw [mem_rightConjugate_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hx
    have h1 : s⁻¹ * x * s ∈ rightConjugate A₁ s := by rw [he]; exact k₂ hx'
    rw [mem_rightConjugate_iff] at h1
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h1
  · exact Or.inl ⟨Subgroup.eq_of_le_of_card_ge k₁ hc₁.ge,
      Subgroup.eq_of_le_of_card_ge k₂ hc₂.ge⟩
  · have h12' : Nat.card A₁ ≤ Nat.card A₂ := hc₁ ▸ Subgroup.card_le_of_le k₁
    have h21' : Nat.card A₂ ≤ Nat.card A₁ := hc₂ ▸ Subgroup.card_le_of_le k₂
    exact Or.inr ⟨Subgroup.eq_of_le_of_card_ge k₁ (by omega),
      Subgroup.eq_of_le_of_card_ge k₂ (by omega)⟩
  ·
    exfalso
    have he : rightConjugate A₂ s = A₂ := Subgroup.eq_of_le_of_card_ge k₂ hc₂.ge
    apply h12
    intro x hx
    have hx' : s⁻¹ * x * s ∈ rightConjugate A₁ s := by
      rw [mem_rightConjugate_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hx
    have h1 : s⁻¹ * x * s ∈ rightConjugate A₂ s := by rw [he]; exact k₁ hx'
    rw [mem_rightConjugate_iff] at h1
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using h1

theorem Hyp.pairStabilizer_le (h : Hyp S A₁ A₂) :
    pairStabilizer A₁ A₂ ≤ overlapClosure A₁ A₂ := by
  intro g hg
  rcases hg with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact normalizer_le_overlapClosure_one h.ne_bot_one
      ((rightConjugate_eq_self_iff A₁ g).mp h₁)
  · refine mem_overlapClosure (Or.inl rfl) (Or.inr rfl) ?_
    rw [h₁, inf_idem]
    exact h.ne_bot_two

theorem Hyp.sylow_le_overlapClosure (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) :
    (S : Subgroup G) ≤ overlapClosure A₁ A₂ :=
  (h.sylow_le_pairStabilizer h12 h21).trans h.pairStabilizer_le

theorem Hyp.sylow_le_overlapClosure_of_le (h : Hyp S A₁ A₂) (h21 : A₂ ≤ A₁) :
    (S : Subgroup G) ≤ overlapClosure A₁ A₂ :=
  (h.sylow_le_normalizer_of_le h21).trans (normalizer_le_overlapClosure_one h.ne_bot_one)

theorem Hyp.fixesOnly_of_card (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    {X : Subgroup G} (hX : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂) (hcard : 4 ≤ Nat.card X) :
    FixesOnly (overlapClosure A₁ A₂) X := by
  intro g hg
  have hSH := h.sylow_le_overlapClosure h12 h21
  have hXS : X ≤ S := fun x hx => by
    rcases hX hx with hx | hx
    · exact h.le_one hx
    · exact h.le_two hx
  have hP : IsPGroup 2 (rightConjugate X g) :=
    (S.isPGroup'.to_le hXS).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_sylow hSH (rightConjugate_le_iff.mpr hg) hP
  have hXS' : ∀ x ∈ X, (g * k)⁻¹ * x * (g * k) ∈ (S : Subgroup G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ rightConjugate X g := by
      rw [mem_rightConjugate_iff]
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hx
    have := hkS _ hx'
    simpa only [mul_inv_rev, mul_assoc] using this
  have hYstab : rightConjugate X (g * k) ≤ pairStabilizer A₁ A₂ :=
    (rightConjugate_le_iff.mpr hXS').trans (h.sylow_le_pairStabilizer h12 h21)
  obtain ⟨y, hyX, hy1, hyN⟩ := exists_mem_normalizer_of_four_le hYstab
    ((rightConjugate_card X (g * k)).symm ▸ hcard)
  rw [mem_rightConjugate_iff] at hyX
  have hy1' : (g * k) * y * (g * k)⁻¹ ≠ 1 := by
    intro h1
    apply hy1
    calc y = (g * k)⁻¹ * ((g * k) * y * (g * k)⁻¹) * (g * k) := by group
      _ = 1 := by rw [h1]; group
  have hyeq : (g * k)⁻¹ * ((g * k) * y * (g * k)⁻¹) * (g * k) = y := by group
  obtain ⟨hgk, -⟩ := h.conj_subset_of_normalizer (X := (X : Set G)) hX hXS' hyX hy1'
    (Or.inl (by rw [hyeq]; exact hyN))
  have := (overlapClosure A₁ A₂).mul_mem hgk ((overlapClosure A₁ A₂).inv_mem hk)
  rwa [mul_inv_cancel_right] at this

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
