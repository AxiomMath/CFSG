module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification.FooteLit

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem exists_isSylowOf_ge_of_le {X A : Subgroup G} (hAX : A ≤ X) (hA : IsPGroup p A) :
    ∃ B : Subgroup G, IsSylowOf p B X ∧ A ≤ B := by
  have hA' : IsPGroup p (A.subgroupOf X) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup X).map X.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAX ha⟩, hQ ha, rfl⟩

theorem exists_conj_le_of_isSylowOf {T X A : Subgroup G} (hT : IsSylowOf p T X) (hAX : A ≤ X)
    (hA : IsPGroup p A) : ∃ k ∈ X, ∀ a ∈ A, k⁻¹ * a * k ∈ T := by
  obtain ⟨B, hB, hAB⟩ := exists_isSylowOf_ge_of_le hAX hA
  obtain ⟨k, hkX, hk⟩ := hT.exists_mem_conj hB
  exact ⟨k, hkX, fun a ha => (hk a).mp (hAB ha)⟩

theorem exists_mem_normalizer_of_lt {T P : Subgroup G} (hP : IsPGroup p P) (hTP : T < P) :
    ∃ x ∈ P, x ∉ T ∧ x ∈ normalizer (T : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  set W := T.subgroupOf P with hW
  have hWtop : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hTP.not_ge fun x hx => ?_
    have h1 : (⟨x, hx⟩ : P) ∈ W := h ▸ mem_top _
    exact h1
  obtain ⟨y, hyN, hyW⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent W hWtop)
  refine ⟨y, y.2, hyW, mem_normalizer_iff.mpr fun t => ?_⟩
  constructor
  · intro ht
    have h1 : (⟨t, hTP.le ht⟩ : P) ∈ W := ht
    have h2 := (mem_normalizer_iff.mp hyN _).mp h1
    exact h2
  · intro ht
    have htP : t ∈ P := by
      have h1 : (y : G) * t * (y : G)⁻¹ ∈ P := hTP.le ht
      have h2 : t = (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G) := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem y.2) h1) y.2
    have h1 : y * (⟨t, htP⟩ : P) * y⁻¹ ∈ W := ht
    exact (mem_normalizer_iff.mp hyN _).mpr h1

theorem isSylowOf_of_normalizer_le {T X Y : Subgroup G} (hT : IsSylowOf p T X) (hXY : X ≤ Y)
    (hN : Y ⊓ normalizer (T : Set G) ≤ X) : IsSylowOf p T Y := by
  obtain ⟨T', hT', hTT'⟩ := exists_isSylowOf_ge_of_le (hT.le.trans hXY) hT.isPGroup
  rcases eq_or_lt_of_le hTT' with h | h
  · rw [h]
    exact hT'
  exfalso
  obtain ⟨x, hxT', hxT, hxN⟩ := exists_mem_normalizer_of_lt hT'.isPGroup h
  set R := T' ⊓ normalizer (T : Set G) with hR
  have hRX : R ≤ X := fun y hy => hN (mem_inf.mpr ⟨hT'.le (mem_inf.mp hy).1, (mem_inf.mp hy).2⟩)
  have hTR : T ≤ R := le_inf hTT' le_normalizer
  have hRp : IsPGroup p R := hT'.isPGroup.to_le inf_le_left
  have hRT : R = T := hT.eq_of_le hTR hRX hRp
  exact hxT (hRT ▸ mem_inf.mpr ⟨hxT', hxN⟩)

theorem exists_isSylowOf_le_normalizer {T X Y : Subgroup G} (hT : IsSylowOf p T X)
    (hXY : X ≤ Y) (hYX : Y ≤ normalizer (X : Set G)) :
    ∃ P : Subgroup G, IsSylowOf p P Y ∧ T ≤ P ∧ P ≤ normalizer (T : Set G) := by
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_ge_of_le (hT.le.trans hXY) hT.isPGroup
  have h1 : IsSylowOf p (P ⊓ X) X := hP.inf_of_le_normalizer hXY hYX
  have h2 : P ⊓ X = T := hT.eq_of_le (le_inf hTP hT.le) inf_le_right h1.isPGroup
  refine ⟨P, hP, hTP, fun g hg => ?_⟩
  rw [← h2]
  have hgX := hYX (hP.le hg)
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hx).1) (inv_mem hg),
      (mem_normalizer_iff.mp hgX x).mp (mem_inf.mp hx).2⟩
  · have hxP : x ∈ P := by
      have h3 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [h3]
      exact mul_mem (mul_mem (inv_mem hg) (mem_inf.mp hx).1) hg
    exact mem_inf.mpr ⟨hxP, (mem_normalizer_iff.mp hgX x).mpr (mem_inf.mp hx).2⟩

end CFSG.ComponentClassification.FooteLit
