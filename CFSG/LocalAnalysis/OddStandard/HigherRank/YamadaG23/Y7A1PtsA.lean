module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CfgB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6PtsA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

theorem y7a_t_mem_Up (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t ∈ y6Up A V t := by
  refine ⟨1, one_mem A, ?_, 1, one_mem V, ?_⟩
  · simp
  · group

theorem y7a_Up_sub (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ y6Up A V t, x ∈ A ⊔ C0 ∧ x ∉ A ⊔ V := by
  rintro x ⟨a, ha, -, v, hv, rfl⟩
  refine ⟨mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (y7a_t_mem_C0 h)))
    (mem_sup_right (y7a_V_le_C0 h hv)), ?_⟩
  intro hx
  exact y7a_t_not_mem_AV h (by
    have ht : t = a⁻¹ * (a * t * v) * v⁻¹ := by group
    rw [ht]
    exact mul_mem (mul_mem (mem_sup_left (inv_mem ha)) hx) (mem_sup_right (inv_mem hv)))

theorem y7a_Um_sub (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ y6Um A V z t, x ∈ A ⊔ C0 ∧ x ∉ A ⊔ V := by
  rintro x ⟨a, ha, -, v, hv, rfl⟩
  refine ⟨mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (y7a_t_mem_C0 h)))
    (mem_sup_right (y7a_V_le_C0 h hv)), ?_⟩
  intro hx
  exact y7a_t_not_mem_AV h (by
    have ht : t = a⁻¹ * (a * t * v) * v⁻¹ := by group
    rw [ht]
    exact mul_mem (mul_mem (mem_sup_left (inv_mem ha)) hx) (mem_sup_right (inv_mem hv)))

theorem y7a_C1_split (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ C0, x ∈ A ⊔ V ∨ x ∈ y6Um A V z t ∨ x ∈ y6Up A V t := by
  intro x hx
  rcases y7a_C1_elems h x hx with ⟨a, ha, v, hv, rfl⟩ | ⟨a, ha, v, hv, rfl⟩
  · exact Or.inl (mul_mem (mem_sup_left ha) (mem_sup_right hv))
  · have ha' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at ha
    rcases y6q8_sq_cases h.cfg.rel a ha' with h1 | hz
    · exact Or.inr (Or.inr ⟨a, ha, h1, v, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha, hz, v, hv, rfl⟩)

theorem y7a_Up_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ y6Up A V t, ∀ v ∈ V, x * v ∈ y6Up A V t := by
  rintro x ⟨a, ha, ha1, v₀, hv₀, rfl⟩ v hv
  exact ⟨a, ha, ha1, v₀ * v, mul_mem hv₀ hv, by group⟩

theorem y7a_Um_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ y6Um A V z t, ∀ v ∈ V, x * v ∈ y6Um A V z t := by
  rintro x ⟨a, ha, haz, v₀, hv₀, rfl⟩ v hv
  exact ⟨a, ha, haz, v₀ * v, mul_mem hv₀ hv, by group⟩

theorem y7a_U16_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ w ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}, ∀ v ∈ V, w * v ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} := by
  rintro w ⟨hwC, hwAV⟩ v hv
  refine ⟨mul_mem hwC (mem_sup_right (y7a_V_le_C0 h hv)), ?_⟩
  intro hx
  exact hwAV (by
    have hw : w = (w * v) * v⁻¹ := by group
    rw [hw]
    exact mul_mem hx (mem_sup_right (inv_mem hv)))

theorem y7a_card_U16 [Finite G] (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    Nat.card ↥{w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} = 16 * Nat.card ↥V := by
  have hsub : ((A ⊔ V : Subgroup G) : Set G) ⊆ ((A ⊔ C0 : Subgroup G) : Set G) :=
    fun x hx => y7a_AV_le_C1 h hx
  have hL : Nat.card ↥{w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} =
      (((A ⊔ C0 : Subgroup G) : Set G) \ ((A ⊔ V : Subgroup G) : Set G)).ncard :=
    Nat.card_coe_set_eq _
  rw [hL, Set.ncard_sdiff hsub]
  have h1 : ((A ⊔ C0 : Subgroup G) : Set G).ncard = 128 := by
    rw [← Nat.card_coe_set_eq]; exact y6_card_C1 h.cfg
  have h2 : ((A ⊔ V : Subgroup G) : Set G).ncard = 64 := by
    rw [← Nat.card_coe_set_eq]; exact y7a_card_AV h
  rw [h1, h2, y7a_card_V h]

private lemma y7a_at_mem_U16 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {a : G} (ha : a ∈ A) :
    a * t ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} := by
  have ha' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at ha
  rcases y6q8_sq_cases h.cfg.rel a ha' with h1 | hz
  · exact y7a_Up_sub h (a * t) ⟨a, ha, h1, 1, one_mem V, by group⟩
  · exact y7a_Um_sub h (a * t) ⟨a, ha, hz, 1, one_mem V, by group⟩

private lemma y7a_A_le_gen (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    A ≤ closure ({w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} ∪ (V : Set G)) := by
  intro a ha
  have hat : a * t ∈ closure ({w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} ∪ (V : Set G)) :=
    Subgroup.subset_closure (Or.inl (y7a_at_mem_U16 h ha))
  have ht : t ∈ closure ({w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} ∪ (V : Set G)) :=
    Subgroup.subset_closure (Or.inl (y7a_Up_sub h t (y7a_t_mem_Up h)))
  have haeq : a = (a * t) * t⁻¹ := by group
  rw [haeq]
  exact mul_mem hat (inv_mem ht)

theorem y7a_gen_U16 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    closure ({w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} ∪ (V : Set G)) = A ⊔ C0 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hx.1
    · exact mem_sup_right (y7a_V_le_C0 h hx)
  · intro x hx
    have hAV_le : A ⊔ V ≤ closure ({w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} ∪ (V : Set G)) :=
      sup_le (y7a_A_le_gen h) (fun v hv => Subgroup.subset_closure (Or.inr hv))
    rcases y7a_C1_split h x hx with hAV | hUm | hUp
    · exact hAV_le hAV
    · exact Subgroup.subset_closure (Or.inl (y7a_Um_sub h x hUm))
    · exact Subgroup.subset_closure (Or.inl (y7a_Up_sub h x hUp))

end CFSG.OddStandard.HigherRank.YamadaG23
