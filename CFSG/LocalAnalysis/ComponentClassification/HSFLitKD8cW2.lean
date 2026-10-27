module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cE

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

@[expose] def inE0h (a : MC) : Bool := inE 0 a && inE 6 a

theorem card_Q0h : (Finset.univ.filter fun a : MC => MC.inQ0 a = true).card = 32 := by
  decide +kernel

theorem Q0h_cosets : ∀ a : MC, MC.inQ0 a = true → inE0h a = true ∨
    inE0h (MC.w₁⁻¹ * a) = true ∨ inE0h (MC.w₂⁻¹ * a) = true ∨
    inE0h ((MC.w₁ * MC.w₂)⁻¹ * a) = true := by
  decide +kernel

theorem cosets_ne : inE0h MC.w₂ = false ∧ inE0h (MC.w₁⁻¹ * MC.w₂) = false ∧
    inE0h ((MC.w₁ * MC.w₂)⁻¹ * MC.w₂) = false ∧ inE0h (MC.w₁⁻¹ * (MC.w₁ * MC.w₂)) = false ∧
    inE0h MC.w₁ = false ∧ inE0h (MC.w₂⁻¹ * (MC.w₁ * MC.w₂)) = false ∧
    inE0h (MC.w₁ * MC.w₂) = false := by
  decide +kernel

theorem w1E0_F2 : ∀ a : MC, inE0h (MC.w₁⁻¹ * a) = true → a * a = 1 → inE 7 a = true := by
  decide +kernel

theorem tkv_miss : ∀ a : MC, (InSpan [MC.t, MC.k, MC.v] a ∨ InSpan [MC.t, MC.k, MC.v * MC.t] a) →
    inE0h (MC.w₁⁻¹ * a) = false ∧ inE0h (MC.w₂⁻¹ * a) = false ∧
    inE0h ((MC.w₁ * MC.w₂)⁻¹ * a) = false := by
  decide +kernel

theorem card_tkv : (Finset.univ.filter fun a : MC => InSpan [MC.t, MC.k, MC.v] a).card = 8 ∧
    (Finset.univ.filter fun a : MC => InSpan [MC.t, MC.k, MC.v * MC.t] a).card = 8 := by
  decide +kernel

namespace Conf

variable (K : Conf S T₁)

theorem E0_eq : S.E0 S.y S.k = K.Ex 0 ⊓ K.Ex 6 := by
  refine eq_of_le_of_card_ge ?_ ?_
  · refine (closure_le _).mpr (Set.insert_subset_iff.mpr ⟨?_, Set.insert_subset_iff.mpr ⟨?_,
      Set.singleton_subset_iff.mpr ?_⟩⟩)
    · rw [← K.ι_z]; exact ⟨K.ι_mem_Ex (by decide +kernel), K.ι_mem_Ex (by decide +kernel)⟩
    · rw [← K.ι_y]; exact ⟨K.ι_mem_Ex (by decide +kernel), K.ι_mem_Ex (by decide +kernel)⟩
    · rw [← K.ι_k]; exact ⟨K.ι_mem_Ex (by decide +kernel), K.ι_mem_Ex (by decide +kernel)⟩
  · have hc : Nat.card (S.E0 S.y S.k) = 8 := K.P.V.F.card_E0
    rw [K.card_inf_Ex, hc]
    decide

theorem mem_E0_iff (a : MC) : K.ι a ∈ S.E0 S.y S.k ↔ inE0h a = true := by
  rw [K.E0_eq, mem_inf, K.mem_Ex, K.mem_Ex]
  constructor
  · rintro ⟨⟨b, hb, hba⟩, ⟨c, hc, hca⟩⟩
    rw [K.ι_injective hba] at hb
    rw [K.ι_injective hca] at hc
    simp [inE0h, hb, hc]
  · intro h
    simp only [inE0h, Bool.and_eq_true] at h
    exact ⟨⟨a, h.1, rfl⟩, ⟨a, h.2, rfl⟩⟩

theorem mem_coset_iff (b a : MC) : (K.ι b)⁻¹ * K.ι a ∈ S.E0 S.y S.k ↔ inE0h (b⁻¹ * a) = true := by
  rw [← map_inv, ← map_mul, K.mem_E0_iff]

noncomputable abbrev Q0X : Subgroup X := S.Q0 S.y S.k K.D₁.w₁ K.D₁.w₂

theorem E0_le_Q0X : S.E0 S.y S.k ≤ K.Q0X := le_sup_left.trans le_sup_left

theorem ι_mem_Q0X {a : MC} (ha : MC.inQ0 a = true) : K.ι a ∈ K.Q0X := by
  refine map_mem_of_inSpan K.ι (MC.Q0_span a ha) fun g hg => ?_
  have hk : S.k ∈ S.E0 S.y S.k := subset_closure (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · rw [K.P.ι_w₂]
    have hy : S.y ∈ K.Q0X := K.E0_le_Q0X (subset_closure (by simp))
    rcases K.P.w₂N_eq with h | h <;> rw [h]
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem hy (mem_sup_right (mem_zpowers _))
  · rw [K.P.ι_w₁, CPair.w₁N_eq]
    refine mul_mem (mem_sup_left (mem_sup_right (mem_zpowers _))) (K.E0_le_Q0X ?_)
    exact (zpowers_le.mpr hk) K.P.cN_mem
  · rw [K.ι_z]; exact K.E0_le_Q0X (subset_closure (by simp))
  · rw [K.ι_y]; exact K.E0_le_Q0X (subset_closure (by simp))
  · rw [K.ι_k]; exact K.E0_le_Q0X hk

theorem card_Q0X : Nat.card K.Q0X = 32 := by
  have h := K.D₁.q0_holds
  rw [K.hq₁] at h
  exact h.2.2.2.2

theorem exists_of_mem_Q0X {x : X} (hx : x ∈ K.Q0X) : ∃ a, MC.inQ0 a = true ∧ K.ι a = x := by
  classical
  set Ss : Set X := K.ι '' ↑(Finset.univ.filter fun a : MC => MC.inQ0 a = true) with hSs
  have hsub : Ss ⊆ (K.Q0X : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at ha
    exact K.ι_mem_Q0X ha.2
  have hQ : (K.Q0X : Set X).ncard = 32 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, K.card_Q0X]
  have hcard : (K.Q0X : Set X).ncard ≤ Ss.ncard := by
    rw [hSs, Set.ncard_image_of_injective _ K.ι_injective, Set.ncard_coe_finset, card_Q0h, hQ]
  have hEq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hx' : x ∈ (K.Q0X : Set X) := hx
  rw [← hEq] at hx'
  obtain ⟨a, ha, rfl⟩ := hx'
  rw [Finset.mem_coe, Finset.mem_filter] at ha
  exact ⟨a, ha.2, rfl⟩

theorem exists_of_mem_C {x : X} (hx : x ∈ K.D₁.Q₁ ⊓ centralizer (K.D₁.D₁₁ : Set X)) :
    ∃ a, (InSpan [MC.t, MC.k, MC.v] a ∨ InSpan [MC.t, MC.k, MC.v * MC.t] a) ∧ K.ι a = x := by
  classical
  have hvN : K.P.V.vN = K.D₁.v ∨ K.P.V.vN = K.D₁.v * t := K.P.V.vN_eq
  obtain ⟨v', hv', hv'span⟩ : ∃ v' : MC, K.ι v' = K.D₁.v ∧
      (∀ a, InSpan [MC.t, MC.k, v'] a →
        InSpan [MC.t, MC.k, MC.v] a ∨ InSpan [MC.t, MC.k, MC.v * MC.t] a) ∧
      (Finset.univ.filter fun a : MC => InSpan [MC.t, MC.k, v'] a).card = 8 := by
    rcases hvN with h | h
    · refine ⟨MC.v, by rw [CPair.ι_v, h], fun a ha => Or.inl ha, card_tkv.1⟩
    · refine ⟨MC.v * MC.t, ?_, fun a ha => Or.inr ha, card_tkv.2⟩
      rw [map_mul, CPair.ι_v, h, K.ι_t, mul_assoc, tt (A := A), mul_one]
  rw [K.D₁.C_eq] at hx
  set Ss : Set X := K.ι '' ↑(Finset.univ.filter fun a : MC => InSpan [MC.t, MC.k, v'] a)
    with hSs
  have hsub : Ss ⊆ (closure {t, S.k, K.D₁.v} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at ha
    refine map_mem_of_inSpan K.ι ha.2 fun g hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [K.ι_t]; exact subset_closure (by simp)
    · rw [K.ι_k]; exact subset_closure (by simp)
    · rw [hv']; exact subset_closure (by simp)
  have hC : (closure {t, S.k, K.D₁.v} : Set X).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, ← K.D₁.C_eq, K.D₁.card_C]
  have hcard : (closure {t, S.k, K.D₁.v} : Set X).ncard ≤ Ss.ncard := by
    rw [hSs, Set.ncard_image_of_injective _ K.ι_injective, Set.ncard_coe_finset, hv'span.2, hC]
  have hEq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hx' : x ∈ (closure {t, S.k, K.D₁.v} : Set X) := hx
  rw [← hEq] at hx'
  obtain ⟨a, ha, rfl⟩ := hx'
  rw [Finset.mem_coe, Finset.mem_filter] at ha
  exact ⟨a, hv'span.1 a ha.2, rfl⟩

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
