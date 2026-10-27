module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitaryFieldData

variable {p f : ℕ} {K : Type*} [Field K]

theorem trace_mem_fixedField (h : UnitaryFieldData p f K) (c : K) :
    h.trace c ∈ h.fixedField := by
  rw [mem_fixedField, trace, map_add, bar_bar, add_comm]

@[expose] noncomputable def traceLin (h : UnitaryFieldData p f K) :
    K →ₗ[h.fixedField] h.fixedField where
  toFun c := ⟨h.trace c, h.trace_mem_fixedField c⟩
  map_add' a b := Subtype.ext (by simp only [trace, map_add, Subfield.coe_add]; ring)
  map_smul' a c := Subtype.ext (by
    have ha : h.bar (a : K) = a := a.2
    change (a : K) * c + h.bar ((a : K) * c) = (a : K) * (c + h.bar c)
    rw [map_mul, ha]
    ring)

@[simp] theorem coe_traceLin (h : UnitaryFieldData p f K) (c : K) :
    (h.traceLin c : K) = h.trace c :=
  rfl

theorem mem_ker_traceLin (h : UnitaryFieldData p f K) {c : K} :
    c ∈ LinearMap.ker h.traceLin ↔ c ∈ h.traceZero := by
  rw [LinearMap.mem_ker, mem_traceZero, Subtype.ext_iff, coe_traceLin, ZeroMemClass.coe_zero]

theorem exists_trace_ne_zero (h : UnitaryFieldData p f K) : ∃ c : K, h.trace c ≠ 0 := by
  by_contra! hz
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have h1 := hz 1
  have h2 := hz c
  simp only [trace, map_one] at h1 h2
  exact hc (by linear_combination h2 - c * h1)

theorem traceLin_surjective (h : UnitaryFieldData p f K) : Function.Surjective h.traceLin := by
  obtain ⟨c, hc⟩ := h.exists_trace_ne_zero
  intro s
  refine ⟨(s / h.traceLin c) • c, ?_⟩
  have ht : h.traceLin c ≠ 0 := fun h0 => hc (by simpa using congrArg Subtype.val h0)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ ht]

theorem card_traceZero (h : UnitaryFieldData p f K) : Nat.card h.traceZero = p ^ f := by
  have := h.finite
  have hker : (h.traceLin.toAddMonoidHom).ker = h.traceZero := by
    ext c
    exact h.mem_ker_traceLin
  have h3 := AddSubgroup.card_mul_index (h.traceLin.toAddMonoidHom).ker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr h.traceLin_surjective,
    AddSubgroup.card_top, h.card_fixedField, hker, h.card_eq_sq, pow_two] at h3
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos f) h3

@[expose] noncomputable def barSub (h : UnitaryFieldData p f K) : K →+ K :=
  h.bar.toAddMonoidHom - AddMonoidHom.id K

theorem barSub_apply (h : UnitaryFieldData p f K) (c : K) : h.barSub c = h.bar c - c :=
  rfl

theorem barSub_mem_traceZero (h : UnitaryFieldData p f K) (c : K) :
    h.barSub c ∈ h.traceZero := by
  rw [mem_traceZero, trace, barSub_apply, map_sub, bar_bar]
  ring

theorem ker_barSub (h : UnitaryFieldData p f K) :
    h.barSub.ker = h.fixedField.toAddSubgroup := by
  ext c
  rw [AddMonoidHom.mem_ker, barSub_apply, sub_eq_zero]
  rfl

theorem range_barSub (h : UnitaryFieldData p f K) : h.barSub.range = h.traceZero := by
  have := h.finite
  have hle : h.barSub.range ≤ h.traceZero := by
    rintro _ ⟨c, rfl⟩
    exact h.barSub_mem_traceZero c
  have h3 := AddSubgroup.card_mul_index h.barSub.ker
  rw [AddSubgroup.index_ker, ker_barSub, h.card_eq_sq, pow_two] at h3
  have hF : Nat.card h.fixedField.toAddSubgroup = p ^ f := h.card_fixedField
  rw [hF] at h3
  have hrange : Nat.card h.barSub.range = p ^ f :=
    Nat.eq_of_mul_eq_mul_left (pow_pos h.prime.pos f) h3
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hrange, h.card_traceZero])

theorem traceZero_eq_mul_image (h : UnitaryFieldData p f K) {τ : K} (hτ : τ ∈ h.traceZero)
    (hτ0 : τ ≠ 0) : (h.traceZero : Set K) = (τ * ·) '' h.fixedField := by
  have := h.finite
  have hτ' : h.bar τ = -τ := by
    rw [mem_traceZero, trace] at hτ
    linear_combination hτ
  have hsub : (τ * ·) '' (h.fixedField : Set K) ⊆ h.traceZero := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : h.bar a = a := ha
    rw [SetLike.mem_coe, mem_traceZero, trace, map_mul, hτ', ha']
    ring
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [Set.ncard_image_of_injective _ (mul_right_injective₀ hτ0), ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq]
  change Nat.card h.traceZero ≤ Nat.card h.fixedField
  rw [h.card_traceZero, h.card_fixedField]

theorem exists_mem_traceZero_ne_zero (h : UnitaryFieldData p f K) :
    ∃ τ ∈ h.traceZero, τ ≠ 0 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact ⟨h.barSub c, h.barSub_mem_traceZero c, sub_ne_zero.mpr hc⟩

end UnitaryFieldData

theorem unitary_field_trace {p f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData p f K) :
    Function.Surjective h.traceLin ∧ Nat.card h.traceZero = p ^ f ∧
      Set.range (fun c => h.bar c - c) = h.traceZero ∧
      {c : K | h.bar c - c = 0} = h.fixedField ∧
      (∀ τ ∈ h.traceZero, τ ≠ 0 → (h.traceZero : Set K) = (τ * ·) '' h.fixedField) ∧
      ∃ τ ∈ h.traceZero, τ ≠ 0 := by
  refine ⟨h.traceLin_surjective, h.card_traceZero, ?_, ?_, fun τ hτ hτ0 =>
    h.traceZero_eq_mul_image hτ hτ0, h.exists_mem_traceZero_ne_zero⟩
  · have h1 : (Set.range fun c => h.bar c - c) = Set.range h.barSub := rfl
    rw [h1, ← AddMonoidHom.coe_range, h.range_barSub]
  · ext c
    rw [Set.mem_ofPred_eq, sub_eq_zero]
    rfl

end CFSG.LocalAnalysis.ComponentInitial
