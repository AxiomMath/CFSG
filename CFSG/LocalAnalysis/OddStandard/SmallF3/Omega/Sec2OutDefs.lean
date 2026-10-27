module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {P : Type} [Group P]

@[expose] def fixSub (α : MulAut P) : Subgroup P where
  carrier := {p | α p = p}
  mul_mem' := by
    intro a b ha hb
    change α (a * b) = a * b
    rw [map_mul]
    change α a * α b = a * b
    rw [show α a = a from ha, show α b = b from hb]
  one_mem' := map_one α
  inv_mem' := by
    intro a ha
    change α a⁻¹ = a⁻¹
    rw [map_inv]
    change (α a)⁻¹ = a⁻¹
    rw [show α a = a from ha]

theorem mem_fixSub_iff {α : MulAut P} {p : P} : p ∈ fixSub α ↔ α p = p := Iff.rfl

@[expose] def OuterData (P : Type) [Group P] (α : MulAut P) : Prop :=
  ∃ a u : P, u * u = 1 ∧ u ≠ 1 ∧ u ∈ CFSG.inSubgroup CFSG.layer (fixSub α) ∧ a⁻¹ * α a = u

theorem aut_apply_inv (β : MulAut P) (p : P) : β (β⁻¹ p) = p := MulEquiv.apply_symm_apply β p

theorem aut_inv_apply (β : MulAut P) (p : P) : β⁻¹ (β p) = p := MulEquiv.symm_apply_apply β p

theorem mem_fixSub_conj_iff (α β : MulAut P) {p : P} :
    p ∈ fixSub (β⁻¹ * α * β) ↔ β p ∈ fixSub α := by
  rw [mem_fixSub_iff, mem_fixSub_iff]
  change β⁻¹ (α (β p)) = p ↔ α (β p) = β p
  constructor
  · intro h
    have h' := congrArg β h
    rwa [aut_apply_inv] at h'
  · intro h
    rw [h]
    exact aut_inv_apply β p

@[expose] def fixSubConjEquiv (α β : MulAut P) : ↥(fixSub (β⁻¹ * α * β)) ≃* ↥(fixSub α) where
  toFun p := ⟨β p, (mem_fixSub_conj_iff α β).mp p.2⟩
  invFun q := ⟨β⁻¹ q, (mem_fixSub_conj_iff α β).mpr (by
    have : β (β⁻¹ (q : P)) = q := aut_apply_inv β q
    rw [this]
    exact q.2)⟩
  left_inv p := Subtype.ext (aut_inv_apply β (p : P))
  right_inv q := Subtype.ext (aut_apply_inv β (q : P))
  map_mul' a b := Subtype.ext (map_mul β (a : P) (b : P))

theorem OuterData.of_conj {α : MulAut P} (β : MulAut P) (h : OuterData P (β⁻¹ * α * β)) :
    OuterData P α := by
  obtain ⟨a, u, huu, hu1, hl, hau⟩ := h
  refine ⟨β a, β u, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, huu, map_one]
  · intro h1
    exact hu1 (β.injective (by rw [h1, map_one]))
  · obtain ⟨uF, huF, rfl⟩ := hl
    have h2 := CFSG.WholeGroup.layer_map_mulEquiv (fixSubConjEquiv α β)
    have h3 : (fixSubConjEquiv α β) uF ∈ CFSG.layer ↥(fixSub α) := by
      rw [← h2]
      exact ⟨uF, huF, rfl⟩
    exact ⟨_, h3, rfl⟩
  · have h4 : (β⁻¹ * α * β) a = β⁻¹ (α (β a)) := rfl
    rw [h4] at hau
    have h5 : β (a⁻¹ * β⁻¹ (α (β a))) = β u := by rw [hau]
    rw [map_mul, map_inv, aut_apply_inv] at h5
    exact h5

end CFSG.OddStandard.SmallF3.Omega
