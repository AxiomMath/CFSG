module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Equivariant

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a w : G}

theorem Sec4Hyp.exists_aut_conj (h : Sec4Hyp T T₁ a T₂) {y : G} (hy : y ∈ sec4Y T T₁ T₂) :
    ∃ κ : ↥(sec4N T T₁ T₂) ≃* ↥(sec4N T T₁ T₂), ∀ m : ↥(sec4N T T₁ T₂),
      ((κ m : ↥(sec4N T T₁ T₂)) : G) = y * m * y⁻¹ :=
  ⟨(sec4N T T₁ T₂).normalizerMonoidHom ⟨y, h.sec4Y_le_normalizer hy⟩, fun m => by simp⟩

theorem Sec4Hyp.sec4Psi_conj (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) {y : G}
    (hy : y ∈ sec4Y T T₁ T₂) :
    ∃ κ : ↥(sec4N T T₁ T₂) ≃* ↥(sec4N T T₁ T₂),
      sec4Psi h hw (conjSubgroup y T) = (sec4Psi h hw T).map κ.toMonoidHom := by
  obtain ⟨κ, hκ⟩ := h.exists_aut_conj hy
  have hν : ∀ m : ↥(sec4N T T₁ T₂), sec4Nu h hw (κ m) = κ (sec4Nu h hw m) := fun m =>
    Subtype.ext (by
      rw [coe_sec4Nu, hκ, hκ, coe_sec4Nu]
      exact h.comm_equivariant hw hy m.2)
  refine ⟨κ, ?_⟩
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' := Subgroup.mem_subgroupOf.1 hm
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ↥(sec4N T T₁ T₂), κ m₀ = m := ⟨κ.symm m, κ.apply_symm_apply m⟩
    have hm₀G : (m₀ : G) = y⁻¹ * m * y := by
      have := hκ m₀
      rw [hm₀] at this
      rw [this]
      group
    refine ⟨sec4Nu h hw m₀, ⟨m₀, Subgroup.mem_subgroupOf.2 ⟨?_, m₀.2⟩, rfl⟩, ?_⟩
    · rw [hm₀G]
      exact mem_conjSubgroup.1 hm'.1
    · show κ (sec4Nu h hw m₀) = sec4Nu h hw m
      rw [← hν, hm₀]
  · rintro ⟨_, ⟨m₀, hm₀, rfl⟩, rfl⟩
    have hm₀' := Subgroup.mem_subgroupOf.1 hm₀
    refine ⟨κ m₀, Subgroup.mem_subgroupOf.2 ⟨?_, (κ m₀).2⟩, hν m₀⟩
    rw [hκ]
    have : y * (m₀ : G) * y⁻¹ ∈ conjSubgroup y T :=
      mem_conjSubgroup.2 (by simpa [mul_assoc] using hm₀'.1)
    exact this

theorem Sec4Hyp.card_sec4Psi_conj (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) {y : G}
    (hy : y ∈ sec4Y T T₁ T₂) :
    Nat.card ↥(sec4Psi h hw (conjSubgroup y T)) = Nat.card ↥(sec4Psi h hw T) := by
  obtain ⟨κ, hκ⟩ := h.sec4Psi_conj hw hy
  rw [hκ]
  exact Subgroup.card_map_of_injective κ.injective

end Equivariant

end CFSG.CGT.Timmesfeld75
