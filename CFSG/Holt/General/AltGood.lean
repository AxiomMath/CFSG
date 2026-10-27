module

public import CFSG.Holt.General.Defs
import CFSG.Holt.General.Simple

public section

namespace CFSG.Holt.General

open MulAction Subgroup Equiv Equiv.Perm

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

section Bridge

variable [Fintype Ω] [DecidableEq Ω]

theorem range_toPermHom_le_alternatingGroup [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : (toPermHom X Ω).range ≤ alternatingGroup Ω := by
  let f : X →* ℤˣ := sign.comp (toPermHom X Ω)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd ((MonoidHom.ker_eq_bot_iff f).mp h (by rw [map_mul, map_mul, mul_comm])) hab
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ f.ker := h ▸ Subgroup.mem_top x
    exact mem_alternatingGroup.mpr (MonoidHom.mem_ker.mp hx)

theorem range_toPermHom_eq_alternatingGroup_of_le [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hA : alternatingGroup Ω ≤ (toPermHom X Ω).range) :
    (toPermHom X Ω).range = alternatingGroup Ω :=
  le_antisymm (range_toPermHom_le_alternatingGroup hnonab) hA

theorem exists_mulEquiv_alternatingGroup_of_le_range [IsSimpleGroup X] [FaithfulSMul X Ω]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {m : ℕ} (hm : Nat.card Ω = 2 * m + 1)
    (hA : alternatingGroup Ω ≤ (toPermHom X Ω).range) (α : Ω) :
    2 ≤ m ∧ ∃ e : X ≃* alternatingGroup (Fin (2 * m + 1)),
      (stabilizer X α).map e.toMonoidHom =
        stabilizer (alternatingGroup (Fin (2 * m + 1))) (0 : Fin (2 * m + 1)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Ω ≃ Fin (2 * m + 1), φ α = 0 := by
    let φ₀ : Ω ≃ Fin (2 * m + 1) :=
      Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hm])
    exact ⟨φ₀.trans (Equiv.swap (φ₀ α) 0), by simp⟩
  let e : X ≃* alternatingGroup (Fin (2 * m + 1)) :=
    ((MonoidHom.ofInjective (f := toPermHom X Ω) toPerm_injective).trans
      (MulEquiv.subgroupCongr (range_toPermHom_eq_alternatingGroup_of_le hnonab hA))).trans
      φ.altCongrHom
  have he : ∀ x : X, ((e x : alternatingGroup (Fin (2 * m + 1))) : Perm (Fin (2 * m + 1))) =
      φ.permCongr (toPerm x) := fun x => rfl
  refine ⟨?_, e, ?_⟩
  · by_contra hlt
    have hc : IsMulCommutative (alternatingGroup (Fin (2 * m + 1))) :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mpr (by rw [Nat.card_fin]; omega)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _))
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hα : φ.symm 0 = α := φ.symm_apply_eq.mpr hφ.symm
    rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_stabilizer_iff, mem_stabilizer_iff,
      Subgroup.smul_def, Perm.smul_def, he, permCongr_apply, hα, ← hφ, φ.injective.eq_iff,
      toPerm_apply]

theorem isGoodZ_top_of_alternatingGroup_le [IsSimpleGroup X] [FaithfulSMul X Ω]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hodd : Odd (Nat.card Ω))
    (hA : alternatingGroup Ω ≤ (toPermHom X Ω).range) (α : Ω) : IsGoodZ X Ω α ⊤ := by
  have : Finite X := Finite.of_injective _ (toPerm_injective (α := X) (β := Ω))
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨hm2, e, he⟩ := exists_mulEquiv_alternatingGroup_of_le_range hnonab hm hA α
  exact (isGoodZ_top_iff hnonab α).mpr (Or.inr ⟨m, hm2, e, he⟩)

end Bridge

end CFSG.Holt.General
