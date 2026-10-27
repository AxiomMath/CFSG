module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv

@[expose] def pa4 : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def pb4 : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def px4 : Perm (Fin 4) := swap 0 1 * swap 1 2

@[expose] def InV4 (u : Perm (Fin 4)) : Prop := u = 1 ∨ u = pa4 ∨ u = pb4 ∨ u = pa4 * pb4

instance (u : Perm (Fin 4)) : Decidable (InV4 u) := by unfold InV4; infer_instance

theorem inV_mul4 : ∀ u v : Perm (Fin 4), InV4 u → InV4 v → InV4 (u * v) := by
  unfold InV4 pa4 pb4; decide +kernel

theorem inV_inv4 : ∀ u : Perm (Fin 4), InV4 u → InV4 u⁻¹ := by
  unfold InV4 pa4 pb4; decide +kernel

theorem inV_conj4 : ∀ u : Perm (Fin 4), InV4 u ↔ InV4 (px4 * u * px4⁻¹) := by
  unfold InV4 pa4 pb4 px4; decide +kernel

theorem sign_pa4 : Perm.sign pa4 = 1 := by unfold pa4; decide +kernel

theorem sign_pb4 : Perm.sign pb4 = 1 := by unfold pb4; decide +kernel

theorem sign_px4 : Perm.sign px4 = 1 := by unfold px4; decide +kernel

theorem sign_of_inV4 {u : Perm (Fin 4)} (h : InV4 u) : Perm.sign u = 1 := by
  rcases h with rfl | rfl | rfl | rfl
  · simp
  · exact sign_pa4
  · exact sign_pb4
  · rw [map_mul, sign_pa4, sign_pb4]; rfl

@[expose] def kleinFour4 : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {g | InV4 (g : Perm (Fin 4))}
  mul_mem' := fun {a b} ha hb => inV_mul4 _ _ ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => inV_inv4 _ ha

theorem kleinFour_ne_bot4 : kleinFour4 ≠ ⊥ := by
  intro h
  have hmem : (⟨pa4, Equiv.Perm.mem_alternatingGroup.2 sign_pa4⟩ : alternatingGroup (Fin 4)) ∈
      kleinFour4 := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg Subtype.val hmem
  revert this
  unfold pa4
  decide +kernel

theorem isPGroup_kleinFour4 : IsPGroup 2 kleinFour4 := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨g, hg⟩ := g
  have hg' : InV4 (g : Perm (Fin 4)) := hg
  apply Subtype.ext
  apply Subtype.ext
  show (g : Perm (Fin 4)) ^ 2 ^ 1 = 1
  have : ∀ u : Perm (Fin 4), InV4 u → u ^ 2 ^ 1 = 1 := by unfold InV4 pa4 pb4; decide +kernel
  exact this _ hg'

@[expose] def altX4 : alternatingGroup (Fin 4) := ⟨px4, Equiv.Perm.mem_alternatingGroup.2 sign_px4⟩

theorem altX_mem_normalizer4 :
    altX4 ∈ Subgroup.normalizer (kleinFour4 : Set (alternatingGroup (Fin 4))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact inV_conj4 (h : Perm (Fin 4))

theorem orderOf_altX4 : orderOf altX4 = 3 := by
  have h1 : altX4 ^ 3 = 1 := by
    apply Subtype.ext
    show px4 ^ 3 = 1
    unfold px4; decide +kernel
  have h2 : altX4 ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    revert this
    unfold altX4 px4
    decide +kernel
  exact orderOf_eq_prime h1 h2

theorem threeTwoWitness_alt_four : ThreeTwoWitness (alternatingGroup (Fin 4)) :=
  ⟨kleinFour4, kleinFour_ne_bot4, isPGroup_kleinFour4, altX4, orderOf_altX4, altX_mem_normalizer4⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
