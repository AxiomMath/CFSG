module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv

@[expose] def pa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pb : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def px : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def InV (u : Perm (Fin 5)) : Prop := u = 1 ∨ u = pa ∨ u = pb ∨ u = pa * pb

instance (u : Perm (Fin 5)) : Decidable (InV u) := by unfold InV; infer_instance

theorem inV_mul : ∀ u v : Perm (Fin 5), InV u → InV v → InV (u * v) := by
  unfold InV pa pb; decide +kernel

theorem inV_inv : ∀ u : Perm (Fin 5), InV u → InV u⁻¹ := by
  unfold InV pa pb; decide +kernel

theorem inV_conj : ∀ u : Perm (Fin 5), InV u ↔ InV (px * u * px⁻¹) := by
  unfold InV pa pb px; decide +kernel

theorem sign_pa : Perm.sign pa = 1 := by unfold pa; decide +kernel

theorem sign_pb : Perm.sign pb = 1 := by unfold pb; decide +kernel

theorem sign_px : Perm.sign px = 1 := by unfold px; decide +kernel

theorem sign_of_inV {u : Perm (Fin 5)} (h : InV u) : Perm.sign u = 1 := by
  rcases h with rfl | rfl | rfl | rfl
  · simp
  · exact sign_pa
  · exact sign_pb
  · rw [map_mul, sign_pa, sign_pb]; rfl

@[expose] def kleinFour : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {g | InV (g : Perm (Fin 5))}
  mul_mem' := fun {a b} ha hb => inV_mul _ _ ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => inV_inv _ ha

theorem kleinFour_ne_bot : kleinFour ≠ ⊥ := by
  intro h
  have hmem : (⟨pa, Equiv.Perm.mem_alternatingGroup.2 sign_pa⟩ : alternatingGroup (Fin 5)) ∈
      kleinFour := Or.inr (Or.inl rfl)
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg Subtype.val hmem
  revert this
  unfold pa
  decide +kernel

theorem isPGroup_kleinFour : IsPGroup 2 kleinFour := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨g, hg⟩ := g
  have hg' : InV (g : Perm (Fin 5)) := hg
  apply Subtype.ext
  apply Subtype.ext
  show (g : Perm (Fin 5)) ^ 2 ^ 1 = 1
  have : ∀ u : Perm (Fin 5), InV u → u ^ 2 ^ 1 = 1 := by unfold InV pa pb; decide +kernel
  exact this _ hg'

@[expose] def altX : alternatingGroup (Fin 5) := ⟨px, Equiv.Perm.mem_alternatingGroup.2 sign_px⟩

theorem altX_mem_normalizer :
    altX ∈ Subgroup.normalizer (kleinFour : Set (alternatingGroup (Fin 5))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact inV_conj (h : Perm (Fin 5))

theorem orderOf_altX : orderOf altX = 3 := by
  have h1 : altX ^ 3 = 1 := by
    apply Subtype.ext
    show px ^ 3 = 1
    unfold px; decide +kernel
  have h2 : altX ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    revert this
    unfold altX px
    decide +kernel
  exact orderOf_eq_prime h1 h2

theorem threeTwoWitness_alt_five : ThreeTwoWitness (alternatingGroup (Fin 5)) :=
  ⟨kleinFour, kleinFour_ne_bot, isPGroup_kleinFour, altX, orderOf_altX, altX_mem_normalizer⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
