module

public import CFSG.ClassicalInvolution.Q3.Sec13EndSp4

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Sp4

open Equiv

@[expose] def invA6 : List (Perm (Fin 6)) := [
  swap 0 1 * swap 2 3,
  swap 0 2 * swap 1 3,
  swap 0 3 * swap 1 2,
  swap 0 1 * swap 2 4,
  swap 0 2 * swap 1 4,
  swap 0 4 * swap 1 2,
  swap 0 1 * swap 2 5,
  swap 0 2 * swap 1 5,
  swap 0 5 * swap 1 2,
  swap 0 1 * swap 3 4,
  swap 0 3 * swap 1 4,
  swap 0 4 * swap 1 3,
  swap 0 1 * swap 3 5,
  swap 0 3 * swap 1 5,
  swap 0 5 * swap 1 3,
  swap 0 1 * swap 4 5,
  swap 0 4 * swap 1 5,
  swap 0 5 * swap 1 4,
  swap 0 2 * swap 3 4,
  swap 0 3 * swap 2 4,
  swap 0 4 * swap 2 3,
  swap 0 2 * swap 3 5,
  swap 0 3 * swap 2 5,
  swap 0 5 * swap 2 3,
  swap 0 2 * swap 4 5,
  swap 0 4 * swap 2 5,
  swap 0 5 * swap 2 4,
  swap 0 3 * swap 4 5,
  swap 0 4 * swap 3 5,
  swap 0 5 * swap 3 4,
  swap 1 2 * swap 3 4,
  swap 1 3 * swap 2 4,
  swap 1 4 * swap 2 3,
  swap 1 2 * swap 3 5,
  swap 1 3 * swap 2 5,
  swap 1 5 * swap 2 3,
  swap 1 2 * swap 4 5,
  swap 1 4 * swap 2 5,
  swap 1 5 * swap 2 4,
  swap 1 3 * swap 4 5,
  swap 1 4 * swap 3 5,
  swap 1 5 * swap 3 4,
  swap 2 3 * swap 4 5,
  swap 2 4 * swap 3 5,
  swap 2 5 * swap 3 4]

theorem mem_invA6 : ∀ s : Perm (Fin 6), s * s = 1 → s ≠ 1 → Perm.sign s = 1 → s ∈ invA6 := by
  unfold invA6; decide +kernel


private def KX (s t : Perm (Fin 6)) (z : Fin 6 → ZMod 2) : Prop :=
  ∀ x : Fin 6 → ZMod 2, Even6 x → Sim (permVec s x) x → Sim (permVec t x) x → Sim x 0 ∨ Sim x z

private instance (s t : Perm (Fin 6)) (z : Fin 6 → ZMod 2) : Decidable (KX s t z) := by
  unfold KX; infer_instance

private def KAB (s t : Perm (Fin 6)) : Prop :=
  ∀ a b : Fin 6, a ≠ b → Sim (permVec s (duadVec a b)) (duadVec a b) →
    Sim (permVec t (duadVec a b)) (duadVec a b) → KX s t (duadVec a b) →
      s a = a ∧ s b = b ∧ t a = a ∧ t b = b

private instance (s t : Perm (Fin 6)) : Decidable (KAB s t) := by unfold KAB; infer_instance

private def KT (s : Perm (Fin 6)) : Prop :=
  ∀ t ∈ invA6, t ≠ s → s * t = t * s → KAB s t

private instance (s : Perm (Fin 6)) : Decidable (KT s) := by unfold KT; infer_instance

private theorem kt_all : ∀ s ∈ invA6, KT s := by
  decide +kernel

theorem klein_fixes_duad : ∀ a b : Fin 6, a ≠ b →
    ∀ s : Equiv.Perm (Fin 6), s * s = 1 → s ≠ 1 → Equiv.Perm.sign s = 1 →
      Sim (permVec s (duadVec a b)) (duadVec a b) →
    ∀ t : Equiv.Perm (Fin 6), t * t = 1 → t ≠ 1 → Equiv.Perm.sign t = 1 → t ≠ s → s * t = t * s →
      Sim (permVec t (duadVec a b)) (duadVec a b) →
      (∀ x : Fin 6 → ZMod 2, Even6 x → Sim (permVec s x) x → Sim (permVec t x) x →
        Sim x 0 ∨ Sim x (duadVec a b)) →
      s a = a ∧ s b = b ∧ t a = a ∧ t b = b := by
  intro a b hab s hs2 hs1 hss hsd t ht2 ht1 hts hts' hcomm htd hX
  exact kt_all s (mem_invA6 s hs2 hs1 hss) t (mem_invA6 t ht2 ht1 hts) hts' hcomm a b hab hsd htd hX

private def VF (a b : Fin 6) (s : Perm (Fin 6)) : Prop :=
  ∀ f : Fin 6 → ZMod 2, Even6 f → Sim (f + permVec s f) (duadVec a b) → f a = f b

private instance (a b : Fin 6) (s : Perm (Fin 6)) : Decidable (VF a b s) := by
  unfold VF; infer_instance

private def VAB (s : Perm (Fin 6)) : Prop :=
  ∀ a b : Fin 6, a ≠ b → s a = a → s b = b → VF a b s

private instance (s : Perm (Fin 6)) : Decidable (VAB s) := by unfold VAB; infer_instance

private theorem vab_all : ∀ s : Perm (Fin 6), s * s = 1 → s ≠ 1 → VAB s := by
  decide +kernel

theorem vec_supported_model : ∀ a b : Fin 6, a ≠ b →
    ∀ s : Equiv.Perm (Fin 6), s * s = 1 → s ≠ 1 → s a = a → s b = b →
    ∀ f : Fin 6 → ZMod 2, Even6 f → Sim (f + permVec s f) (duadVec a b) → f a = f b := by
  intro a b hab s hs2 hs1 hsa hsb f hf hsim
  exact vab_all s hs2 hs1 a b hab hsa hsb f hf hsim

end CFSG.ClassicalInvolution.Q3.Sec13.Sp4
