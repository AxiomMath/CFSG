module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L126

open Equiv Equiv.Perm Subgroup MulAction
open scoped Pointwise

abbrev A11 := alternatingGroup (Fin 11)

@[expose] def FixF (F : Set (Fin 11)) : Subgroup A11 where
  carrier := {σ | ∀ x, x ∈ F → (σ : Perm (Fin 11)) x = x}
  one_mem' := fun x _ => rfl
  mul_mem' := by
    intro a b ha hb x hx
    show (a : Perm (Fin 11)) ((b : Perm (Fin 11)) x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    show ((a : Perm (Fin 11))⁻¹) x = x
    rw [Perm.inv_eq_iff_eq]
    exact (ha x hx).symm

abbrev StabF (F : Set (Fin 11)) : Subgroup A11 := MulAction.stabilizer A11 F

theorem mem_StabF {F : Set (Fin 11)} {σ : A11} :
    σ ∈ StabF F ↔ ∀ x, (σ : Perm (Fin 11)) x ∈ F ↔ x ∈ F := by
  rw [MulAction.mem_stabilizer_set]
  rfl

theorem StabF_conj_FixF (F : Set (Fin 11)) {σ : A11} (hσ : σ ∈ StabF F) {τ : A11} (hτ : τ ∈ FixF F) :
    σ * τ * σ⁻¹ ∈ FixF F := by
  rw [mem_StabF] at hσ
  intro x hx
  show (σ : Perm (Fin 11)) ((τ : Perm (Fin 11)) ((σ : Perm (Fin 11))⁻¹ x)) = x
  have h1 : (σ : Perm (Fin 11))⁻¹ x ∈ F := by
    exact (hσ _).mp (by simpa using hx)
  rw [hτ _ h1]
  simp

abbrev ThreeSets := {s : Finset (Fin 11) // s.card = 3}

instance : SMul (Perm (Fin 11)) ThreeSets :=
  ⟨fun σ s => ⟨s.1.map σ.toEmbedding, by rw [Finset.card_map]; exact s.2⟩⟩

theorem smul_threeSets_coe (σ : Perm (Fin 11)) (s : ThreeSets) :
    (σ • s).1 = s.1.map σ.toEmbedding := rfl

instance : MulAction (Perm (Fin 11)) ThreeSets where
  one_smul s := Subtype.ext (by
    rw [smul_threeSets_coe]
    ext x
    simp only [Finset.mem_map_equiv, ← Equiv.Perm.inv_def, inv_one, Equiv.Perm.one_apply])
  mul_smul σ τ s := Subtype.ext (by
    rw [smul_threeSets_coe, smul_threeSets_coe, smul_threeSets_coe]
    ext x
    simp only [Finset.mem_map_equiv, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply])

theorem FixF_normal_in_StabF (F : Set (Fin 11)) : ((FixF F).subgroupOf (StabF F)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := StabF_conj_FixF F g.2 hn
  simpa using this

instance (F : Set (Fin 11)) : ((FixF F).subgroupOf (StabF F)).Normal := FixF_normal_in_StabF F

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L126
