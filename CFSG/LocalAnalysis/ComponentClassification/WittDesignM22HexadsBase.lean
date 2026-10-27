
module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
public import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Monster.B.Classical.PlaneData
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs
public import Certificates.Data.CFSGNative.Mathieu.M22

@[expose] public section

namespace CFSG.ComponentClassification.WittDesign

open scoped Pointwise
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Classical.Plane

@[expose] def hexads : Finset (Finset (Fin 22)) := hexadList.toFinset

theorem mem_hexads {B : Finset (Fin 22)} : B ∈ hexads ↔ B ∈ hexadList := List.mem_toFinset

theorem card_eq_length_filter (A : Finset (Fin 22)) :
    A.card = ((List.finRange 22).filter fun i => decide (i ∈ A)).length := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 22).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  congr 1
  ext i
  simp

theorem card_inter_eq_interBits (B B' : Finset (Fin 22)) :
    (B ∩ B').card = interBits (mask B) (mask B') := by
  rw [card_eq_length_filter, interBits]
  congr 1
  refine List.filter_congr fun i _ => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, testBit_mask, testBit_mask,
    Finset.mem_inter]

theorem smul_finset_eq_self_iff (g : Equiv.Perm (Fin 22)) (B : Finset (Fin 22)) :
    g • B = B ↔ ∀ x ∈ B, g x ∈ B := by
  rw [Finset.smul_finset_def]
  constructor
  · intro h x hx
    rw [← h]
    exact Finset.mem_image_of_mem _ hx
  · intro h
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact h x hx
    · rw [Finset.card_image_of_injective _ (MulAction.injective g)]

theorem smul_finset_eq_map (g : Equiv.Perm (Fin 22)) (B : Finset (Fin 22)) :
    g • B = B.map g.toEmbedding := by
  rw [Finset.smul_finset_def, Finset.map_eq_image]
  rfl

theorem mem_stabilizer_finset_iff {g : M22} {B : Finset (Fin 22)} :
    g ∈ MulAction.stabilizer M22 B ↔ ∀ x ∈ B, (g : Equiv.Perm (Fin 22)) x ∈ B := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, smul_finset_eq_self_iff]

theorem natCard_orbit_mul_card_stabilizer (G : Type*) [Group G] {α : Type*} [MulAction G α]
    (x : α) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

theorem card_orbit_mul_card_stabilizer {α : Type*} [MulAction M22 α] (x : α) :
    Nat.card (MulAction.orbit M22 x) * Nat.card (MulAction.stabilizer M22 x) = 443520 := by
  rw [← card_M22, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M22 x)

end CFSG.ComponentClassification.WittDesign
