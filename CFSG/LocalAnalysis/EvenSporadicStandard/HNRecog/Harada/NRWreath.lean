module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

private theorem coord_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd x) with h | h
  · left
    rw [← ofAdd_toAdd x, h]
    rfl
  · right
    rw [← ofAdd_toAdd x, h]

private theorem ofAdd_one_ne_one :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide

private theorem inv_one_eq : (1 : Multiplicative (ZMod 2))⁻¹ = 1 := by
  exact inv_one

private theorem inv_one_mul (x : Multiplicative (ZMod 2)) :
    (1 : Multiplicative (ZMod 2))⁻¹ * x = x := by
  rw [show (1 : Multiplicative (ZMod 2))⁻¹ = 1 from inv_one, one_mul]

private theorem natCard_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [natCard_A5, h2]
  norm_num

@[expose] def wrBase : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* A5WrTwo where
  toFun p := ⟨fun x => if x = 1 then p.1 else p.2, 1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext x
      by_cases h : x = 1 <;> simp [h]
    · rfl
  map_mul' p q := by
    apply RegularWreathProduct.ext
    · funext x
      change (if x = 1 then (p * q).1 else (p * q).2) =
        (if x = 1 then p.1 else p.2) *
          (if (1 : Multiplicative (ZMod 2))⁻¹ * x = 1 then q.1 else q.2)
      rcases coord_cases x with rfl | rfl <;>
        simp [inv_one_eq, inv_one_mul, ofAdd_one_ne_one]
    · simp [RegularWreathProduct.mul_def]

@[expose] def wrSwap : A5WrTwo := ⟨1, Multiplicative.ofAdd 1⟩

theorem wrBase_injective : Function.Injective wrBase := by
  intro p q h
  have h1 : p.1 = q.1 := by
    simpa [wrBase] using congrArg (fun g : A5WrTwo => g.left 1) h
  have h2 : p.2 = q.2 := by
    simpa [wrBase, ofAdd_one_ne_one] using
      congrArg (fun g : A5WrTwo => g.left (Multiplicative.ofAdd 1)) h
  exact Prod.ext h1 h2

theorem wrSwap_notMem_range_wrBase : wrSwap ∉ wrBase.range := by
  intro h
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp h
  have hright : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 := by
    simpa [wrBase, wrSwap] using congrArg (fun g : A5WrTwo => g.right) hp.symm
  exact ofAdd_one_ne_one hright

theorem index_range_wrBase : wrBase.range.index = 2 := by
  have hcard : Nat.card wrBase.range * wrBase.range.index = Nat.card A5WrTwo :=
    Subgroup.card_mul_index wrBase.range
  have hrange : Nat.card wrBase.range =
      Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (Nat.card_congr (MonoidHom.ofInjective wrBase_injective).toEquiv).symm
  have hprod : Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = 3600 := by
    rw [Nat.card_prod, natCard_A5]
  rw [natCard_A5WrTwo, hrange, hprod] at hcard
  omega

theorem wrSwap_mul_wrBase_mul_inv (p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    wrSwap * wrBase p * wrSwap⁻¹ = wrBase p.swap := by
  have hσ2 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) *
      (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 := by decide
  have hσinv : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ =
      Multiplicative.ofAdd 1 := inv_eq_of_mul_eq_one_right hσ2
  apply RegularWreathProduct.ext
  · funext x
    rcases coord_cases x with rfl | rfl <;>
      simp [wrSwap, wrBase, Prod.swap, RegularWreathProduct.mul_def, hσ2, hσinv,
        ofAdd_one_ne_one]
  · simp [wrSwap, wrBase, RegularWreathProduct.mul_def, hσ2, hσinv]

theorem wrSwap_mul_self : wrSwap * wrSwap = wrBase 1 := by
  have hσ2 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) *
      (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 := by decide
  have hσinv : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ =
      Multiplicative.ofAdd 1 := inv_eq_of_mul_eq_one_right hσ2
  apply RegularWreathProduct.ext
  · funext x
    rcases coord_cases x with rfl | rfl <;>
      simp [wrSwap, wrBase, RegularWreathProduct.mul_def, hσ2, hσinv]
  · simp [wrSwap, wrBase, RegularWreathProduct.mul_def, hσ2, hσinv]

end CFSG.EvenSporadicStandard.HNRecog.Harada
