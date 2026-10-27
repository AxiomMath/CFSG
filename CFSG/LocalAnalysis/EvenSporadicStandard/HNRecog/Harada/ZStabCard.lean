module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Subgroup

private theorem eichF_self_w {w : V6} (hw : qm w = 0) (x : V6) : eichF w w x = x := by
  have h2 : eichF w w x = eichF w 0 x := by
    have hh := eichF_add_w hw (bil_zero_left w) x
    rwa [zero_add] at hh
  rw [h2, eichF_zero]

private def perpHom (w : V6) : V6 →+ ZMod 2 where
  toFun := fun x => bil x w
  map_zero' := bil_zero_left w
  map_add' := fun x y => bil_add_left x y w

private def perpSub (w : V6) : AddSubgroup V6 := (perpHom w).ker

private theorem bil_of_mem_perpSub {w u : V6} (h : u ∈ perpSub w) : bil u w = 0 := by
  have h' := (AddMonoidHom.mem_ker (f := perpHom w)).mp h
  simpa [perpHom] using h'

private def eichHom (w : V6) : Multiplicative (perpSub w) →* Equiv.Perm V6 where
  toFun := fun u => eichPerm w (Multiplicative.toAdd u).1
    (bil_of_mem_perpSub (Multiplicative.toAdd u).2)
  map_one' := by
    apply Equiv.ext; intro x
    change eichF w 0 x = (1 : Equiv.Perm V6) x
    rw [eichF_zero, Equiv.Perm.one_apply]
  map_mul' := by
    intro u v
    apply Equiv.ext; intro x
    rw [Equiv.Perm.mul_apply, eichPerm_apply, eichPerm_apply, eichPerm_apply, toAdd_mul,
      AddSubgroup.coe_add]
    exact (eichF_comp (bil_of_mem_perpSub (Multiplicative.toAdd u).2)
      (bil_of_mem_perpSub (Multiplicative.toAdd v).2) x).symm

private theorem eichHom_eq_one_iff {w : V6} (hw : qm w = 0) (hw0 : w ≠ 0)
    (u : Multiplicative (perpSub w)) :
    eichHom w u = 1 ↔ (Multiplicative.toAdd u).1 = 0 ∨ (Multiplicative.toAdd u).1 = w := by
  constructor
  · intro h
    have hfun : ∀ x, eichF w (Multiplicative.toAdd u).1 x = eichF w 0 x := by
      intro x
      have hx := Equiv.ext_iff.mp h x
      change eichF w (Multiplicative.toAdd u).1 x = (1 : Equiv.Perm V6) x at hx
      rw [Equiv.Perm.one_apply] at hx
      rw [hx, eichF_zero]
    simpa using (eichF_eq_iff hw hw0 (bil_of_mem_perpSub (Multiplicative.toAdd u).2)
      (bil_zero_left w)).1 hfun
  · rintro (h | h)
    · apply Equiv.ext; intro x
      change eichF w (Multiplicative.toAdd u).1 x = (1 : Equiv.Perm V6) x
      rw [h, eichF_zero, Equiv.Perm.one_apply]
    · apply Equiv.ext; intro x
      change eichF w (Multiplicative.toAdd u).1 x = (1 : Equiv.Perm V6) x
      rw [h]
      rw [eichF_self_w hw, Equiv.Perm.one_apply]


theorem card_EichU {w : V6} (hw : qm w = 0) (hw0 : w ≠ 0) : Nat.card (EichU w) = 16 := by
  have hwmem : w ∈ (perpHom w).ker := by
    rw [AddMonoidHom.mem_ker]; exact bil_self w
  let z1 : Multiplicative (perpSub w) := Multiplicative.ofAdd ⟨w, hwmem⟩
  have hz1_mem : eichHom w z1 = 1 := by
    apply Equiv.ext; intro x
    change eichF w w x = (1 : Equiv.Perm V6) x
    rw [eichF_self_w hw, Equiv.Perm.one_apply]
  have hz1_ne : z1 ≠ 1 := by
    intro h
    have h1 : (Multiplicative.ofAdd (⟨w, hwmem⟩ : perpSub w) : Multiplicative (perpSub w)) = 1 := by
      simpa [z1] using h
    have h2 : (⟨w, hwmem⟩ : perpSub w) = 0 :=
      Equiv.injective Multiplicative.ofAdd (by rw [h1, ofAdd_zero])
    exact hw0 (congrArg Subtype.val h2)
  have hker : Nat.card (eichHom w).ker = 2 := by
    rw [Nat.card_eq_two_iff' (1 : (eichHom w).ker)]
    refine ⟨⟨z1, hz1_mem⟩, ?_, ?_⟩
    · intro h
      exact hz1_ne (congrArg Subtype.val h)
    · intro y hy
      have hyclass := (eichHom_eq_one_iff hw hw0 y.1).1 y.2
      rcases hyclass with h0 | hw'
      · exfalso
        apply hy
        have hy1 : y.1 = 1 := by
          rw [← ofAdd_toAdd y.1, show Multiplicative.toAdd y.1 = 0 from Subtype.ext h0,
            ofAdd_zero]
        exact Subtype.ext (by simpa using hy1)
      · have hyz : y.1 = z1 := by
          rw [← ofAdd_toAdd y.1,
            show Multiplicative.toAdd y.1 = ⟨w, hwmem⟩ from Subtype.ext hw']
        exact Subtype.ext hyz
  have hW : Nat.card (Multiplicative (perpSub w)) = 32 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    change Nat.card {x : V6 // bil x w = 0} = 32
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_perp hw0
  have hrange : (eichHom w).range = EichU w := by
    ext g
    rw [MonoidHom.mem_range, mem_EichU]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(Multiplicative.toAdd u).1, bil_of_mem_perpSub (Multiplicative.toAdd u).2,
        fun _ => rfl⟩
    · rintro ⟨u, hu, hgu⟩
      have hmem : u ∈ (perpHom w).ker := by rw [AddMonoidHom.mem_ker]; exact hu
      refine ⟨Multiplicative.ofAdd ⟨u, hmem⟩, ?_⟩
      apply Equiv.ext; intro x
      show eichF w u x = g x
      rw [hgu x]
  have hmain := Subgroup.card_ker_mul_card_range (eichHom w)
  rw [hrange, hker, hW] at hmain
  omega

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
