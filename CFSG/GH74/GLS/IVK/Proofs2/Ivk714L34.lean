module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Spor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.PSL3Four (nonempty_equiv_of_stated)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S
local notation "R42" => CFSG.ComponentClassification.PSL3Four.R

theorem ivk714_l34 :
    Ivk714Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro K _ _ _ hK z hz h
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hK
  obtain ⟨θ⟩ := nonempty_equiv_of_stated K hst
  have hA := l34_autModel
  set α : MulAut ↥S42 := MulAut.congr θ z with hα
  have hαα : α * α = 1 := ivk714_congr_sq_eq_one θ hz
  have hα1 : α ≠ 1 := ivk714_congr_ne_one θ hz
  set x : Equiv.Perm (Fin 42) := hA.elt α with hx
  have hxR : x ∈ R42 := hA.elt_mem α
  have hxx : x * x = 1 := by
    have h1 := (hA.hom).map_mul α α
    rw [hαα, map_one] at h1
    exact h1.symm
  have hx1 : x ≠ 1 := by
    intro h1
    apply hα1
    apply hA.hom_injective
    rw [map_one]
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hmem : ∀ y : ↥S42, α y = y ↔
      (x * (y : Equiv.Perm (Fin 42)) = (y : Equiv.Perm (Fin 42)) * x) := by
    intro y
    have h1 := hA.elt_spec α y
    constructor
    · intro hy
      rw [hy] at h1
      calc x * (y : Equiv.Perm (Fin 42)) = (x * (y : Equiv.Perm (Fin 42)) * x⁻¹) * x := by group
        _ = (y : Equiv.Perm (Fin 42)) * x := by rw [← h1]
    · intro hc
      apply Subtype.ext
      rw [h1]
      calc x * (y : Equiv.Perm (Fin 42)) * x⁻¹ = ((y : Equiv.Perm (Fin 42)) * x) * x⁻¹ := by
            rw [hc]
        _ = (y : Equiv.Perm (Fin 42)) := by group
  have hcard : Nat.card ↥(fixedSubgroup K z) =
      Nat.card ↥(S42 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42)))) := by
    rw [ivk714_card_fixedSubgroup_congr θ z]
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1 : Equiv.Perm (Fin 42)), Subgroup.mem_inf.2
          ⟨y.1.2, Subgroup.mem_centralizer_singleton_iff.2 ((hmem y.1).1 y.2).symm⟩⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, (hmem _).2
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2).symm⟩
        left_inv := fun y => rfl
        right_inv := fun s => rfl }
  have hdvd := h.two_five_two_zero_dvd
  rw [hcard] at hdvd
  rcases l34_inv_cases hxR hx2 with ⟨-, -, -, hN⟩ | ⟨-, -, -, hN⟩ | ⟨-, -, -, hN⟩ | ⟨-, -, -, hN⟩ <;>
    (rw [hN] at hdvd; exact absurd hdvd (by decide))

end CFSG.GH74.GLS.IVK.Proofs2
