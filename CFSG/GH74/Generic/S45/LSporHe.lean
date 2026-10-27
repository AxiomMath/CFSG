module

public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterClass
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

namespace CFSG.GH74.Generic.S45

theorem he_fixed_card
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He)
    (α : MulAut S) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card ↥(autFixed α) = 161280 ∨ Nat.card ↥(autFixed α) = 21504 ∨
      Nat.card ↥(autFixed α) = 15120 := by
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  let φ : S ≃* heP := e.trans heEquivP
  let β : MulAut heP := MulAut.congr φ α
  have hβ2 : β * β = 1 := by
    show MulAut.congr φ α * MulAut.congr φ α = 1
    rw [← map_mul, hα2, map_one]
  have hβ1 : β ≠ 1 := fun h => hα1 ((MulAut.congr φ).injective (by
    have h' : MulAut.congr φ α = 1 := h
    rw [h', map_one]))
  obtain ⟨x, hx⟩ := hbij.2 β
  have hxx : x * x = 1 := hbij.1 (by rw [map_mul, hx, hβ2, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [← hx, h, map_one])
  have hord : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have h2 : (x : Equiv.Perm (Fin 8330)) * x = 1 := by
        have := congrArg Subtype.val hxx
        simpa using this
      rw [pow_two]
      exact h2
    · intro h
      exact hx1 (Subtype.ext h)
  have hkey : ∀ p : heP, β p = p ↔
      (p : Equiv.Perm (Fin 8330)) * (x : Equiv.Perm (Fin 8330)) =
        (x : Equiv.Perm (Fin 8330)) * (p : Equiv.Perm (Fin 8330)) := by
    intro p
    have h1 : ((β p : heP) : Equiv.Perm (Fin 8330)) =
        (x : Equiv.Perm (Fin 8330)) * (p : Equiv.Perm (Fin 8330)) *
          (x : Equiv.Perm (Fin 8330))⁻¹ := by
      rw [← hx]
      exact heConjR_apply x p
    constructor
    · intro h
      have h2 : (p : Equiv.Perm (Fin 8330)) =
          (x : Equiv.Perm (Fin 8330)) * (p : Equiv.Perm (Fin 8330)) *
            (x : Equiv.Perm (Fin 8330))⁻¹ := by
        rw [← h1, h]
      calc (p : Equiv.Perm (Fin 8330)) * x
          = ((x : Equiv.Perm (Fin 8330)) * (p : Equiv.Perm (Fin 8330)) *
              (x : Equiv.Perm (Fin 8330))⁻¹) * x := by rw [← h2]
        _ = x * p := by group
    · intro h
      apply Subtype.ext
      rw [h1, ← h]
      group
  have hfix : Nat.card {p : heP // β p = p} =
      Nat.card ↥(heP ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} :
        Set (Equiv.Perm (Fin 8330)))) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1 : Equiv.Perm (Fin 8330)), Subgroup.mem_inf.2 ⟨p.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 ((hkey p.1).1 p.2)⟩⟩
        invFun := fun q => ⟨⟨q.1, (Subgroup.mem_inf.1 q.2).1⟩, (hkey _).2
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 q.2).2)⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hall : Nat.card ↥(autFixed α) = Nat.card ↥(heP ⊓ Subgroup.centralizer
      ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330)))) := by
    rw [← hfix]
    exact Nat.card_congr (autFixedEquiv φ α).toEquiv
  rw [hall]
  by_cases hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP
  · rcases involution_conj_cases hxP hord with ⟨g, hg, hxg⟩ | ⟨g, hg, hxg⟩
    · left
      rw [hxg]
      show Nat.card ↥(centralizerIn heP (g * heGenPerm 0 * g⁻¹)) = 161280
      rw [centralizerIn_conj heP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact card_heP_cent0
    · right
      left
      rw [hxg]
      show Nat.card ↥(centralizerIn heP (g * heT1P * g⁻¹)) = 21504
      rw [centralizerIn_conj heP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact card_heP_cent1
  · obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hord
    right
    right
    rw [hxg]
    show Nat.card ↥(centralizerIn heP (g * heAutU * g⁻¹)) = 15120
    rw [centralizerIn_conj heP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_heP_centralizer_heAutU

end CFSG.GH74.Generic.S45
