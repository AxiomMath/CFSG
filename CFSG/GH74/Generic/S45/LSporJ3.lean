module

public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.GH74.Generic.S45

theorem card_fixed_congr' {S T : Type} [Group S] [Group T] (e : S ≃* T) (yb : MulAut S) :
    Nat.card {x : T // (MulAut.congr e yb) x = x} = Nat.card ↥(autFixed yb) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)).symm
  have h : (MulAut.congr e yb) (e x) = e (yb x) := by
    rw [MulAut.congr_apply]
    simp
  rw [mem_autFixed_iff]
  show yb x = x ↔ (MulAut.congr e yb) (e x) = e x
  rw [h]
  exact ⟨fun h => by rw [h], fun h => e.injective h⟩

theorem j3_fixed_card
    {S : Type} [Group S] (e : S ≃* NativeSporadic.J3) (α : MulAut S) (hα2 : α * α = 1)
    (hα1 : α ≠ 1) :
    Nat.card ↥(autFixed α) = 1920 ∨ Nat.card ↥(autFixed α) = 2448 := by
  obtain ⟨eR, heR, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  let φ : S ≃* j3P := e.trans j3PermEquiv
  let β : MulAut j3P := MulAut.congr φ α
  have hβ2 : β * β = 1 := by
    show MulAut.congr φ α * MulAut.congr φ α = 1
    rw [← map_mul, hα2, map_one]
  have hβ1 : β ≠ 1 := fun h => hα1 ((MulAut.congr φ).injective (by
    have h' : MulAut.congr φ α = 1 := h
    rw [h', map_one]))
  obtain ⟨x, hx⟩ := eR.surjective β
  have hxx : x * x = 1 := eR.injective (by rw [map_mul, hx, hβ2, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [← hx, h, map_one])
  have hord : orderOf (x : Equiv.Perm (Fin 6156)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have h2 : (x : Equiv.Perm (Fin 6156)) * x = 1 := by
        have := congrArg Subtype.val hxx
        simpa using this
      rw [pow_two]
      exact h2
    · intro h
      exact hx1 (Subtype.ext h)
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin 6156)) x.2 hord
  obtain ⟨-, -, -, -, hcent, -⟩ := hrows r hr
  have hkey : ∀ p : j3P, β p = p ↔
      (p : Equiv.Perm (Fin 6156)) * (x : Equiv.Perm (Fin 6156)) =
        (x : Equiv.Perm (Fin 6156)) * (p : Equiv.Perm (Fin 6156)) := by
    intro p
    have h1 : ((β p : j3P) : Equiv.Perm (Fin 6156)) =
        (x : Equiv.Perm (Fin 6156)) * (p : Equiv.Perm (Fin 6156)) * (x : Equiv.Perm (Fin 6156))⁻¹ := by
      rw [← hx]
      exact heR x p
    constructor
    · intro h
      have h2 : (p : Equiv.Perm (Fin 6156)) =
          (x : Equiv.Perm (Fin 6156)) * (p : Equiv.Perm (Fin 6156)) *
            (x : Equiv.Perm (Fin 6156))⁻¹ := by
        rw [← h1, h]
      calc (p : Equiv.Perm (Fin 6156)) * x
          = ((x : Equiv.Perm (Fin 6156)) * (p : Equiv.Perm (Fin 6156)) *
              (x : Equiv.Perm (Fin 6156))⁻¹) * x := by rw [← h2]
        _ = x * p := by group
    · intro h
      apply Subtype.ext
      rw [h1, ← h]
      group
  have hfix : Nat.card {p : j3P // β p = p} =
      Nat.card ↥(j3P ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 6156))} :
        Set (Equiv.Perm (Fin 6156)))) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1 : Equiv.Perm (Fin 6156)), Subgroup.mem_inf.2 ⟨p.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 ((hkey p.1).1 p.2)⟩⟩
        invFun := fun q => ⟨⟨q.1, (Subgroup.mem_inf.1 q.2).1⟩, (hkey _).2
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 q.2).2)⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hcardx : Nat.card ↥(j3P ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 6156))} :
      Set (Equiv.Perm (Fin 6156)))) = r.centOrder := by
    rw [hxg]
    show Nat.card ↥(centralizerIn j3P (g * tp 6156 r.rep * g⁻¹)) = r.centOrder
    rw [centralizerIn_conj j3P hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcent
  have hcO : r.centOrder = 1920 ∨ r.centOrder = 2448 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        List.map (fun r => (r.outer, r.classSize, r.centOrder)) j3Rows := List.mem_map_of_mem hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hall : Nat.card ↥(autFixed α) = r.centOrder := by
    rw [← card_fixed_congr' φ α]
    exact hfix.trans hcardx
  rw [hall]
  exact hcO

end CFSG.GH74.Generic.S45
