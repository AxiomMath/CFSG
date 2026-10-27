module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.GF2Type.Smith1979.Case2

open CFSG.Blueprint CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Sporadic.Schreier

theorem card_fixedPoints_outer_J2
    (σ : MulAut P) (hσ : σ * σ = 1) (hout : ∀ x : P, σ ≠ MulAut.conj x) :
    Nat.card {x : P // σ x = x} = 336 := by
  obtain ⟨r, rfl⟩ := rConj_bijective.2 σ
  have hrr : r * r = 1 := rConj_injective (by rw [map_mul, hσ, map_one])
  have hrP : (r : Equiv.Perm (Fin 315)) ∉ P := fun h => hout ⟨(r : Equiv.Perm (Fin 315)), h⟩
    (MulEquiv.ext fun g => Subtype.ext (by rw [rConj_apply, MulAut.conj_apply]; rfl))
  have hone : (r : Equiv.Perm (Fin 315)) ≠ 1 := fun h => hrP (by rw [h]; exact P.one_mem)
  have ht2 : (r : Equiv.Perm (Fin 315)) ^ 2 = 1 := by
    rw [sq]
    exact_mod_cast congrArg Subtype.val hrr
  have hord : orderOf (r : Equiv.Perm (Fin 315)) = 2 := orderOf_eq_prime ht2 hone
  have hcos : permU⁻¹ * (r : Equiv.Perm (Fin 315)) ∈ P :=
    (mem_P_or_coset r.2).resolve_left hrP
  obtain ⟨c, hc, hceq⟩ := outer_classes.1 _ hcos hord
  have hcen : centralizerIn P (r : Equiv.Perm (Fin 315)) =
      (centralizerIn P permU).map (MulAut.conj c).toMonoidHom := by
    rw [hceq]
    exact centralizerIn_conj P hc permU
  have hfix : (fixSub (rConj r)).map P.subtype = centralizerIn P (r : Equiv.Perm (Fin 315)) :=
    map_fixSub_conjOn P (rConj r) _ fun h => rConj_apply r h
  have h1 : Nat.card (fixSub (rConj r)) =
      Nat.card (centralizerIn P (r : Equiv.Perm (Fin 315))) := by
    rw [← hfix, Subgroup.card_map_of_injective P.subtype_injective]
  have h2 : Nat.card (centralizerIn P (r : Equiv.Perm (Fin 315))) =
      Nat.card (centralizerIn P permU) := by
    rw [hcen, Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective]
  have h3 : Nat.card (centralizerIn P permU) = 336 := by
    rw [outer_classes.2.2]
    exact centOuter_facts.2.1
  calc Nat.card {x : P // rConj r x = x} = Nat.card (fixSub (rConj r)) := rfl
    _ = Nat.card (centralizerIn P (r : Equiv.Perm (Fin 315))) := h1
    _ = Nat.card (centralizerIn P permU) := h2
    _ = 336 := h3

theorem card_fixedPoints_outer_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* P)
    (σ : MulAut X) (hσ : σ * σ = 1) (hout : ∀ x : X, σ ≠ MulAut.conj x) :
    Nat.card {x : X // σ x = x} = 336 := by
  have hσin : σ ∉ inner X := fun h => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h
    exact hout x hx.symm
  have hτin : MulAut.congr e σ ∉ inner P := by
    intro h
    rw [← inner_map_congr e] at h
    obtain ⟨β, hβ, hβσ⟩ := h
    have hβσ' : β = σ := (MulAut.congr e).injective hβσ
    exact hσin (hβσ' ▸ hβ)
  have hτ : MulAut.congr e σ * MulAut.congr e σ = 1 := by
    rw [← map_mul, hσ, map_one]
  have hτout : ∀ x : P, MulAut.congr e σ ≠ MulAut.conj x := fun x hx =>
    hτin (by rw [hx]; exact MonoidHom.mem_range.2 ⟨x, rfl⟩)
  calc Nat.card {x : X // σ x = x} = Nat.card (fixSub σ) := rfl
    _ = Nat.card ((fixSub σ).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (fixSub (MulAut.congr e σ)) := by rw [map_fixSub_equiv]
    _ = Nat.card {x : P // MulAut.congr e σ x = x} := rfl
    _ = 336 := card_fixedPoints_outer_J2 (MulAut.congr e σ) hτ hτout

theorem not_outer_involution_1344_J2 {X : Type} [Group X]
    (e : X ≃* P) :
    ¬ ∃ σ : MulAut X, σ * σ = 1 ∧ (∀ x : X, σ ≠ MulAut.conj x) ∧
      Nat.card {x : X // σ x = x} = 1344 := by
  rintro ⟨σ, hσ, hout, hcard⟩
  rw [card_fixedPoints_outer_of_mulEquiv e σ hσ hout] at hcard
  norm_num at hcard

theorem not_outer_involution_1344_nativeJ2 :
    ¬ ∃ σ : MulAut NativeSporadic.J2, σ * σ = 1 ∧ (∀ x : NativeSporadic.J2, σ ≠ MulAut.conj x) ∧
      Nat.card {x : NativeSporadic.J2 // σ x = x} = 1344 :=
  not_outer_involution_1344_J2 nativeEquivP

end CFSG.GF2Type.Smith1979.Case2
