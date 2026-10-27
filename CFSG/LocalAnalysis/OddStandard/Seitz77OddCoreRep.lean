module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreCount

import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.Seitz77

@[expose] def oddCoreRep {H : Type*} [Group H] (ρ : H →* GL (Fin 8) (ZMod 2)) :
    H →* Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  (Matrix.toLinAlgEquiv' (R := ZMod 2) (n := Fin 8)).toAlgHom.toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin 8) (Fin 8) (ZMod 2))).comp ρ)

theorem oddCoreRep_injective {H : Type*} [Group H] (ρ : H →* GL (Fin 8) (ZMod 2))
    (hρ : Function.Injective ρ) : Function.Injective (oddCoreRep ρ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = 1 := by
    apply Matrix.toLinAlgEquiv'.injective
    simpa [oddCoreRep] using hg
  apply hρ
  rw [map_one]
  exact Units.ext h1

theorem oddCore_finrank_fin_eight_fun : Module.finrank (ZMod 2) (Fin 8 → ZMod 2) = 8 := by
  simp

theorem oddCore_card_dvd_gl_eight {H : Type*} [Group H] (ρ : H →* GL (Fin 8) (ZMod 2))
    (hρ : Function.Injective ρ) :
    Nat.card H ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  rw [← oddCore_card_gl_eight]
  exact Subgroup.card_dvd_of_injective ρ hρ

end CFSG.OddStandard.Seitz77
