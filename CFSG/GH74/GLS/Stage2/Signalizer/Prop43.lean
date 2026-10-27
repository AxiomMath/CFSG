module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section CharNormal

variable {A : Type} [Group A]

theorem pCore_map_le (K : Subgroup A) [K.Normal] (q : ℕ) :
    (pCore q ↥K).map K.subtype ≤ pCore q A := by
  have hmem : (pCore q ↥K).map K.subtype ∈ {M : Subgroup A | M.Normal ∧ IsPGroup q M} := by
    refine ⟨⟨?_⟩, (pCore_isPGroup (p := q) (G := ↥K)).map K.subtype⟩
    rintro n ⟨y, hy, rfl⟩ g
    refine ⟨MulAut.conjNormal g y, ?_, ?_⟩
    · have hfix := (inferInstance : (pCore q ↥K).Characteristic).fixed (MulAut.conjNormal g)
      have : y ∈ (pCore q ↥K).comap (MulAut.conjNormal g).toMonoidHom := by rw [hfix]; exact hy
      exact this
    · simp
  exact le_sSup hmem

end CharNormal

end CFSG.GH74.GLS.Stage2.Signalizer
