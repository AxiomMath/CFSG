module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EModel

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

structure Ctx (G : Type) [Group G] where
  t : G
  t_sq : t * t = 1
  Φ : ↥(centralizer ({t} : Set G)) →* Cm
  inj : Function.Injective Φ
  mem_Am : ∀ x, Φ x ∈ Am
  surj : ∀ a ∈ Am, ∃ x, Φ x = a
  map_t : Φ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ = tauH
  I2 : ∀ x : ↥(centralizer ({t} : Set G)),
    (∃ g : G, g * t * g⁻¹ = (x : G)) ↔
      (Φ x = tauH ∨ ∃ l, IsLong l ∧ Φ x = tauH * inA l)

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
