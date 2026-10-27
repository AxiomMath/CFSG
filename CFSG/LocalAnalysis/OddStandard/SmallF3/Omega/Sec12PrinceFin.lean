module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceAb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceZ4

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

namespace PrinceData

variable {B V H : Subgroup G} {φ φ₀ : (Fin 5 → ZMod 2) → G}

theorem conclusion [Finite G] (hP : PrinceData B V H φ φ₀) : IsElemAb2 V 8 ∨ IsZ4Pow4 V := by
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => hP.abelian hx hy
  have hcard : Nat.card ↥V = 256 := hP.card_V
  rcases hP.sq_dichotomy with h | h
  · refine Or.inl ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · exact Subtype.ext (hab a.1 a.2 b.1 b.2)
    · rw [pow_two]
      exact h x hx
    · rw [hcard]
      norm_num
  · refine Or.inr (prince_z4_of_sq V φ φ₀ hab hcard hP.mod.2.2.2.2.1 ?_ ?_ h)
    · exact hP.via.1
    · exact hP.via.2.1

end PrinceData

end CFSG.OddStandard.SmallF3.Omega
