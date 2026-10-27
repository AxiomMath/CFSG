module

public import CFSG.Holt.H78.StartAssembly
public import CFSG.Holt.H78.Section4Defs
import CFSG.Holt.H78.DataPrimitive
import CFSG.Holt.H78.KernelSplit

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General

section Step

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem holtStructure_of_below_of_pPrimeCore_eq_bot (h4 : HoltSection4Statement)
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    (hO : CFSG.pPrimeCore 2 G = ⊥) : HoltStructure G Ω := by
  by_cases hH : jHull G Ω = ⊤
  · by_cases hprim : IsPreprimitive G Ω
    · let := Fintype.ofFinite Ω
      let := Classical.decEq Ω
      exact holtStructure_of_alternatingGroup_le_or_isBenderNormal hG.longInv_nonempty hH hO
        (h4 G Ω hG hprim hH hO hB)
    · exact holtStructure_of_not_isPreprimitive hG hB hH hO hprim
  · exact holtStructure_of_jHull_ne_top hG hB hH

end Step

theorem holtTheorem1Below_of_step
    (hstep : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω]
      [FaithfulSMul G Ω], IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω) →
        HoltStructure G Ω) (n d : ℕ) : HoltTheorem1Below n d := by
  induction n using Nat.strong_induction_on generalizing d with
  | _ n ihn =>
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro G _ _ Ω _ _ _ hlt hG
      refine hstep G Ω hG ?_
      rcases hlt with hlt | ⟨rfl, hlt⟩
      · exact ihn _ hlt _
      · exact ihd _ hlt

theorem holtTheorem1_of_step
    (hstep : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω]
      [FaithfulSMul G Ω], IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω) →
        HoltStructure G Ω) : HoltTheorem1 :=
  fun G _ _ Ω _ _ _ hG => hstep G Ω hG (holtTheorem1Below_of_step hstep _ _)

section Theorem1

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem holtStructure_of_pPrimeCore_ne_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hO : CFSG.pPrimeCore 2 G ≠ ⊥) :
    HoltStructure G Ω :=
  holtStructure_of_pPrimeCore_ne_bot_of_below hG hO hB

theorem holtStructure_of_below (h4 : HoltSection4Statement) (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) : HoltStructure G Ω := by
  by_cases hO : CFSG.pPrimeCore 2 G = ⊥
  · exact holtStructure_of_below_of_pPrimeCore_eq_bot h4 hG hB hO
  · exact holtStructure_of_pPrimeCore_ne_bot hG hB hO

end Theorem1

theorem holtTheorem1_of_section4 (h4 : HoltSection4Statement) : HoltTheorem1 :=
  holtTheorem1_of_step fun _ _ _ _ _ _ _ hG hB => holtStructure_of_below h4 hG hB

end CFSG.Holt.H78
