module

public import CFSG.ClassicalInvolution.Uniform.U4Resid
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Uniform.UBranch
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement

@[expose] def DiagInputNorm (F : Type) [Group F] [Finite F] : Prop :=
  ∀ {Q : Subgroup F} {r u : F}, Mem3 Q r → u * u = 1 → u * r = r * u → Q ≠ conjSub u Q →
    ∀ {I : Subgroup F}, Mem3 I u → r ∈ Subgroup.normalizer (I : Set F) →
      ∀ {q : F}, q ∈ Q → IsPGroup 2 (Subgroup.zpowers q) →
        q * (u * q * u⁻¹) = (u * q * u⁻¹) * q →
          q * (u * q * u⁻¹) ∈ Subgroup.normalizer (I : Set F)

structure Fusion3Min (F : Type) [Group F] [Finite F] : Prop where
  symOuter : SymOuterInput F
  diagNorm : DiagInputNorm F

@[expose] def Fusion3MinAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    Fusion3Min G

@[expose] def invClass {F : Type} [Group F] (z : F) : Set F := {x | ∃ g : F, g * z * g⁻¹ = x}

@[expose] def SymOuterOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {X Y : Subgroup F} {x y : F}, Mem3 X x → Mem3 Y y → x ∈ S → y ∈ S →
    x ∈ Subgroup.normalizer (Y : Set F) → (∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) →
      y ∈ Subgroup.normalizer (X : Set F)

@[expose] def DiagInputNormOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {Q : Subgroup F} {r u : F}, Mem3 Q r → r ∈ S → u ∈ S → u * u = 1 → u * r = r * u →
    Q ≠ conjSub u Q → ∀ {I : Subgroup F}, Mem3 I u → r ∈ Subgroup.normalizer (I : Set F) →
      ∀ {q : F}, q ∈ Q → IsPGroup 2 (Subgroup.zpowers q) →
        q * (u * q * u⁻¹) = (u * q * u⁻¹) * q →
          q * (u * q * u⁻¹) ∈ Subgroup.normalizer (I : Set F)

structure Fusion3MinOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop where
  symOuter : SymOuterOn F S
  diagNorm : DiagInputNormOn F S

section Implications

variable {F : Type} [Group F] [Finite F]

theorem fusion3MinOn_of_min (S : Set F) (h : Fusion3Min F) : Fusion3MinOn F S where
  symOuter := by
    intro X Y x y hX hY _ _ hxY hout
    exact h.symOuter hX hY hxY hout
  diagNorm := by
    intro Q r u hQ _ _ hu2 hur hne I hI hrI q hq hq2 hqc
    exact h.diagNorm hQ hu2 hur hne hI hrI hq hq2 hqc

end Implications

section Branch

@[expose] def Fusion3MinBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU 3 1 K z → Fusion3MinOn G (invClass z)

theorem fusion3MinBranch_of_all (h : Fusion3MinAll) : Fusion3MinBranch :=
  fun G _ _ _ _ _ hb => fusion3MinOn_of_min _ (h G hb.nonabelian)

end Branch

end CFSG.ClassicalInvolution.Q3.Q3T6X
