module

public import CFSG.LargeExtraspecial.S5Syl
public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

@[expose] def TwoCentralBar (S : Setting G) (t : S.O) : Prop :=
  ∃ T : Subgroup S.O, S5.IsSylowTwoIn T S.Mbar ∧ ∀ x ∈ T, x * t = t * x

@[expose] noncomputable def NLbar (S : Setting G) (g : G) : Subgroup S.O :=
  S.Mbar ⊓ normalizer (S.Lbar g : Set S.O)

@[expose] noncomputable def Delta (S : Setting G) (g : G) (t : S.O) : Set S.O :=
  {x | ∃ n ∈ NLbar S g, x = n * t * n⁻¹}

theorem mem_Delta_self (S : Setting G) (g : G) (t : S.O) : t ∈ Delta S g t :=
  ⟨1, one_mem _, by group⟩

open Module in
@[expose] def CountSixStmt : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] (Q : QuadraticForm (ZMod 2) W),
    finrank (ZMod 2) W = 6 → (QuadraticMap.polarBilin Q).Nondegenerate → ∀ a : W, a ≠ 0 → Q a = 0 →
      (∀ D : Submodule (ZMod 2) W, a ∈ D → (∀ d ∈ D, QuadraticMap.polar Q a d = 0) →
        4 ≤ finrank (ZMod 2) D →
          (∃ x ∈ D, Q x = 0 ∧ x ≠ 0 ∧ x ≠ a) ∧
          ((∀ x ∈ D, ∀ y ∈ D, Q x = 0 → Q y = 0 → x ≠ 0 → x ≠ a → y ≠ 0 → y ≠ a →
              x = y ∨ x = y + a) →
            Set.ncard {v : W | v ≠ 0 ∧ Q v = 0} = 27)) ∧
      (Set.ncard {v : W | v ≠ 0 ∧ Q v = 0} = 27 →
        Set.ncard {x : W | QuadraticMap.polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a} = 10)

end CFSG.GF2Type.Smith1979
