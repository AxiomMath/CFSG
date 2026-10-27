module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Module Subgroup QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace InvolutionTrichotomy

section Group

open CFSG.RankThree.Literature.FSmith

variable {Q : Type*} [Group Q]

@[expose] def preim [Module (ZMod 2) (Additive (Abelianization Q))]
    (S : Submodule (ZMod 2) (Additive (Abelianization Q))) : Subgroup Q :=
  (AddSubgroup.toSubgroup' S.toAddSubgroup).comap Abelianization.of

theorem mem_preim [Module (ZMod 2) (Additive (Abelianization Q))]
    {S : Submodule (ZMod 2) (Additive (Abelianization Q))} {y : Q} :
    y ∈ preim S ↔ Additive.ofMul (Abelianization.of y) ∈ S :=
  AddSubgroup.mem_toSubgroup' _ _

theorem abelianization_of_surjective :
    Function.Surjective (Abelianization.of : Q →* Abelianization Q) :=
  fun a => by
    obtain ⟨y, hy⟩ := exists_ofMul_of (Additive.ofMul a)
    exact ⟨y, Additive.ofMul.injective hy⟩

variable (hQ : CFSG.IsExtraspecialPGroup 2 Q)
include hQ

theorem card_preim [Finite Q] [Module (ZMod 2) (Additive (Abelianization Q))]
    (S : Submodule (ZMod 2) (Additive (Abelianization Q))) :
    Nat.card (preim S) = 2 ^ finrank (ZMod 2) S * 2 := by
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  rw [preim, CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.card_comap_of_surjective
    abelianization_of_surjective, Abelianization.ker_of, hQ.2.1, hQ.2.2.2]
  congr 1
  rw [show (2 : ℕ) ^ finrank (ZMod 2) S = Nat.card S by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]]
  exact Nat.card_congr
    { toFun := fun g => ⟨Additive.ofMul (g : Abelianization Q),
        (AddSubgroup.mem_toSubgroup' _ _).1 g.2⟩
      invFun := fun v => ⟨Additive.toMul (v : Additive (Abelianization Q)),
        (AddSubgroup.mem_toSubgroup' _ _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {z : Q} (hz : zpowers z = center Q)
include hz

end Group

end InvolutionTrichotomy

end CFSG.LocalAnalysis.GorensteinLyons
