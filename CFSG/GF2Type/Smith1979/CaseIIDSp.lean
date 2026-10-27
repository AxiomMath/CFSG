module

public import CFSG.GF2Type.Smith1979.CaseIIDCrit
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open CFSG.Open CFSG.RankThree.Classical
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem not_critII_sp62 {X : Type} [Group X] (h : StatedClassicalModel X .PSp 3 2 1) :
    ¬ CritII X := by
  rintro ⟨σ, -, hσ, -⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hout := (higher_symplectic_outer_order_divides_field_multiplier_bound Nat.prime_two
    le_rfl le_rfl hK).1
  have h1 : Nat.card (Outer X) = 1 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact Nat.dvd_one.mp (by simpa using hout)
  have hsub : Subsingleton (Outer X) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hmem : σ ∈ inner X :=
    (QuotientGroup.eq_one_iff σ).mp (Subsingleton.elim (QuotientGroup.mk σ : Outer X) 1)
  obtain ⟨x, hx⟩ := hmem
  exact hσ x hx.symm

end CFSG.GF2Type.Smith1979.Case2
