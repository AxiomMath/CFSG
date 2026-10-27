module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup
open scoped MatrixGroups

private theorem not_isPerfect_sl2_zmod_three : ¬ Group.IsPerfect SL(2, ZMod 3) := by
  intro h
  haveI : Nontrivial SL(2, ZMod 3) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [CFSG.ClassicalInvolution.natCard_sl2Three]
    norm_num)
  have hsolv : Group.IsSolvable SL(2, ZMod 3) :=
    CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_card_two_three (a := 3) (b := 1) (by
      rw [CFSG.ClassicalInvolution.natCard_sl2Three]
      norm_num)
  exact Group.IsPerfect.not_isSolvable SL(2, ZMod 3) hsolv


theorem oddLieOrder_of_isMTypeSchur {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Group L]
    (hperf : Group.IsPerfect L) (hM : IsMTypeSchur p L) :
    OddLieOrder (Nat.card (L ⧸ Open.fusionZStar L)) := by
  rcases hM with ⟨-, ⟨τ, n, f, hm⟩, -, -⟩ | ⟨-, ⟨e⟩⟩
  · exact oddLieOrder_of_lieModel hp hp2 hm
  · exfalso
    haveI := hperf
    have hperfQ : Group.IsPerfect (L ⧸ pPrimeCore 2 L) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 L))
        (QuotientGroup.mk'_surjective (pPrimeCore 2 L))
    haveI := hperfQ
    exact not_isPerfect_sl2_zmod_three
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
