module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.NoncommCoprod

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {M : Type*} [Group M]

theorem isNilpotent_sup_of_disjoint_of_le_centralizer {H U : Subgroup M}
    [Group.IsNilpotent H] [Group.IsNilpotent U] (hdisj : Disjoint H U)
    (hcent : U ≤ centralizer (H : Set M)) : Group.IsNilpotent (H ⊔ U : Subgroup M) := by
  have comm : ∀ (x : H) (y : U), Commute (H.subtype x) (U.subtype y) := fun x y =>
    Subgroup.mem_centralizer_iff.mp (hcent y.2) _ x.2
  have hinj : Function.Injective (H.subtype.noncommCoprod U.subtype comm) := fun a b hab =>
    Subgroup.mul_injective_of_disjoint hdisj (by simpa using hab)
  have hrange : (H.subtype.noncommCoprod U.subtype comm).range = H ⊔ U := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact Group.nilpotent_of_mulEquiv
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))

theorem not_le_centralizer_of_isMaximalNilpotentNormalHall
    {H J U B : Subgroup M} [H.Normal] [J.Normal]
    [Group.IsNilpotent H] [Group.IsNilpotent U]
    (_hHhall : (Nat.card H).Coprime H.index)
    (hHmax : ∀ K : Subgroup M, Group.IsNilpotent K → K.Normal →
      (Nat.card K).Coprime K.index → K ≤ H)
    (hJB : J.IsComplement' B) (hBhall : (Nat.card B).Coprime B.index)
    (hsup : H ⊔ U = J) (hdisj : Disjoint H U) (hU : U ≠ ⊥) :
    ¬ U ≤ centralizer (H : Set M) := by
  intro hcent
  have hJnil : Group.IsNilpotent J :=
    hsup ▸ isNilpotent_sup_of_disjoint_of_le_centralizer hdisj hcent
  have hJidx : J.index = Nat.card B := hJB.symm.index_eq_card
  have hBidx : B.index = Nat.card J := hJB.index_eq_card
  have hJhall : (Nat.card J).Coprime J.index := by
    rw [hJidx]; rw [hBidx] at hBhall; exact hBhall.symm
  have hUH : U ≤ H := (hsup ▸ le_sup_right : U ≤ J).trans (hHmax J hJnil ‹_› hJhall)
  exact hU (le_bot_iff.mp (le_trans (le_inf hUH le_rfl) hdisj.le_bot))

theorem exists_not_commute_of_isMaximalNilpotentNormalHall
    {H J U B : Subgroup M} [H.Normal] [J.Normal]
    [Group.IsNilpotent H] [Group.IsNilpotent U]
    (hHhall : (Nat.card H).Coprime H.index)
    (hHmax : ∀ K : Subgroup M, Group.IsNilpotent K → K.Normal →
      (Nat.card K).Coprime K.index → K ≤ H)
    (hJB : J.IsComplement' B) (hBhall : (Nat.card B).Coprime B.index)
    (hsup : H ⊔ U = J) (hdisj : Disjoint H U) (hU : U ≠ ⊥) :
    ∃ u ∈ U, ∃ h ∈ H, ¬ Commute u h := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact not_le_centralizer_of_isMaximalNilpotentNormalHall hHhall hHmax hJB hBhall hsup hdisj hU
    fun u hu => mem_centralizer_iff.2 fun h hh => (hc u hu h hh).symm

end CFSG.FeitThompson
