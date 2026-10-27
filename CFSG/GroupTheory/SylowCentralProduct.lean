module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.GroupTheory.CommutingConjugatePair

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.QuasithinUnique

variable {Y : Type} [Group Y] [Finite Y]

theorem isSylowTwoOf_sup_inf_of_odd_inf {L L' P : Subgroup Y}
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hodd : Odd (Nat.card ↥(L ⊓ L')))
    (hP : IsSylowTwoOf P (L ⊔ L')) :
    P = (P ⊓ L) ⊔ (P ⊓ L') ∧ IsSylowTwoOf (P ⊓ L) L ∧
      IsSylowTwoOf (P ⊓ L') L' := by
  have hL'C : L' ≤ Subgroup.centralizer (L : Set Y) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  have hLC : L ≤ Subgroup.centralizer (L' : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
  have hLn : L ⊔ L' ≤ Subgroup.normalizer (L : Set Y) :=
    sup_le Subgroup.le_normalizer (hL'C.trans (Subgroup.centralizer_le_normalizer _))
  have hL'n : L ⊔ L' ≤ Subgroup.normalizer (L' : Set Y) :=
    sup_le (hLC.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hB : IsSylowTwoOf (P ⊓ L) L :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hP le_sup_left hLn
  have hB' : IsSylowTwoOf (P ⊓ L') L' :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hP le_sup_right hL'n
  have hBc : ∀ a ∈ P ⊓ L, ∀ b ∈ P ⊓ L', a * b = b * a := fun a ha b hb => hcomm a ha.2 b hb.2
  have hBinf : (P ⊓ L) ⊓ (P ⊓ L') = ⊥ := by
    have hle : (P ⊓ L) ⊓ (P ⊓ L') ≤ L ⊓ L' := by
      rintro x ⟨hxPL, hxPL'⟩
      exact ⟨hxPL.2, hxPL'.2⟩
    have h := inf_eq_bot_of_isPGroup_two_of_odd (H := (P ⊓ L) ⊓ (P ⊓ L'))
      (K := L ⊓ L') hB.2.1.to_inf_left hodd
    rwa [inf_eq_left.mpr hle] at h
  have hQP : (P ⊓ L) ⊔ (P ⊓ L') ≤ P := sup_le inf_le_left inf_le_left
  have hQK : (P ⊓ L) ⊔ (P ⊓ L') ≤ L ⊔ L' := sup_le_sup inf_le_right inf_le_right
  have c1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L L' hcomm).1
  have c2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (P ⊓ L) (P ⊓ L') hBc).1
  rw [hBinf, Subgroup.card_bot, mul_one] at c2
  have c3 := Subgroup.relIndex_mul_card ((P ⊓ L) ⊔ (P ⊓ L')) (L ⊔ L')
  rw [inf_eq_left.2 hQK] at c3
  have c4 := Subgroup.relIndex_mul_card (P ⊓ L) L
  rw [inf_eq_left.2 inf_le_right] at c4
  have c5 := Subgroup.relIndex_mul_card (P ⊓ L') L'
  rw [inf_eq_left.2 inf_le_right] at c5
  have key : ((P ⊓ L) ⊔ (P ⊓ L')).relIndex (L ⊔ L') * Nat.card ↥(L ⊓ L') =
      (P ⊓ L).relIndex L * (P ⊓ L').relIndex L' := by
    have hpos : 0 < Nat.card ↥((P ⊓ L) ⊔ (P ⊓ L')) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc ((P ⊓ L) ⊔ (P ⊓ L')).relIndex (L ⊔ L') * Nat.card ↥(L ⊓ L') *
        Nat.card ↥((P ⊓ L) ⊔ (P ⊓ L'))
        = ((P ⊓ L) ⊔ (P ⊓ L')).relIndex (L ⊔ L') *
          Nat.card ↥((P ⊓ L) ⊔ (P ⊓ L')) * Nat.card ↥(L ⊓ L') := by ring
      _ = Nat.card ↥(L ⊔ L') * Nat.card ↥(L ⊓ L') := by rw [c3]
      _ = Nat.card ↥L * Nat.card ↥L' := c1
      _ = (P ⊓ L).relIndex L * (P ⊓ L').relIndex L' *
          (Nat.card ↥(P ⊓ L) * Nat.card ↥(P ⊓ L')) := by
          rw [← c4, ← c5]
          ring
      _ = (P ⊓ L).relIndex L * (P ⊓ L').relIndex L' *
          Nat.card ↥((P ⊓ L) ⊔ (P ⊓ L')) := by rw [c2]
  have hQ : IsSylowTwoOf ((P ⊓ L) ⊔ (P ⊓ L')) (L ⊔ L') := by
    refine ⟨hQK, hP.2.1.to_le hQP, ?_⟩
    show ¬ 2 ∣ ((P ⊓ L) ⊔ (P ⊓ L')).relIndex (L ⊔ L')
    have hoddA : Odd ((P ⊓ L).relIndex L) := by
      rw [Subgroup.relIndex]
      exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hB.2.2)
    have hoddB : Odd ((P ⊓ L').relIndex L') := by
      rw [Subgroup.relIndex]
      exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hB'.2.2)
    have hoddR : Odd ((P ⊓ L).relIndex L * (P ⊓ L').relIndex L') := hoddA.mul hoddB
    have hoddL : Odd (((P ⊓ L) ⊔ (P ⊓ L')).relIndex (L ⊔ L') * Nat.card ↥(L ⊓ L')) :=
      key ▸ hoddR
    exact (Nat.Odd.of_mul_left hoddL).not_two_dvd_nat
  have hEq : ((P ⊓ L) ⊔ (P ⊓ L')) = P :=
    CFSG.Quasithin.SBc6.eq_of_le_normalizer_of_isSylowTwoOf (Y := Y) hQ hP
      (hQP.trans Subgroup.le_normalizer)
  exact ⟨hEq.symm, hB, hB'⟩

end CFSG.GroupTheory
