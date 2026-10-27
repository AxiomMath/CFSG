module

public import CFSG.ClassicalInvolution.Uniform.UMember
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

namespace MemberType

@[expose] def Cert : MemberType → Prop
  | .sl2 _ _ => True
  | .twoA7 => True

theorem cert_sl2 (p f : ℕ) : (MemberType.sl2 p f).Cert := trivial

theorem isSolvableType_sl2 {p f : ℕ} : (MemberType.sl2 p f).IsSolvableType ↔ p ^ f = 3 := Iff.rfl

theorem not_isSolvableType_twoA7 : ¬ MemberType.twoA7.IsSolvableType := fun h => h

end MemberType

namespace IsClassicalMemberU

variable {t : MemberType} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem nonempty_equiv_sl2 {p f : ℕ} [Fact p.Prime] (h : IsClassicalMemberU (.sl2 p f) L z) :
    Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, GaloisField p f)) := by
  obtain ⟨_, e⟩ := h.witness
  exact e

theorem sl2_admissible {p f : ℕ} (h : IsClassicalMemberU (.sl2 p f) L z) :
    p.Prime ∧ p ≠ 2 ∧ 0 < f := h.admissible

theorem isUniqueInvolution_of_forall (h : IsClassicalMemberU t L z)
    (hu : ∀ w ∈ L, orderOf w = 2 → w = z) : IsUniqueInvolution L z where
  mem := h.mem
  ne_one := h.ne_one
  sq := h.mul_self
  unique y hy hy2 := by
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · refine Or.inr (hu y hy ?_)
      exact orderOf_eq_prime (by rwa [pow_two]) hy1

theorem isUniqueInvolution_sl2 [Finite Y] {p f : ℕ} (h : IsClassicalMemberU (.sl2 p f) L z) :
    IsUniqueInvolution L z := by
  obtain ⟨hp, ⟨e⟩⟩ := h.witness
  have := hp
  have hodd := odd_natCard_galoisField_of_pos h.admissible.2.1 h.admissible.2.2
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  refine h.isUniqueInvolution_of_forall fun y hy hy2 => ?_
  set y' : L := ⟨y, hy⟩ with hy'
  set z' : L := ⟨z, h.mem⟩ with hz'
  have hz'c : ∀ l : L, l * z' = z' * l := fun l => Subtype.ext (h.comm_of_mem l.2).symm
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hy'2 : orderOf y' = 2 := by rw [hy', Subgroup.orderOf_mk]; exact hy2
  have hρy := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
    (QuotientGroup.mk' (classicalInvolutionOddCore L) y')).mp (orderOf_mk_oddCore_eq_two hy'2)
  have hρz := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
    (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp (orderOf_mk_oddCore_eq_two hz'2)
  have hmem : z'⁻¹ * y' ∈ classicalInvolutionOddCore L :=
    QuotientGroup.eq.mp (hρz.trans hρy.symm)
  have hzz : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'2, pow_two] at this
  have hyy : y' * y' = 1 := by
    have := pow_orderOf_eq_one y'
    rwa [hy'2, pow_two] at this
  have hyo : y' = z' * (z'⁻¹ * y') := by group
  set o : L := z'⁻¹ * y' with ho
  have hoo : o * o = 1 := by
    have h1 : (z' * o) * (z' * o) = (z' * z') * (o * o) := by
      calc (z' * o) * (z' * o) = z' * (o * z') * o := by group
        _ = z' * (z' * o) * o := by rw [hz'c o]
        _ = (z' * z') * (o * o) := by group
    rw [← hyo, hyy, hzz, one_mul] at h1
    exact h1.symm
  have ho1 : o = 1 := by
    by_contra ho1
    exact ho1 (eq_one_of_mem_odd_of_orderOf_eq_two_pow hOodd hmem (k := 1)
      (by rw [pow_one]; exact orderOf_eq_prime (by rwa [pow_two]) ho1))
  rw [ho1, mul_one] at hyo
  exact congrArg Subtype.val hyo

theorem isUniqueInvolution_twoA7 [Finite Y]
    (h : IsClassicalMemberU .twoA7 L z) : IsUniqueInvolution L z :=
  h.isUniqueInvolution_of_forall
    (Hat2A7.unique_involution_of_witness h.witness h.orderOf_eq_two h.mem
      fun _ hk => (h.comm_of_mem hk).symm)

theorem isUniqueInvolution [Finite Y] (hc : t.Cert) (h : IsClassicalMemberU t L z) :
    IsUniqueInvolution L z := by
  cases t with
  | sl2 p f => exact h.isUniqueInvolution_sl2
  | twoA7 =>
    exact h.isUniqueInvolution_twoA7

theorem natCard_center_eq_two (h : IsClassicalMemberU t L z) :
    Nat.card (Subgroup.center (L ⧸ classicalInvolutionOddCore L)) = 2 := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h.witness
    have := hp
    exact natCard_center_of_equiv_sl2
      (odd_natCard_galoisField_of_pos h.admissible.2.1 h.admissible.2.2) e
  | twoA7 => exact h.witness.2.1

theorem nonempty_equiv_sl2Three (h : IsClassicalMemberU t L z) (hs : t.IsSolvableType) :
    Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, ZMod 3)) := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h.witness
    have := hp
    have h3 : Nat.card (GaloisField p f) = 3 := by
      rw [natCard_galoisField_eq h.admissible.2.2]
      exact hs
    obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
    exact ⟨e.trans e'⟩
  | twoA7 => exact absurd hs MemberType.not_isSolvableType_twoA7

theorem isQuasisimple_quot (h : IsClassicalMemberU t L z) (hns : ¬ t.IsSolvableType) :
    CFSG.Open.IsQuasisimple (L ⧸ classicalInvolutionOddCore L) := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h.witness
    have := hp
    have h3 : 3 ≤ p ^ f :=
      three_le_pow_of_odd_prime h.admissible.1 h.admissible.2.1 h.admissible.2.2
    have hns' : p ^ f ≠ 3 := hns
    have h4 : 4 ≤ Nat.card (GaloisField p f) := by
      rw [natCard_galoisField_eq h.admissible.2.2]
      omega
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
      (isQuasisimple_specialLinearGroup_two h4)
  | twoA7 => exact h.witness.1

theorem natCard_quot_twoA7 (h : IsClassicalMemberU .twoA7 L z) :
    Nat.card (L ⧸ classicalInvolutionOddCore L) = 5040 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h.witness
  set Q := L ⧸ classicalInvolutionOddCore L
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
  rw [hc, Nat.card_congr e.toEquiv] at h1
  have h2 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h2] at h1
  omega

theorem natCard_quot_eq {L' : Subgroup Y} {z' : Y} (h : IsClassicalMemberU t L z)
    (h' : IsClassicalMemberU t L' z') :
    Nat.card (L ⧸ classicalInvolutionOddCore L) =
      Nat.card (L' ⧸ classicalInvolutionOddCore L') := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h.witness
    obtain ⟨hp', ⟨e'⟩⟩ := h'.witness
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv]
  | twoA7 => rw [h.natCard_quot_twoA7, h'.natCard_quot_twoA7]

end IsClassicalMemberU

end CFSG.ClassicalInvolution.Uniform
