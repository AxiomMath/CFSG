module

public import CFSG.ClassicalInvolution.Generic.StepOdd
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

inductive MemberType : Type
  | sl2 (p f : ℕ) : MemberType
  | twoA7 : MemberType

namespace MemberType

@[expose] def Admissible : MemberType → Prop
  | .sl2 p f => p.Prime ∧ p ≠ 2 ∧ 0 < f
  | .twoA7 => True

@[expose] def IsSolvableType : MemberType → Prop
  | .sl2 p f => p ^ f = 3
  | .twoA7 => False

@[expose] def Witness {Y : Type*} [Group Y] (t : MemberType) (L : Subgroup Y) : Prop :=
  match t with
  | .sl2 p f => ∃ _ : Fact p.Prime,
      Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, GaloisField p f))
  | .twoA7 => CFSG.Open.IsQuasisimple (L ⧸ classicalInvolutionOddCore L) ∧
      Nat.card (Subgroup.center (L ⧸ classicalInvolutionOddCore L)) = 2 ∧
      Nonempty ((L ⧸ classicalInvolutionOddCore L) ⧸
        Subgroup.center (L ⧸ classicalInvolutionOddCore L) ≃* alternatingGroup (Fin 7))

variable {Y : Type*} [Group Y]

theorem Witness.of_quotientEquiv {t : MemberType} {A B : Type*} [Group A] [Group B]
    {JA : Subgroup A} {JB : Subgroup B}
    (q : (JA ⧸ classicalInvolutionOddCore JA) ≃* (JB ⧸ classicalInvolutionOddCore JB))
    (h : t.Witness JA) : t.Witness JB := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h
    exact ⟨hp, ⟨q.symm.trans e⟩⟩
  | twoA7 =>
    have hZ : (Subgroup.center (JA ⧸ classicalInvolutionOddCore JA)).map q.toMonoidHom =
        Subgroup.center (JB ⧸ classicalInvolutionOddCore JB) := Subgroup.map_center_eq q
    obtain ⟨hqs, hcard, ⟨ψ⟩⟩ := h
    refine ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv q.symm hqs, ?_,
      ⟨(QuotientGroup.congr _ _ q hZ).symm.trans ψ⟩⟩
    rw [← hcard, ← hZ]
    exact Subgroup.card_map_of_injective q.injective

theorem Witness.of_mulEquiv {t : MemberType} {A B : Type*} [Group A] [Group B]
    {JA : Subgroup A} {JB : Subgroup B} (e : JA ≃* JB) (h : t.Witness JA) : t.Witness JB :=
  Witness.of_quotientEquiv (QuotientGroup.congr _ _ e
    (CFSG.ComponentClassification.OddCore.equiv_invariant e)) h

end MemberType

theorem three_le_pow_of_odd_prime {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f) :
    3 ≤ p ^ f := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact h3.trans (Nat.le_self_pow hf.ne' p)

theorem natCard_galoisField_eq {p f : ℕ} [Fact p.Prime] (hf : 0 < f) :
    Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'

theorem odd_natCard_galoisField_of_pos {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f) :
    Odd (Nat.card (GaloisField p f)) := by
  rw [natCard_galoisField_eq hf]
  exact (Fact.out (p := p.Prime) |>.odd_of_ne_two hp2).pow

structure IsClassicalMemberU (t : MemberType) {Y : Type} [Group Y] (L : Subgroup Y) (z : Y) :
    Prop where
  admissible : t.Admissible
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ L
  subnormal : IsSubnormal L (Subgroup.centralizer ({z} : Set Y))
  witness : t.Witness L
  perfect : ¬ t.IsSolvableType → Group.IsPerfect L

namespace IsClassicalMemberU

variable {t : MemberType} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem ne_one (h : IsClassicalMemberU t L z) : z ≠ 1 := by
  intro hz
  have h2 := h.orderOf_eq_two
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem mul_self (h : IsClassicalMemberU t L z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.orderOf_eq_two, pow_two] at this

theorem le_centralizer (h : IsClassicalMemberU t L z) :
    L ≤ Subgroup.centralizer ({z} : Set Y) :=
  isSubnormal_le h.subnormal

theorem comm_of_mem (h : IsClassicalMemberU t L z) {k : Y} (hk : k ∈ L) : z * k = k * z :=
  (Subgroup.mem_centralizer_iff.mp (h.le_centralizer hk) z (Set.mem_singleton z))

theorem conj (h : IsClassicalMemberU t L z) (g : Y) :
    IsClassicalMemberU t (conjSub g L) (g * z * g⁻¹) where
  admissible := h.admissible
  orderOf_eq_two := by rw [orderOf_conj_eq]; exact h.orderOf_eq_two
  mem := conj_mem_conjSub h.mem
  subnormal := isSubnormal_map_conj_centralizer h.subnormal g
  witness := by
    let e : L ≃* conjSub g L :=
      L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact MemberType.Witness.of_mulEquiv e h.witness
  perfect hns := by
    have := h.perfect hns
    let e : L ≃* conjSub g L :=
      L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem subgroupOf (h : IsClassicalMemberU t L z) {H : Subgroup Y} (hLH : L ≤ H) :
    IsClassicalMemberU t (L.subgroupOf H) (⟨z, hLH h.mem⟩ : H) where
  admissible := h.admissible
  orderOf_eq_two := by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  mem := Subgroup.mem_subgroupOf.mpr h.mem
  subnormal := by
    have h1 : IsSubnormal L (Subgroup.centralizer ({z} : Set Y) ⊓ H) := by
      have := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hLH] at this
    have h2 : (Subgroup.centralizer ({z} : Set Y) ⊓ H).subgroupOf H =
        Subgroup.centralizer ({(⟨z, hLH h.mem⟩ : H)} : Set H) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h1 H
  witness := by
    let e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
    exact MemberType.Witness.of_mulEquiv e.symm h.witness
  perfect hns := by
    have := h.perfect hns
    let e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem map_oddQuotient [Finite Y] (h : IsClassicalMemberU t L z) :
    IsClassicalMemberU t (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) where
  admissible := h.admissible
  orderOf_eq_two := orderOf_mk_oddCore_eq_two h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    rw [← centralizer_map_oddCore h.orderOf_eq_two]
    exact CFSG.ComponentClassification.Components.chain_map _ h.subnormal
  witness :=
    MemberType.Witness.of_quotientEquiv
      (CFSG.ComponentClassification.OddKernel.coreQuotientEquiv
        ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L)
        (MonoidHom.subgroupMap_surjective _ L) (oddCore_restriction_ker_odd L)) h.witness
  perfect hns := by
    have := h.perfect hns
    exact Group.IsPerfect.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))

end IsClassicalMemberU

end CFSG.ClassicalInvolution.Uniform
