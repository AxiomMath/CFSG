module

public import Mathlib.GroupTheory.Frattini
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.FrattiniNongenerators
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {P : Type*} [Group P] {p n : ℕ}

theorem isInvariantSubgroup_of_characteristic {A : Type*} [Group A] (ρ : A →* MulAut P)
    (N : Subgroup P) [N.Characteristic] : IsInvariantSubgroup ρ N :=
  isInvariantSubgroup_iff_forall_map_eq.2 fun b =>
    Subgroup.characteristic_iff_map_eq.1 ‹N.Characteristic› (ρ b)

def frattiniQuotientAut (P : Type*) [Group P] : MulAut P →* MulAut (P ⧸ frattini P) :=
  (isInvariantSubgroup_of_characteristic (MonoidHom.id (MulAut P)) (frattini P)).quotientAut

@[simp]
theorem frattiniQuotientAut_apply_mk (a : MulAut P) (x : P) :
    frattiniQuotientAut P a (QuotientGroup.mk x) = (QuotientGroup.mk (a x) : P ⧸ frattini P) :=
  IsInvariantSubgroup.quotientAut_mk _ a x

def autKerFrattini (P : Type*) [Group P] : Subgroup (MulAut P) := (frattiniQuotientAut P).ker

theorem autKerFrattini_eq_ker : autKerFrattini P = (frattiniQuotientAut P).ker := (rfl)

theorem mem_autKerFrattini {a : MulAut P} :
    a ∈ autKerFrattini P ↔ ∀ x : P, (QuotientGroup.mk (a x) : P ⧸ frattini P) = x := by
  rw [autKerFrattini, MonoidHom.mem_ker]
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · have h2 : frattiniQuotientAut P a (QuotientGroup.mk x) = (1 : MulAut (P ⧸ frattini P)) x := by
      rw [h]
    rwa [frattiniQuotientAut_apply_mk, MulAut.one_apply] at h2
  · ext x
    induction x using QuotientGroup.induction_on with
    | H v => rw [frattiniQuotientAut_apply_mk, MulAut.one_apply]; exact h v

theorem mem_autKerFrattini_iff_smul_eq {a : MulAut P} :
    a ∈ autKerFrattini P ↔ ∀ x : P, a x • (frattini P : Set P) = x • (frattini P : Set P) :=
  mem_autKerFrattini.trans
    (forall_congr' fun _ => by rw [leftCoset_eq_iff, QuotientGroup.eq])

theorem mem_autKerFrattini_iff_inv_mul_mem {a : MulAut P} :
    a ∈ autKerFrattini P ↔ ∀ x : P, (a x)⁻¹ * x ∈ frattini P :=
  mem_autKerFrattini.trans (forall_congr' fun _ => QuotientGroup.eq)

instance autKerFrattini_normal : (autKerFrattini P).Normal := (frattiniQuotientAut P).normal_ker

theorem autKerFrattini_eq_bot_of_subsingleton [Subsingleton P] : autKerFrattini P = ⊥ := by
  rw [eq_bot_iff]
  intro a _
  rw [Subgroup.mem_bot]
  ext x
  exact Subsingleton.elim _ _

theorem eq_one_of_mem_autKerFrattini_of_coprime [Finite P] [Group.IsSolvable P] {a : MulAut P}
    (ha : a ∈ autKerFrattini P) (hcop : (orderOf a).Coprime (Nat.card P)) : a = 1 := by
  set A : Subgroup (MulAut P) := Subgroup.zpowers a with hAdef
  set ρ : ↥A →* MulAut P := A.subtype with hρ
  have hAsolv : Group.IsSolvable ↥A :=
    Group.isSolvable_of_comm fun x y => (Subgroup.zpowers_isMulCommutative a).is_comm.comm x y
  have hN : IsInvariantSubgroup ρ (frattini P) := isInvariantSubgroup_of_characteristic ρ _
  have hcopA : (Nat.card ↥A).Coprime (Nat.card P) := by rw [hAdef, Nat.card_zpowers]; exact hcop
  have hAle : A ≤ autKerFrattini P := Subgroup.zpowers_le.2 ha
  have hfix : ∀ x : P, ∀ b : ↥A, hN.quotientAut b (QuotientGroup.mk x) = QuotientGroup.mk x := by
    intro x b
    rw [hN.quotientAut_mk]
    exact mem_autKerFrattini.1 (hAle b.2) x
  have hC : FixedPoints.subgroup ρ.range P = ⊤ := by
    refine eq_top_of_mul_frattini_eq_univ (Y := FixedPoints.subgroup ρ.range P) ?_
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨v, hv, hvx⟩ := exists_mem_fixedPoints_range_mk_eq hN hcopA (hfix x)
    exact ⟨v, hv, v⁻¹ * x, QuotientGroup.eq.1 hvx, by group⟩
  ext x
  have hx : x ∈ FixedPoints.subgroup ρ.range P := hC ▸ Subgroup.mem_top x
  rw [mem_fixedPoints_range_iff] at hx
  rw [MulAut.one_apply]
  exact hx ⟨a, Subgroup.mem_zpowers a⟩

theorem isPGroup_autKerFrattini_of_isPGroup [Finite P] (hp : p.Prime) (hP : IsPGroup p P) :
    IsPGroup p (autKerFrattini P) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hP.isNilpotent
  have : Group.IsSolvable P := inferInstance
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors]
  intro q hq
  rw [Finset.mem_singleton]
  by_contra hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hborder : orderOf (b : MulAut P) = q := by rw [Subgroup.orderOf_coe]; exact hb
  have hcop : (orderOf (b : MulAut P)).Coprime (Nat.card P) := by
    rw [hborder]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
    rw [hm]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hqprime hp).2 hqp)
  have h1 := eq_one_of_mem_autKerFrattini_of_coprime b.2 hcop
  rw [h1, orderOf_one] at hborder
  exact hqprime.one_lt.ne' hborder.symm

theorem isPGroup_autKerFrattini (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    IsPGroup p (autKerFrattini P) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  exact isPGroup_autKerFrattini_of_isPGroup hp (IsPGroup.of_card hP)

theorem exists_card_autKerFrattini_eq (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    ∃ k, Nat.card (autKerFrattini P) = p ^ k := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card.1 (isPGroup_autKerFrattini hp hP)

end CFSG.FeitThompson
