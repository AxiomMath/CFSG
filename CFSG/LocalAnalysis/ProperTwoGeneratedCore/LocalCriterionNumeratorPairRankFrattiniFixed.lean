module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorDecomposition
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorOrder

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

variable {A : Type u} [Group A]
variable {P : Type v} [Group P] [Finite P] [MulDistribMulAction A P]

@[expose, reducible]
def frattiniQuotientAction : MulDistribMulAction A (P ⧸ frattini P) :=
  quotientMulDistribMulAction (frattini P) (isInvariant_of_characteristic (frattini P))

theorem frattini_kernel_structure {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hpodd : Odd p) :
    (frattini P).Characteristic ∧ Group.IsSolvable (frattini P) ∧
      Odd (Nat.card (frattini P)) ∧ IsElementaryAbelian p (P ⧸ frattini P) ∧
        Odd (Nat.card (P ⧸ frattini P)) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hPodd : Odd (Nat.card P) := by
    rw [hn]
    exact hpodd.pow
  let : Group.IsNilpotent P := hP.isNilpotent
  exact ⟨inferInstance, inferInstance,
    hPodd.of_dvd_nat (frattini P).card_subgroup_dvd_card,
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1,
    hPodd.of_dvd_nat (frattini P).card_quotient_dvd_card⟩

theorem frattini_fixed_quotient_eq_image [Finite A] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hpodd : Odd p) (w : A) (hw : w ^ 2 = 1) :
    let := frattiniQuotientAction (A := A) (P := P)
    actorFixedSubgroup (I := P ⧸ frattini P) w =
      (actorFixedSubgroup (I := P) w).map (QuotientGroup.mk' (frattini P)) := by
  let := frattiniQuotientAction (A := A) (P := P)
  have hs := frattini_kernel_structure hP hpodd
  let : MulDistribMulAction (Subgroup.zpowers w) P :=
    MulDistribMulAction.compHom P (Subgroup.zpowers w).subtype
  have hinv : IsInvariant (Subgroup.zpowers w) P (frattini P) :=
    isInvariant_of_characteristic (frattini P)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers w)) (Nat.card (frattini P)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one hw)
      hs.2.2.1.coprime_two_left
  have hlift := SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    (A := Subgroup.zpowers w) (frattini P) hinv hs.2.1 hcop
  simpa only [fixedPointSubgroup_zpowers_eq_actorFixed] using hlift

omit [Finite P] in
theorem frattini_commutator_image (t : A)
    (ht : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹) (a : P) :
    QuotientGroup.mk' (frattini P) (a⁻¹ * (t • a)) =
      (QuotientGroup.mk' (frattini P) a)⁻¹ *
        (QuotientGroup.mk' (frattini P) a)⁻¹ := by
  let := frattiniQuotientAction (A := A) (P := P)
  calc
    _ = (QuotientGroup.mk' (frattini P) a)⁻¹ *
        (t • QuotientGroup.mk' (frattini P) a) := by rfl
    _ = _ := by rw [ht]

theorem frattini_fixed_eq_commutator_image [Finite A] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hpodd : Odd p) (w t : A) (hw : w ^ 2 = 1)
    (hwt : Commute w t)
    (ht : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹) :
    let := frattiniQuotientAction (A := A) (P := P)
    actorFixedSubgroup (I := P ⧸ frattini P) w =
      (actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)).map
        (QuotientGroup.mk' (frattini P)) := by
  let := frattiniQuotientAction (A := A) (P := P)
  let K := actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)
  let q := QuotientGroup.mk' (frattini P)
  have hK : K ≤ actorFixedSubgroup (I := P) w := by
    apply (actorCommutatorSubgroup_le t _ _).2
    intro a ha
    change w • (a⁻¹ * (t • a)) = a⁻¹ * (t • a)
    have hwa : w • a = a := ha
    rw [smul_mul', smul_inv', ← mul_smul, hwt.eq, mul_smul, hwa]
  have hfixed := frattini_fixed_quotient_eq_image hP hpodd w hw
  apply le_antisymm
  · intro x hx
    rw [hfixed] at hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have hgen : q (a⁻¹ * (t • a)) ∈ K.map q :=
      Subgroup.mem_map.mpr ⟨a⁻¹ * (t • a),
        actorCommutatorSubgroup_generator_mem t ha, rfl⟩
    rw [frattini_commutator_image t ht a, hax] at hgen
    apply odd_square_mem_implies_mem (frattini_kernel_structure hP hpodd).2.2.2.2
    have hinv := (K.map q).inv_mem hgen
    simpa only [mul_inv_rev, inv_inv, pow_two] using hinv
  · rw [hfixed]
    exact Subgroup.map_mono hK

theorem frattini_cyclic_fixed_card [Finite A] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hpodd : Odd p) (w t : A) (hw : w ^ 2 = 1)
    (hwt : Commute w t)
    (ht : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹)
    (hcyclic : IsCyclic (actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w))) :
    let := frattiniQuotientAction (A := A) (P := P)
    IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) ∧
      Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ∣ p ∧
        Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ≤ p := by
  let := frattiniQuotientAction (A := A) (P := P)
  let K := actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)
  let q := QuotientGroup.mk' (frattini P)
  let : IsCyclic K := hcyclic
  have himage : IsCyclic (K.map q) :=
    isCyclic_of_surjective (q.subgroupMap K) (q.subgroupMap_surjective K)
  have hfixed := frattini_fixed_eq_commutator_image hP hpodd w t hw hwt ht
  have hcyc : IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) := by
    rw [hfixed]
    exact himage
  let := hcyc
  have hexp : Monoid.exponent (actorFixedSubgroup (I := P ⧸ frattini P) w) ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact (GroupTheory.frattini_elementary_quotient hP).2.2.1 x.val
  have hcard : Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ∣ p := by
    rwa [IsCyclic.exponent_eq_card] at hexp
  exact ⟨hcyc, hcard, Nat.le_of_dvd (Fact.out : p.Prime).pos hcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
