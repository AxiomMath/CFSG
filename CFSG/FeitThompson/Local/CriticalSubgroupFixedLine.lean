module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.SolvableFrobeniusKernelNilpotent
import CFSG.FeitThompson.Local.FixedPointsNormalizedProductFixedFree
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {J : Type*} [Group J] {p q r : ℕ} {R Q P H : Subgroup J}

theorem natCard_eq_one_of_isPGroup_of_isPGroup {X : Type*} [Group X] [Finite X] (hq : q.Prime)
    (hr : r.Prime) (hqr : q ≠ r) (h1 : IsPGroup q X) (h2 : IsPGroup r X) : Nat.card X = 1 := by
  have := Fact.mk hq
  have := Fact.mk hr
  obtain ⟨a, ha⟩ := h1.exists_card_eq
  obtain ⟨b, hb⟩ := h2.exists_card_eq
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · simpa using ha
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hr).1
      (hq.dvd_of_dvd_pow (show q ∣ r ^ b by rw [← hb, ha]; exact dvd_pow_self q hpos.ne'))) hqr

theorem commutator_ne_bot_of_isPGroup_fixingSubgroup [Finite J] [R.Normal]
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (hQ : IsPGroup q ↥Q)
    (hfix : IsPGroup r ↥(fixingSubgroup (MulAut ↥R) ((H.subgroupOf R : Subgroup ↥R) : Set ↥R)))
    (hRQ : ⁅R, Q⁆ ≠ ⊥) : ⁅H, Q⁆ ≠ ⊥ := by
  intro hHQ
  set φ : ↥Q →* MulAut ↥R := (MulAut.conjNormal (H := R)).comp Q.subtype with hφ
  have hHc : H ≤ centralizer (Q : Set J) := commutator_eq_bot_iff_le_centralizer.1 hHQ
  have hle : φ.range ≤ fixingSubgroup (MulAut ↥R) ((H.subgroupOf R : Subgroup ↥R) : Set ↥R) := by
    rintro a ⟨x, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hcomm : (x : J) * (y : J) = (y : J) * (x : J) :=
      mem_centralizer_iff.1 (hHc (show (y : J) ∈ H from hy)) (x : J) x.2
    refine Subtype.ext ?_
    change ((MulAut.conjNormal (x : J) y : ↥R) : J) = (y : J)
    rw [MulAut.conjNormal_apply, hcomm]
    group
  have hqrange : IsPGroup q ↥φ.range := hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have htriv : φ.range = ⊥ := Subgroup.eq_bot_of_card_eq _
    (natCard_eq_one_of_isPGroup_of_isPGroup hq hr hqr hqrange (hfix.to_le hle))
  apply hRQ
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have hyR : y ∈ R := hy
  have hx1 : φ ⟨x, hx⟩ = 1 := by
    have hmem : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
    rwa [htriv, Subgroup.mem_bot] at hmem
  have hcj := congrArg (fun f : MulAut ↥R => ((f (⟨y, hyR⟩ : ↥R) : ↥R) : J)) hx1
  simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, coe_subtype] at hcj
  rw [MulAut.conjNormal_apply] at hcj
  simp only [MulAut.one_apply] at hcj
  calc y * x = (x * y * x⁻¹) * x := by rw [hcj]
    _ = x * y := by group

theorem isCyclic_of_elementaryAbelianPRank_le_one {X : Type*} [Group X] [Finite X] (hr : r.Prime)
    (hodd : Odd r) (hX : IsPGroup r X) (hrank : elementaryAbelianPRank r X ≤ 1) : IsCyclic X := by
  by_contra h
  exact absurd (two_le_elementaryAbelianPRank_of_not_isCyclic hr hodd hX h) (by omega)

theorem natCard_eq_of_isCyclic_of_forall_pow_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (hr : r.Prime) (hne : Nontrivial A) (hexp : ∀ x : A, x ^ r = 1) : Nat.card A = r := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hcard : Nat.card A = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hne1 : Nat.card A ≠ 1 := by
    have := Finite.one_lt_card_iff_nontrivial.2 hne
    omega
  rcases hr.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hexp g)) with h | h
  · exact absurd (hcard.trans h) hne1
  · exact hcard.trans h

theorem isNilpotent_of_isSolvable_of_le_normalizer [Finite J] {A E : Subgroup J}
    [Group.IsSolvable ↥A] (hAE : A ⊓ E = ⊥) (hE : E ≠ ⊥) (hEN : E ≤ normalizer (A : Set J))
    (hC : ∀ e ∈ E, e ≠ 1 → A ⊓ centralizer ({e} : Set J) = ⊥) : Group.IsNilpotent ↥A := by
  have hAn : ((A.subgroupOf (A ⊔ E))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hEN)
  have hsol : Group.IsSolvable ↥(A.subgroupOf (A ⊔ E)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (le_sup_left (a := A) (b := E))).toMonoidHom)
      (by simpa using (subgroupOfEquivOfLe (le_sup_left (a := A) (b := E))).injective)
  have hinf : A.subgroupOf (A ⊔ E) ⊓ E.subgroupOf (A ⊔ E) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf] at hx
    have hmem : (x : J) ∈ A ⊓ E := ⟨hx.1, hx.2⟩
    rw [hAE, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hEne : E.subgroupOf (A ⊔ E) ≠ ⊥ := fun h =>
    hE ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le le_sup_right)
  have hC' : ∀ e ∈ E.subgroupOf (A ⊔ E), e ≠ 1 →
      A.subgroupOf (A ⊔ E) ⊓ centralizer ({e} : Set ↥(A ⊔ E)) = ⊥ := by
    intro e he hne
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hx
    have hxc : (x : J) ∈ A ⊓ centralizer ({(e : J)} : Set J) :=
      Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val hx.2)⟩
    rw [hC _ (show (e : J) ∈ E from he) (fun h => hne (Subtype.ext h)), Subgroup.mem_bot] at hxc
    exact Subtype.ext hxc
  exact Group.nilpotent_of_mulEquiv
    (_h := isNilpotent_of_isSolvable_of_inf_centralizer_eq_bot (H := A.subgroupOf (A ⊔ E))
      (E := E.subgroupOf (A ⊔ E)) hinf hEne hC')
    (subgroupOfEquivOfLe (le_sup_left (a := A)))

theorem centralizer_singleton_eq_of_natCard_eq_prime [Finite J]
    (hp : p.Prime) (hP : Nat.card P = p) {e : J} (he : e ∈ P) (hne : e ≠ 1) :
    centralizer ({e} : Set J) = centralizer (P : Set J) := by
  have hgen : zpowers e = P := by
    have hdvd : orderOf e ∣ p := by
      rw [← hP]
      have hd : orderOf (⟨e, he⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
      simpa [Subgroup.orderOf_coe] using hd
    have hone : orderOf e ≠ 1 := by simpa [orderOf_eq_one_iff] using hne
    exact eq_of_le_of_card_ge (zpowers_le.2 he)
      (by rw [hP, Nat.card_zpowers, (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hone])
  rw [← hgen, zpowers_eq_closure, centralizer_closure]

theorem inf_centralizer_ne_bot_of_commutator_ne_bot [Finite J] [R.Normal] [H.Normal]
    [Group.IsSolvable ↥(H ⊔ Q)]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hR : IsPGroup r ↥R) (hQ : IsPGroup q ↥Q) (hPcard : Nat.card P = p)
    (hQn : (Q.subgroupOf (Q ⊔ P)).Normal) (hQPdisj : Q ⊓ P = ⊥)
    (hRdisj : R ⊓ (Q ⊔ P) = ⊥) (hCQP : Q ⊓ centralizer (P : Set J) = ⊥)
    (hHR : H ≤ R) (hHQ : ⁅H, Q⁆ ≠ ⊥) : H ⊓ centralizer (P : Set J) ≠ ⊥ := by
  have := Fact.mk hq
  have := Fact.mk hr
  intro hCH
  have hHQdisj : Disjoint H Q := by
    rw [Subgroup.disjoint_def]
    intro x hxH hxQ
    have hmem : x ∈ R ⊓ (Q ⊔ P) := ⟨hHR hxH, mem_sup_left hxQ⟩
    rw [hRdisj] at hmem
    exact hmem
  have hPQ : P ≤ normalizer (Q : Set J) :=
    le_sup_right.trans (le_normalizer_of_normal_subgroupOf (hK := hQn) le_sup_left)
  have hPH : P ≤ normalizer (H : Set J) := le_normalizer_of_normal (H := H)
  have hfix : (H ⊔ Q) ⊓ centralizer (P : Set J) = ⊥ := by
    rw [sup_inf_centralizer_eq_of_inf_centralizer_eq_bot normal_subgroupOf hHQdisj hPH hPQ hCQP,
      hCH]
  have hAE : (H ⊔ Q) ⊓ P = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxHQ : x ∈ (H ⊔ Q : Subgroup J) := hx.1
    have hxP : x ∈ P := hx.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul H Q] at hxHQ
    obtain ⟨h, hh, y, hy, rfl⟩ := hxHQ
    simp only [SetLike.mem_coe] at hh hy
    have hhQP : h ∈ Q ⊔ P := by
      have hrw : h = (h * y) * y⁻¹ := by group
      rw [hrw]
      exact mul_mem (mem_sup_right hxP) (mem_sup_left (inv_mem hy))
    have hh1 : h = 1 := by
      have hmem : h ∈ R ⊓ (Q ⊔ P) := ⟨hHR hh, hhQP⟩
      rw [hRdisj] at hmem
      exact hmem
    have hyQP : y ∈ Q ⊓ P := ⟨hy, by simpa [hh1] using hxP⟩
    rw [hQPdisj, Subgroup.mem_bot] at hyQP
    simp [hh1, hyQP]
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hPcard
    exact hp.one_lt.ne hPcard
  have hnil : Group.IsNilpotent ↥(H ⊔ Q) := by
    refine isNilpotent_of_isSolvable_of_le_normalizer hAE hPne
      (fun x hx => normalizer_inf_normalizer_le_normalizer_sup H Q ⟨hPH hx, hPQ hx⟩) ?_
    intro e he hne
    rw [centralizer_singleton_eq_of_natCard_eq_prime hp hPcard he hne]
    exact hfix
  apply hHQ
  rw [commutator_eq_bot_iff_le_centralizer]
  intro h hh
  rw [mem_centralizer_iff]
  intro y hy
  have hcop : (Nat.card ↥(H.subgroupOf (H ⊔ Q))).Coprime (Nat.card ↥(Q.subgroupOf (H ⊔ Q))) := by
    refine IsPGroup.coprime_card_of_ne r q hqr.symm _ _ ?_ ?_
    · exact (hR.to_le hHR).of_surjective
        (subgroupOfEquivOfLe (le_sup_left (a := H) (b := Q))).symm.toMonoidHom
        (subgroupOfEquivOfLe _).symm.surjective
    · exact hQ.of_surjective (subgroupOfEquivOfLe (le_sup_right (a := H) (b := Q))).symm.toMonoidHom
        (subgroupOfEquivOfLe _).symm.surjective
  have hle := le_centralizer_of_coprime_natCard (X := ↥(H ⊔ Q)) hcop
    (mem_subgroupOf.2 (show ((⟨h, mem_sup_left hh⟩ : ↥(H ⊔ Q)) : J) ∈ H from hh))
  exact congrArg Subtype.val
    (mem_centralizer_iff.1 hle (⟨y, mem_sup_right hy⟩ : ↥(H ⊔ Q)) (mem_subgroupOf.2 hy))

structure IsCriticalFixedLineSetup (p q r : ℕ) (R Q P H : Subgroup J) : Prop where
  prime_p : p.Prime
  prime_q : q.Prime
  prime_r : r.Prime
  odd_p : Odd p
  odd_q : Odd q
  odd_r : Odd r
  p_ne_q : p ≠ q
  p_ne_r : p ≠ r
  q_ne_r : q ≠ r
  normal_R : R.Normal
  coe_mul_coe : (R : Set J) * ((Q ⊔ P : Subgroup J) : Set J) = Set.univ
  disjoint_R : R ⊓ (Q ⊔ P) = ⊥
  normal_Q : (Q.subgroupOf (Q ⊔ P)).Normal
  disjoint_Q : Q ⊓ P = ⊥
  isPGroup_R : IsPGroup r ↥R
  isPGroup_Q : IsPGroup q ↥Q
  ne_bot_Q : Q ≠ ⊥
  natCard_P : Nat.card ↥P = p
  inf_centralizer_Q : Q ⊓ centralizer (P : Set J) = ⊥
  commutator_R_Q : ⁅R, Q⁆ ≠ ⊥
  rank_centralizer_P : elementaryAbelianPRank r ↥(R ⊓ centralizer (P : Set J)) ≤ 1
  rank_centralizer_Q : elementaryAbelianPRank r ↥(R ⊓ centralizer (Q : Set J)) ≤ 1
  ne_bot_H : H ≠ ⊥
  le_H : H ≤ R
  characteristic_H : (H.subgroupOf R).Characteristic
  pow_eq_one_H : ∀ x ∈ H, x ^ r = 1
  isPGroup_fixingSubgroup :
    IsPGroup r ↥(fixingSubgroup (MulAut ↥R) ((H.subgroupOf R : Subgroup ↥R) : Set ↥R))

namespace IsCriticalFixedLineSetup

variable (h : IsCriticalFixedLineSetup p q r R Q P H)

include h

theorem normal_H : H.Normal :=
  have := h.normal_R
  have := h.characteristic_H
  normal_of_characteristic_subgroupOf_of_normal h.le_H

theorem le_normalizer_H (K : Subgroup J) : K ≤ normalizer (H : Set J) :=
  have := h.normal_H
  le_normalizer_of_normal

theorem commutator_H_Q [Finite J] : ⁅H, Q⁆ ≠ ⊥ :=
  have := h.normal_R
  commutator_ne_bot_of_isPGroup_fixingSubgroup h.prime_q h.prime_r h.q_ne_r h.isPGroup_Q
    h.isPGroup_fixingSubgroup h.commutator_R_Q

theorem not_le_centralizer [Finite J] : ¬ Q ≤ centralizer (H : Set J) := fun hle =>
  h.commutator_H_Q (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.2 hle)

theorem isCyclic_inf_centralizer [Finite J] : IsCyclic ↥(R ⊓ centralizer (P : Set J)) :=
  isCyclic_of_elementaryAbelianPRank_le_one h.prime_r h.odd_r
    (h.isPGroup_R.to_le inf_le_left) h.rank_centralizer_P

theorem inf_centralizer_H_ne_bot [Finite J] [Group.IsSolvable J] :
    H ⊓ centralizer (P : Set J) ≠ ⊥ :=
  have := h.normal_R
  have := h.normal_H
  inf_centralizer_ne_bot_of_commutator_ne_bot h.prime_p h.prime_q h.prime_r h.q_ne_r
    h.isPGroup_R h.isPGroup_Q h.natCard_P h.normal_Q h.disjoint_Q h.disjoint_R
    h.inf_centralizer_Q h.le_H h.commutator_H_Q

theorem natCard_inf_centralizer [Finite J] [Group.IsSolvable J] :
    Nat.card ↥(H ⊓ centralizer (P : Set J)) = r := by
  have hle : H ⊓ centralizer (P : Set J) ≤ R ⊓ centralizer (P : Set J) := inf_le_inf_right _ h.le_H
  have := h.isCyclic_inf_centralizer
  have : IsCyclic ↥(H ⊓ centralizer (P : Set J)) :=
    isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact natCard_eq_of_isCyclic_of_forall_pow_eq_one h.prime_r
    ((Subgroup.nontrivial_iff_ne_bot _).2 h.inf_centralizer_H_ne_bot)
    fun x => Subtype.ext (by simpa using h.pow_eq_one_H (x : J) x.2.1)

end IsCriticalFixedLineSetup

theorem critical_fixed_line_for_regular_complement [Finite J] [Group.IsSolvable J]
    (h : IsCriticalFixedLineSetup p q r R Q P H) :
    ⁅H, Q⁆ ≠ ⊥ ∧ IsCyclic ↥(R ⊓ centralizer (P : Set J)) ∧
      Nat.card ↥(H ⊓ centralizer (P : Set J)) = r :=
  ⟨h.commutator_H_Q, h.isCyclic_inf_centralizer, h.natCard_inf_centralizer⟩

end CFSG.FeitThompson
