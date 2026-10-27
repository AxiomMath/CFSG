module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Fixing

variable {S : Type} [Group S]

theorem mem_innerAut_of_fixing {p : ℕ} {a : MulAut S} (ha : a ^ p = 1) {N : Subgroup S}
    (hfix : ∀ w : MulAut S, (∀ x ∈ N, w x = x) → w ∈ Subgroup.zpowers a) {w : MulAut S}
    (hw : Nat.Coprime p (orderOf w)) (hwN : ∀ x ∈ N, w x = x) : w ∈ innerAut S := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hfix w hwN)
  have h1 : w ^ p = 1 := by
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have h2 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hw.symm h2
  rw [orderOf_eq_one_iff.1 h3]
  exact (innerAut S).one_mem

theorem eq_one_of_commute_of_fixing [Finite S] {p : ℕ} (hp : p.Prime) {a : MulAut S}
    (ha : a ^ p = 1)
    (hout : a ∉ innerAut S) {J : Subgroup S}
    (hfix : ∀ w : MulAut S, (∀ x ∈ J, w x = x) → w ∈ Subgroup.zpowers a)
    (hZ : Subgroup.center S = ⊥) {x : S} (hx : ∀ m ∈ J, x * m = m * x) : x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : (MulAut.conj x : MulAut S) = 1 := by
    by_contra hne
    have hfixc : ∀ m ∈ J, (MulAut.conj x : MulAut S) m = m := fun m hm => by
      rw [MulAut.conj_apply, hx m hm]
      group
    have hmem : (MulAut.conj x : MulAut S) ∈ Subgroup.zpowers a := hfix _ hfixc
    have ha1 : a ≠ 1 := fun h => hout (h ▸ (innerAut S).one_mem)
    have hord : orderOf a = p := orderOf_eq_prime ha ha1
    have hle : Subgroup.zpowers (MulAut.conj x : MulAut S) ≤ Subgroup.zpowers a :=
      (Subgroup.zpowers_le).2 hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hxp : (MulAut.conj x : MulAut S) ^ p = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have hordx : orderOf (MulAut.conj x : MulAut S) = p := orderOf_eq_prime hxp hne
    have heq : Subgroup.zpowers (MulAut.conj x : MulAut S) = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordx]
    have hamem : a ∈ Subgroup.zpowers (MulAut.conj x : MulAut S) := by
      rw [heq]
      exact Subgroup.mem_zpowers a
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hamem
    apply hout
    rw [← hj, ← map_zpow]
    exact ⟨x ^ j, rfl⟩
  have hxc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun φ : MulAut S => φ y) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  rw [hZ] at hxc
  exact Subgroup.mem_bot.1 hxc

theorem normal_subgroupOf_self (H : Subgroup S) : (H.subgroupOf H).Normal := by
  rw [Subgroup.subgroupOf_self]
  infer_instance

theorem isSolvable_quotient_self (H : Subgroup S) [(H.subgroupOf H).Normal] :
    Group.IsSolvable (↥H ⧸ H.subgroupOf H) := by
  haveI : Subsingleton (↥H ⧸ H.subgroupOf H) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (H.mul_mem (H.inv_mem a.2) b.2))
  exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _

theorem congr_mem_innerAut_iff {T : Type} [Group T] (e : S ≃* T) (β : MulAut S) :
    MulAut.congr e β ∈ innerAut T ↔ β ∈ innerAut S := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨e.symm t, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  · rintro ⟨s, rfl⟩
    exact ⟨e s, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e s).symm⟩

end Fixing

section FieldType

variable {p : ℕ} {S : Type} [Group S] [Finite S]

theorem OuterCentData.of_fieldType (hp : p.Prime) {a : MulAut S} (ha : a ^ p = 1)
    (hout : a ∉ innerAut S) (hZ : Subgroup.center S = ⊥) {J : Subgroup S}
    (hJC : J ≤ fixSubgroup a) (hJn : (J.subgroupOf (fixSubgroup a)).Normal)
    (hsol : Group.IsSolvable (↥(fixSubgroup a) ⧸ J.subgroupOf (fixSubgroup a)))
    (hsimple : IsSimpleGroup ↥J) (hnab : ∃ x y : ↥J, x * y ≠ y * x) (hchev : IsChevSimple p ↥J)
    (hdvd : p ∣ Nat.card ↥J) (hL27 : ¬ IsLTwoTwentySeven ↥J)
    (hfix : ∀ w : MulAut S, (∀ x ∈ J, w x = x) → w ∈ Subgroup.zpowers a) :
    OuterCentData p a := by
  refine OuterCentData.ofSimpleNormal hp
    ⟨hJC, hJn, hsimple, hnab, hsol, fun x _ hx => eq_one_of_commute_of_fixing hp ha hout hfix hZ hx,
      hchev, hdvd⟩ ?_ fun _ h => absurd h hL27
  intro _ w hw _ hwfix
  exact mem_innerAut_of_fixing ha hfix hw fun x hx => hwfix x (hJC hx)

theorem OuterCentData.of_fieldType_of_fix_eq (hp : p.Prime) {a : MulAut S} (ha : a ^ p = 1)
    (hout : a ∉ innerAut S) (hZ : Subgroup.center S = ⊥) {N J : Subgroup S}
    (hN : fixSubgroup a = N) (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal)
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    (hsimple : IsSimpleGroup ↥J) (hnab : ∃ x y : ↥J, x * y ≠ y * x) (hchev : IsChevSimple p ↥J)
    (hdvd : p ∣ Nat.card ↥J) (hL27 : ¬ IsLTwoTwentySeven ↥J)
    (hfix : ∀ w : MulAut S, (∀ x ∈ J, w x = x) → w ∈ Subgroup.zpowers a) :
    OuterCentData p a := by
  subst hN
  exact OuterCentData.of_fieldType hp ha hout hZ hJN hJn hsol hsimple hnab hchev hdvd hL27 hfix

end FieldType

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
