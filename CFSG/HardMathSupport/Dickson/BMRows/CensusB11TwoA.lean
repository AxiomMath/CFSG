module

public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.StdOdd.Cert.Cent11
public import CFSG.Monster.GMS.BabyTwoAAutBridge

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.LieType.Chevalley.C2E6Std

section Abstract

theorem natCard_inf_centralizer_eq_of_mulEquiv {G X : Type*} [Group G] [Group X]
    {M : Subgroup G} (e : M ≃* X) {w : G} (hw : w ∈ M) :
    Nat.card (M ⊓ centralizer ({w} : Set G) : Subgroup G) =
      Nat.card (centralizer ({e ⟨w, hw⟩} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e ⟨x, (mem_inf.1 x.2).1⟩, ?_⟩
      invFun := fun y => ⟨(e.symm y : G), mem_inf.2 ⟨(e.symm y).2, ?_⟩⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2)
  · have h := congrArg (fun z => ((e.symm z : M) : G)) (mem_centralizer_singleton_iff.1 y.2)
    simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] at h
    exact mem_centralizer_singleton_iff.2 h

theorem card_centralizer_dvd_four_mul_of_cover_prime {Y R : Type*} [Group Y] [Group R]
    {Z Y' : Subgroup Y} [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (hZ2 : Nat.card Z = 2) (φ : Y' ⧸ Z.subgroupOf Y' ≃* R) {p N : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hR : ∀ s : R, orderOf s = p → Nat.card (centralizer ({s} : Set R)) ∣ N)
    {y : Y} (hy : orderOf y = p) : Nat.card (centralizer ({y} : Set Y)) ∣ 4 * N := by
  haveI : Y'.Normal := Subgroup.normal_of_index_eq_two hY'
  have hyY' : y ∈ Y' := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have h : (y ^ (m + 1)) ^ 2 = y := by
      rw [← pow_mul, show (m + 1) * 2 = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    exact h ▸ Subgroup.sq_mem_of_index_two hY' _
  let q : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', q g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hsp : orderOf (q ⟨y, hyY'⟩) = p := by
    have hd : orderOf (q ⟨y, hyY'⟩) ∣ p := by
      have := orderOf_map_dvd q ⟨y, hyY'⟩
      rwa [Subgroup.orderOf_mk, hy] at this
    rcases (Nat.dvd_prime hp).1 hd with h1 | h
    · exfalso
      have hyZ : y ∈ Z := (hker _).1 (orderOf_eq_one_iff.1 h1)
      have := Subgroup.orderOf_dvd_natCard Z hyZ
      rw [hy, hZ2] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact h
  have h1 := Subgroup.relIndex_mul_card Y' (centralizer ({y} : Set Y))
  have h2 := Subgroup.relIndex_dvd_index_of_normal Y' (centralizer ({y} : Set Y))
  rw [hY'] at h2
  have h3 : Nat.card (Y' ⊓ centralizer ({y} : Set Y) : Subgroup Y) =
      Nat.card ((centralizer ({y} : Set Y)).subgroupOf Y') := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h4 := Subgroup.relIndex_mul_card q.ker ((centralizer ({y} : Set Y)).subgroupOf Y')
  rw [Subgroup.relIndex_ker] at h4
  have h5 : ((centralizer ({y} : Set Y)).subgroupOf Y').map q ≤
      centralizer ({q ⟨y, hyY'⟩} : Set R) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : Y) ∈ centralizer ({y} : Set Y) :=
      Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht)
    have htc : (t : Y) * y = y * t := (mem_centralizer_singleton_iff (G := Y)).1 ht'
    refine (mem_centralizer_singleton_iff (G := R)).2 ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htc
  have h6 : Nat.card (q.ker ⊓ (centralizer ({y} : Set Y)).subgroupOf Y' : Subgroup Y') ∣ 2 := by
    have hle : q.ker ⊓ (centralizer ({y} : Set Y)).subgroupOf Y' ≤ Z.subgroupOf Y' :=
      fun g hg => Subgroup.mem_subgroupOf.2
        ((hker g).1 (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1))
    have hZ' : Nat.card (Z.subgroupOf Y') = 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY').toEquiv).trans hZ2
    have := Subgroup.card_dvd_of_le hle
    rwa [hZ'] at this
  have h7 := (Subgroup.card_dvd_of_le h5).trans (hR _ hsp)
  rw [← h1, h3, ← h4]
  have := Nat.mul_dvd_mul h2 (Nat.mul_dvd_mul h7 h6)
  rwa [show 2 * (N * 2) = 4 * N by ring] at this

end Abstract

section Baby


theorem card_centralizer_inf_dvd_of_babyInv_zero {u y : NativeSporadic.B} (hu : BabyInv 0 u)
    (hy : orderOf y = 11) (huy : Commute u y) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set NativeSporadic.B) ⊓
      Subgroup.centralizer ({y} : Set NativeSporadic.B)) ∣ 264 := by
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam CFSG.Monster.Existence.babyTableIII hu
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  have hyu : y ∈ centralizer ({u} : Set NativeSporadic.B) :=
    (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 huy.symm.eq
  have hy' : orderOf (ψ ⟨y, hyu⟩) = 11 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  have hR : ∀ s : ↥stdGroup, orderOf s = 11 →
      Nat.card (centralizer ({s} : Set ↥stdGroup)) ∣ 66 := by
    intro s hs
    haveI : Finite ↥stdGroup := CFSG.Monster.Existence.StdOdd.Cert.rgrp_finite
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have hp2 : ¬ 11 ^ 2 ∣ Nat.card ↥stdGroup := by
      rw [card_stdGroup]
      norm_num
    rw [CFSG.Monster.Existence.StdOdd.Cert.card_centralizer_eq_of_sylow_prime hp2
      CFSG.Monster.Existence.StdOdd.Cert.orderOf_rep11 hs,
      CFSG.Monster.Existence.StdOdd.Cert.card_centralizer_rep11]
  rw [natCard_inf_centralizer_eq_of_mulEquiv ψ hyu]
  exact (card_centralizer_dvd_four_mul_of_cover_prime hidx hZY hZ2 φ (by norm_num)
    (by norm_num) hR hy').trans (by norm_num)

end Baby

end CFSG.HardMathSupport.Dickson.BMRows
