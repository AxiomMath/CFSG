module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSeven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.Monster.Existence.StdOdd
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

section Abstract

theorem card_centralizer_dvd_four_mul_of_cover {Y R : Type*} [Group Y] [Group R]
    {Z Y' : Subgroup Y} [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (hZ2 : Nat.card Z = 2) (φ : Y' ⧸ Z.subgroupOf Y' ≃* R) {N : ℕ}
    (hR : ∀ s : R, orderOf s = 7 → Nat.card (centralizer ({s} : Set R)) ∣ N)
    {y : Y} (hy : orderOf y = 7) : Nat.card (centralizer ({y} : Set Y)) ∣ 4 * N := by
  haveI : Y'.Normal := Subgroup.normal_of_index_eq_two hY'
  have hyY' : y ∈ Y' := mem_of_index_two_of_odd hY' (by rw [hy]; decide)
  let q : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', q g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hs7 : orderOf (q ⟨y, hyY'⟩) = 7 := by
    have hd : orderOf (q ⟨y, hyY'⟩) ∣ 7 := by
      have := orderOf_map_dvd q ⟨y, hyY'⟩
      rwa [Subgroup.orderOf_mk, hy] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hd with h1 | h
    · exfalso
      have hyZ : y ∈ Z := (hker _).1 (orderOf_eq_one_iff.1 h1)
      have := Subgroup.orderOf_dvd_natCard Z hyZ
      rw [hy, hZ2] at this
      norm_num at this
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
  have h7 := (Subgroup.card_dvd_of_le h5).trans (hR _ hs7)
  rw [← h1, h3, ← h4]
  have := Nat.mul_dvd_mul h2 (Nat.mul_dvd_mul h7 h6)
  rwa [show 2 * (N * 2) = 4 * N by ring] at this

end Abstract

section Baby



theorem card_centralizer_seven_B_dvd
    (x : NativeSporadic.B) (hx : orderOf x = 7) :
    Nat.card (centralizer ({x} : Set NativeSporadic.B)) ∣ 564480 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have P := bSevenElem_parts
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bSeven_isConj hx hxS)]
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam CFSG.Monster.Existence.babyTableIII hα
  haveI : Finite ↥CFSG.Monster.B.TwoA.Amalgam.Eam := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  have hxα : xSeven ∈ centralizer ({alphaB} : Set NativeSporadic.B) :=
    centralizer_xSeven_le ((mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 rfl)
  have hy : orderOf (ψ ⟨xSeven, hxα⟩) = 7 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxS]
  have hR : ∀ s : Rgrp, orderOf s = 7 → Nat.card (centralizer ({s} : Set Rgrp)) ∣ 141120 := by
    intro s hs
    rcases CFSG.HardMathSupport.Dickson.I271.TabMFive.card_centralizer_seven_stdGroup s hs
      with h | h <;> rw [h] <;> norm_num
  rw [@CFSG.HardMathSupport.Dickson.I271.TabMFive.card_centralizer_eq_of_mulEquiv
    NativeSporadic.B _ Units.instGroup _ _ ψ xSeven hxα centralizer_xSeven_le]
  exact (card_centralizer_dvd_four_mul_of_cover hidx hZY hZ2 φ hR hy).trans (by norm_num)

theorem census_B_seven
    : ∀ x : CFSG.Blueprint.NativeSporadic.Carrier .B, orderOf x = 7 →
    ∀ J : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .B),
      CFSG.Open.GLAPComponent 7
        (Subgroup.centralizer ({x} : Set (CFSG.Blueprint.NativeSporadic.Carrier .B))) J →
      Nat.card (CFSG.Yardstones.Md0ec50421ce4.PSimple 7 J) ∣ 80640 := by
  intro x hx J hJ
  haveI : Finite (NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  have hc : Nat.card (Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .B))) ∣ 564480 :=
    card_centralizer_seven_B_dvd x hx
  have hd := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.prime_mul_card_pSimple_dvd_cent
    (by norm_num) hx hJ.1
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (hc.trans (by norm_num)))

end Baby

end CFSG.HardMathSupport.Dickson.BMRows
