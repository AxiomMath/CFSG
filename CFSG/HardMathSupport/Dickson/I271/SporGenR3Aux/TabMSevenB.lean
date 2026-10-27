module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley.C2E6Std
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

section Abstract

theorem card_centralizer_le_of_index_two {Y : Type*} [Group Y] [Finite Y] {Y' : Subgroup Y}
    (hY' : Y'.index = 2) {y : Y} (hy : y ∈ Y') :
    Nat.card (centralizer ({y} : Set Y)) ≤
      2 * Nat.card (centralizer ({(⟨y, hy⟩ : Y')} : Set Y')) := by
  haveI : Y'.Normal := Subgroup.normal_of_index_eq_two hY'
  set C := centralizer ({y} : Set Y) with hC
  have h1 : Nat.card (Y'.subgroupOf C) * (Y'.subgroupOf C).index = Nat.card C :=
    Subgroup.card_mul_index _
  have h2 : (Y'.subgroupOf C).index ≤ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal Y' C
    rw [hY'] at this
    exact Nat.le_of_dvd (by norm_num) this
  have h3 : Nat.card (Y'.subgroupOf C) =
      Nat.card (centralizer ({(⟨y, hy⟩ : Y')} : Set Y')) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩, ?_⟩
        invFun := fun g => ⟨⟨g.1.1, ?_⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      exact Subgroup.mem_centralizer_singleton_iff.1 g.1.2
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 g.2))
    · exact Subgroup.mem_subgroupOf.2 g.1.2
  calc Nat.card C = Nat.card (Y'.subgroupOf C) * (Y'.subgroupOf C).index := h1.symm
    _ ≤ Nat.card (Y'.subgroupOf C) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card (centralizer ({(⟨y, hy⟩ : Y')} : Set Y')) := by rw [h3, mul_comm]

theorem card_centralizer_le_of_cover {Y R : Type*} [Group Y] [Finite Y] [Group R]
    {Z Y' : Subgroup Y} [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (hZ2 : Nat.card Z = 2) (φ : Y' ⧸ Z.subgroupOf Y' ≃* R) {N : ℕ}
    (hR : ∀ s : R, orderOf s = 7 → Nat.card (centralizer ({s} : Set R)) ≤ N)
    {y : Y} (hy : orderOf y = 7) : Nat.card (centralizer ({y} : Set Y)) ≤ 4 * N := by
  have hyY' : y ∈ Y' := mem_of_index_two_of_odd hY' (by rw [hy]; decide)
  haveI : Finite R := Finite.of_equiv _ φ.toEquiv
  set y' : Y' := ⟨y, hyY'⟩ with hy'
  have hZcard : Nat.card (Z.subgroupOf Y') = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY').toEquiv, hZ2]
  have hs7 : orderOf (φ (QuotientGroup.mk y')) = 7 := by
    rw [MulEquiv.orderOf_eq]
    have hd : orderOf (QuotientGroup.mk y' : Y' ⧸ Z.subgroupOf Y') ∣ 7 := by
      have := orderOf_map_dvd (QuotientGroup.mk' (Z.subgroupOf Y')) y'
      rwa [Subgroup.orderOf_mk, hy] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hd with h1 | h
    · exfalso
      have hyZ : y' ∈ Z.subgroupOf Y' := (QuotientGroup.eq_one_iff y').1 (orderOf_eq_one_iff.1 h1)
      have := Subgroup.orderOf_dvd_natCard _ hyZ
      rw [Subgroup.orderOf_mk, hy, hZcard] at this
      norm_num at this
    · exact h
  have h1 := card_centralizer_le_of_index_two hY' hyY'
  have h2 := card_centralizer_le_mul (Z.subgroupOf Y') φ y'
  have h3 : Nat.card ((Z.subgroupOf Y') ⊓ centralizer ({y'} : Set Y') : Subgroup Y') ≤ 2 :=
    hZcard ▸ Subgroup.card_le_of_le inf_le_left
  have h4 := hR _ hs7
  calc Nat.card (centralizer ({y} : Set Y))
      ≤ 2 * Nat.card (centralizer ({y'} : Set Y')) := h1
    _ ≤ 2 * (2 * N) := Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul h3 h4))
    _ = 4 * N := by ring

end Abstract

section StdGroup


theorem card_centralizer_seven_le_Rgrp :
    ∀ s : Rgrp, orderOf s = 7 → Nat.card (centralizer ({s} : Set Rgrp)) ≤ 141120 := by
  have hp3 : ¬ 7 ^ 3 ∣ Nat.card Rgrp := by
    rw [CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite Rgrp := rgrp_finite
  obtain ⟨x₀, y₀, hx₀, hy₀, hc, hind, h0, hi⟩ := sylow_seven_fusion
  refine forall_of_sylow_elementary hp3 hx₀ hy₀ hc hind ({rep7A, rep7B} : Set Rgrp) ?_ ?_
    (fun s => Nat.card (centralizer ({s} : Set Rgrp)) ≤ 141120) ?_ ?_ ?_
  · rcases h0 with h | h
    · exact ⟨rep7A, by simp, h⟩
    · exact ⟨rep7B, by simp, h⟩
  · intro i hi'
    rcases hi i hi' with h | h
    · exact ⟨rep7A, by simp, h⟩
    · exact ⟨rep7B, by simp, h⟩
  · intro a b hab ha
    rwa [← CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj hab]
  · intro a b hab ha
    rwa [← centralizer_eq_of_zpowers_eq hab]
  · rintro r (rfl | rfl)
    · show Nat.card (centralizer ({rep7A} : Set Rgrp)) ≤ 141120
      rw [card_centralizer_rep7A]
    · show Nat.card (centralizer ({rep7B} : Set Rgrp)) ≤ 141120
      rw [card_centralizer_rep7B]
      norm_num

end StdGroup

section Baby


theorem card_centralizer_seven_le_B
    {x : NativeSporadic.B} (hx : orderOf x = 7) :
    Nat.card (centralizer ({x} : Set NativeSporadic.B)) ≤ 564480 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have P := bSevenElem_parts
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj (bSeven_isConj hx hxS)]
  have hle := centralizer_xSeven_le
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam CFSG.Monster.Existence.babyTableIII hα
  haveI : Finite ↥CFSG.Monster.B.TwoA.Amalgam.Eam := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  have hxα : xSeven ∈ centralizer ({alphaB} : Set NativeSporadic.B) :=
    hle ((mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 rfl)
  set y := ψ ⟨xSeven, hxα⟩ with hydef
  have hy : orderOf y = 7 := by
    rw [hydef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxS]
  have hcard : Nat.card (centralizer ({xSeven} : Set NativeSporadic.B)) =
      Nat.card (centralizer ({y} : Set ↥CFSG.Monster.B.TwoA.Amalgam.Eam)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨ψ ⟨g, hle g.2⟩, ?_⟩
        invFun := fun h => ⟨((ψ.symm h : ↥(centralizer ({alphaB} : Set NativeSporadic.B))) :
          NativeSporadic.B), ?_⟩
        left_inv := fun g => by simp
        right_inv := fun h => by simp }
    · have hg : (g : NativeSporadic.B) * xSeven = xSeven * g :=
        (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 g.2
      refine (mem_centralizer_singleton_iff (G := ↥CFSG.Monster.B.TwoA.Amalgam.Eam)).2 ?_
      rw [hydef, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (by simpa using hg))
    · have hh : h * y = y * h :=
        (mem_centralizer_singleton_iff (G := ↥CFSG.Monster.B.TwoA.Amalgam.Eam)).1 h.2
      refine (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
      have e : ψ.symm (h : ↥CFSG.Monster.B.TwoA.Amalgam.Eam) * ⟨xSeven, hxα⟩ =
          ⟨xSeven, hxα⟩ * ψ.symm (h : ↥CFSG.Monster.B.TwoA.Amalgam.Eam) := by
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hydef]
        exact hh
      have e' := congrArg Subtype.val e
      simpa only [Subgroup.coe_mul] using e'
  rw [hcard]
  have h := card_centralizer_le_of_cover hidx hZY hZ2 φ card_centralizer_seven_le_Rgrp hy
  omega

end Baby

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
