module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenSylowPred
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7A
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57
public import CFSG.Monster.GMS.BabyTwoAAutBridge
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Monster.GMS.BabyReduce
public import CFSG.Monster.GMS.Facts.Section4

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley.C2E6Std

section Abstract

theorem mem_of_index_two_of_odd {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2)
    {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨m, hm⟩ := hg
  have h : (g ^ (m + 1)) ^ 2 = g := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact h ▸ Subgroup.sq_mem_of_index_two hH _

theorem centralizer_eq_of_zpowers_eq {G : Type*} [Group G] {a b : G}
    (h : zpowers a = zpowers b) :
    centralizer ({a} : Set G) = centralizer ({b} : Set G) := by
  rw [← centralizer_closure ({a} : Set G), ← centralizer_closure ({b} : Set G),
    ← zpowers_eq_closure, ← zpowers_eq_closure, h]

theorem not_dvd_27_of_cover {Y R : Type*} [Group Y] [Finite Y] [Group R] {Z Y' : Subgroup Y}
    [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y') (hZ2 : Nat.card Z = 2)
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = 7 → ¬ 27 ∣ Nat.card (centralizer ({s} : Set R)))
    {y : Y} (hy : orderOf y = 7) : ¬ 27 ∣ Nat.card (centralizer ({y} : Set Y)) := by
  intro h27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({y} : Set Y)) 3
    (n := 3) (by norm_num; exact h27)
  set T : Subgroup Y := K.map (centralizer ({y} : Set Y)).subtype with hTdef
  have hT : Nat.card T = 27 := by
    rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num
  have hTC : T ≤ centralizer ({y} : Set Y) := Subgroup.map_subtype_le K
  have hodd : ∀ t ∈ T, Odd (orderOf t) := fun t ht =>
    Odd.of_dvd_nat (by decide) (hT ▸ Subgroup.orderOf_dvd_natCard T ht)
  have hyY' : y ∈ Y' := mem_of_index_two_of_odd hY' (by rw [hy]; decide)
  let q : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', q g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hord : ∀ g : Y, g ∈ Z → g ∈ T → g = 1 := by
    intro g hgZ hgT
    have h2 : orderOf g ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard Z hgZ
    have h27' : orderOf g ∣ 27 := hT ▸ Subgroup.orderOf_dvd_natCard T hgT
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h27')
  set s := q ⟨y, hyY'⟩ with hsdef
  have hs7 : orderOf s = 7 := by
    have hd : orderOf s ∣ 7 := by
      have := orderOf_map_dvd q ⟨y, hyY'⟩
      rwa [Subgroup.orderOf_mk, hy] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hd with h1 | h
    · exfalso
      have hyZ : y ∈ Z := (hker _).1 (orderOf_eq_one_iff.1 h1)
      have := Subgroup.orderOf_dvd_natCard Z hyZ
      rw [hy, hZ2] at this
      norm_num at this
    · exact h
  set T' : Subgroup R := (T.subgroupOf Y').map q with hT'def
  have hT'C : T' ≤ centralizer ({s} : Set R) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : Y) ∈ T := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht)
    have htc : (t : Y) * y = y * t :=
      (mem_centralizer_singleton_iff (G := Y)).1 (hTC ht')
    refine (mem_centralizer_singleton_iff (G := R)).2 ?_
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htc
  have hinj : Set.InjOn q (T.subgroupOf Y' : Set Y') := by
    intro a ha b hb hab
    have h1 : q (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hZ' := (hker _).1 h1
    have hT1 : ((a * b⁻¹ : Y') : Y) ∈ T :=
      Subgroup.mem_subgroupOf.1 (mul_mem (SetLike.mem_coe.1 ha) (inv_mem (SetLike.mem_coe.1 hb)))
    have := hord _ hZ' hT1
    have h2 : a * b⁻¹ = 1 := Subtype.ext this
    exact mul_inv_eq_one.1 h2
  have hT'card : Nat.card T' = 27 := by
    have e1 : Nat.card T' = Nat.card (q '' (T.subgroupOf Y' : Set Y')) := by
      rw [hT'def, ← Subgroup.coe_map]
      rfl
    rw [e1, Nat.card_image_of_injOn hinj, ← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun t ht => mem_of_index_two_of_odd hY' (hodd t ht))).toEquiv
  apply hR s hs7
  rw [← hT'card]
  exact Subgroup.card_dvd_of_le hT'C

end Abstract

section StdGroup


theorem not_dvd_27_stdGroup :
    ∀ s : Rgrp, orderOf s = 7 → ¬ 27 ∣ Nat.card (centralizer ({s} : Set Rgrp)) := by
  have hp3 : ¬ 7 ^ 3 ∣ Nat.card Rgrp := by
    rw [CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite Rgrp := rgrp_finite
  obtain ⟨x₀, y₀, hx₀, hy₀, hc, hind, h0, hi⟩ := sylow_seven_fusion
  refine CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.forall_of_sylow_elementary hp3
    hx₀ hy₀ hc hind ({rep7A, rep7B} : Set Rgrp) ?_ ?_
    (fun s => ¬ 27 ∣ Nat.card (centralizer ({s} : Set Rgrp))) ?_ ?_ ?_
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
    · show ¬ 27 ∣ Nat.card (centralizer ({rep7A} : Set Rgrp))
      rw [card_centralizer_rep7A]
      norm_num
    · show ¬ 27 ∣ Nat.card (centralizer ({rep7B} : Set Rgrp))
      rw [card_centralizer_rep7B]
      norm_num

end StdGroup

section Baby


theorem not_dvd_27_card_centralizer (hT3 : BabyTableIII) {α x : NativeSporadic.B}
    (hα : BabyInv 0 α) (hx : orderOf x = 7)
    (hle : centralizer ({x} : Set NativeSporadic.B) ≤ centralizer ({α} : Set NativeSporadic.B)) :
    ¬ 27 ∣ Nat.card (centralizer ({x} : Set NativeSporadic.B)) := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨ψ⟩ := nonempty_centralizer_mulEquiv_Eam hT3 hα
  haveI : Finite ↥CFSG.Monster.B.TwoA.Amalgam.Eam := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  have hxα : x ∈ centralizer ({α} : Set NativeSporadic.B) :=
    hle ((mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 rfl)
  set y := ψ ⟨x, hxα⟩ with hydef
  have hy : orderOf y = 7 := by
    rw [hydef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have hcard : Nat.card (centralizer ({x} : Set NativeSporadic.B)) =
      Nat.card (centralizer ({y} : Set ↥CFSG.Monster.B.TwoA.Amalgam.Eam)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨ψ ⟨g, hle g.2⟩, ?_⟩
        invFun := fun h => ⟨((ψ.symm h : ↥(centralizer ({α} : Set NativeSporadic.B))) :
          NativeSporadic.B), ?_⟩
        left_inv := fun g => by simp
        right_inv := fun h => by simp }
    · have hg : (g : NativeSporadic.B) * x = x * g :=
        (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 g.2
      refine (mem_centralizer_singleton_iff (G := ↥CFSG.Monster.B.TwoA.Amalgam.Eam)).2 ?_
      rw [hydef, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (by simpa using hg))
    · have hh : h * y = y * h :=
        (mem_centralizer_singleton_iff (G := ↥CFSG.Monster.B.TwoA.Amalgam.Eam)).1 h.2
      refine (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
      have e : ψ.symm (h : ↥CFSG.Monster.B.TwoA.Amalgam.Eam) * ⟨x, hxα⟩ =
          ⟨x, hxα⟩ * ψ.symm (h : ↥CFSG.Monster.B.TwoA.Amalgam.Eam) := by
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hydef]
        exact hh
      have e' := congrArg Subtype.val e
      simpa only [Subgroup.coe_mul] using e'
  rw [hcard]
  exact not_dvd_27_of_cover hidx hZY hZ2 φ not_dvd_27_stdGroup hy

end Baby

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
