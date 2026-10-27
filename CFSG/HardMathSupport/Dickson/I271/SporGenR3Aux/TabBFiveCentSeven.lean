module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
public import Certificates.Certificate17599

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.Pinned
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

section Abstract

theorem not_dvd_pow_of_cover {Y R : Type*} [Group Y] [Finite Y] [Group R] {Z Y' : Subgroup Y}
    [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y') (hZ2 : Nat.card Z = 2)
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R) {p q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hR : ∀ s : R, orderOf s = p → ¬ q ^ n ∣ Nat.card (centralizer ({s} : Set R)))
    {y : Y} (hy : orderOf y = p) : ¬ q ^ n ∣ Nat.card (centralizer ({y} : Set Y)) := by
  intro hqn
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({y} : Set Y)) q hqn
  set T : Subgroup Y := K.map (centralizer ({y} : Set Y)).subtype with hTdef
  have hT : Nat.card T = q ^ n := by
    rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
  have hTC : T ≤ centralizer ({y} : Set Y) := Subgroup.map_subtype_le K
  have hodd : ∀ t ∈ T, Odd (orderOf t) := fun t ht =>
    Odd.of_dvd_nat ((hq.odd_of_ne_two hq2).pow) (hT ▸ Subgroup.orderOf_dvd_natCard T ht)
  have hyY' : y ∈ Y' := mem_of_index_two_of_odd hY' (by rw [hy]; exact hp.odd_of_ne_two hp2)
  let f : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', f g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hcop : Nat.Coprime 2 (q ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hord : ∀ g : Y, g ∈ Z → g ∈ T → g = 1 := by
    intro g hgZ hgT
    have h2 : orderOf g ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard Z hgZ
    have hqn' : orderOf g ∣ q ^ n := hT ▸ Subgroup.orderOf_dvd_natCard T hgT
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2 hqn')
  set s := f ⟨y, hyY'⟩ with hsdef
  have hs : orderOf s = p := by
    have hd : orderOf s ∣ p := by
      have := orderOf_map_dvd f ⟨y, hyY'⟩
      rwa [Subgroup.orderOf_mk, hy] at this
    rcases (Nat.dvd_prime hp).1 hd with h1 | h
    · exfalso
      have hyZ : y ∈ Z := (hker _).1 (orderOf_eq_one_iff.1 h1)
      have := Subgroup.orderOf_dvd_natCard Z hyZ
      rw [hy, hZ2] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact h
  set T' : Subgroup R := (T.subgroupOf Y').map f with hT'def
  have hT'C : T' ≤ centralizer ({s} : Set R) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : Y) ∈ T := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht)
    have htc : (t : Y) * y = y * t :=
      (mem_centralizer_singleton_iff (G := Y)).1 (hTC ht')
    refine (mem_centralizer_singleton_iff (G := R)).2 ?_
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htc
  have hinj : Set.InjOn f (T.subgroupOf Y' : Set Y') := by
    intro a ha b hb hab
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hT1 : ((a * b⁻¹ : Y') : Y) ∈ T :=
      Subgroup.mem_subgroupOf.1 (mul_mem (SetLike.mem_coe.1 ha) (inv_mem (SetLike.mem_coe.1 hb)))
    exact mul_inv_eq_one.1 (Subtype.ext (hord _ ((hker _).1 h1) hT1))
  have hT'card : Nat.card T' = q ^ n := by
    have e1 : Nat.card T' = Nat.card (f '' (T.subgroupOf Y' : Set Y')) := by
      rw [hT'def, ← Subgroup.coe_map]
      rfl
    rw [e1, Nat.card_image_of_injOn hinj, ← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun t ht => mem_of_index_two_of_odd hY' (hodd t ht))).toEquiv
  apply hR s hs
  rw [← hT'card]
  exact Subgroup.card_dvd_of_le hT'C

theorem card_centralizer_eq_of_mulEquiv {G K : Type*} [Group G] [Group K] {C : Subgroup G}
    (ψ : C ≃* K) {x : G} (hxC : x ∈ C) (hle : centralizer ({x} : Set G) ≤ C) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({ψ ⟨x, hxC⟩} : Set K)) := by
  rw [natCard_centralizer_mulEquiv ψ, card_centralizer_subtype]
  exact congrArg (fun H : Subgroup G => Nat.card ↥H) (inf_eq_right.2 hle).symm

end Abstract

section StdGroup


theorem card_centralizer_seven_stdGroup : ∀ s : Rgrp, orderOf s = 7 →
    Nat.card (centralizer ({s} : Set Rgrp)) = 141120 ∨
      Nat.card (centralizer ({s} : Set Rgrp)) = 1176 := by
  have hp3 : ¬ 7 ^ 3 ∣ Nat.card Rgrp := by
    rw [CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite Rgrp := rgrp_finite
  obtain ⟨x₀, y₀, hx₀, hy₀, hc, hind, h0, hi⟩ := sylow_seven_fusion
  refine forall_of_sylow_elementary hp3 hx₀ hy₀ hc hind ({rep7A, rep7B} : Set Rgrp) ?_ ?_
    (fun s => Nat.card (centralizer ({s} : Set Rgrp)) = 141120 ∨
      Nat.card (centralizer ({s} : Set Rgrp)) = 1176) ?_ ?_ ?_
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
    rwa [← BSevenLocal.centralizer_eq_of_zpowers_eq hab]
  · rintro r (rfl | rfl)
    · exact Or.inl card_centralizer_rep7A
    · exact Or.inr card_centralizer_rep7B

theorem not_dvd_25_stdGroup :
    ∀ s : Rgrp, orderOf s = 7 → ¬ 5 ^ 2 ∣ Nat.card (centralizer ({s} : Set Rgrp)) := by
  intro s hs
  rcases card_centralizer_seven_stdGroup s hs with h | h <;> rw [h] <;> norm_num

end StdGroup

section Baby


theorem not_dvd_pow_card_centralizer_of_le
    (hT3 : BabyTableIII) {α x : NativeSporadic.B}
    (hα : BabyInv 0 α) (hx : orderOf x = 7)
    (hle : centralizer ({x} : Set NativeSporadic.B) ≤ centralizer ({α} : Set NativeSporadic.B))
    {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hR : ∀ s : Rgrp, orderOf s = 7 → ¬ q ^ n ∣ Nat.card (centralizer ({s} : Set Rgrp))) :
    ¬ q ^ n ∣ Nat.card (centralizer ({x} : Set NativeSporadic.B)) := by
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
  have hy : orderOf (ψ ⟨x, hxα⟩) = 7 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  rw [@card_centralizer_eq_of_mulEquiv NativeSporadic.B _ Units.instGroup _ _ ψ x hxα hle]
  exact not_dvd_pow_of_cover hidx hZY hZ2 φ (by norm_num) (by norm_num) hq hq2 hR hy

theorem rank_ySeven
    : Matrix.rank (CFSG.Monster.B.bMat ySeven - 1) = 3480 := by
  rw [bMat_ySeven]
  exact Certificates.certificate17599.2

theorem factorization_five_card_centralizer_xSeven
    :
    (Nat.card (centralizer ({xSeven} : Set NativeSporadic.B))).factorization 5 = 1 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have P := bSevenElem_parts
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  have hyS : orderOf ySeven = 5 := orderOf_eq_prime P.y_pow P.y_ne
  have hyC : ySeven ∈ centralizer ({xSeven} : Set NativeSporadic.B) :=
    (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 P.x_y.symm
  have h5 : 5 ^ 1 ∣ Nat.card (centralizer ({xSeven} : Set NativeSporadic.B)) := by
    rw [pow_one, ← hyS]
    exact Subgroup.orderOf_dvd_natCard _ hyC
  have h25 := not_dvd_pow_card_centralizer_of_le CFSG.Monster.Existence.babyTableIII hα hxS
    centralizer_xSeven_le Nat.prime_five (by norm_num) not_dvd_25_stdGroup
  exact factorization_eq_of_dvd Nat.prime_five Nat.card_pos.ne' h5 h25

theorem not_seven_dvd_card_centralizer_zFive
    :
    ¬ 7 ∣ Nat.card (centralizer ({zFive} : Set NativeSporadic.B)) := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have P := bSevenElem_parts
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  have hyS : orderOf ySeven = 5 := orderOf_eq_prime P.y_pow P.y_ne
  have hz5 : orderOf zFive = 5 := orderOf_zFive
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer ({zFive} : Set NativeSporadic.B))) 7 hdvd
  have hw' : orderOf (w : NativeSporadic.B) = 7 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwz : (w : NativeSporadic.B) * zFive = zFive * w :=
    (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 w.2
  obtain ⟨c, hc⟩ := isConj_iff.1 (bSeven_isConj hw' hxS)
  set u := c * zFive * c⁻¹ with hu
  have huC : u ∈ centralizer ({xSeven} : Set NativeSporadic.B) := by
    refine (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
    rw [← hc, hu]
    calc c * zFive * c⁻¹ * (c * w * c⁻¹) = c * (zFive * w) * c⁻¹ := by group
      _ = c * (w * zFive) * c⁻¹ := by rw [hwz]
      _ = c * w * c⁻¹ * (c * zFive * c⁻¹) := by group
  have hu5 : u ^ 5 = 1 := by
    have h := pow_orderOf_eq_one zFive
    rw [hz5] at h
    rw [hu, conj_pow, h]
    group
  have hyC : ySeven ∈ centralizer ({xSeven} : Set NativeSporadic.B) :=
    (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 P.x_y.symm
  have hQle : zpowers ySeven ≤ centralizer ({xSeven} : Set NativeSporadic.B) :=
    zpowers_le.2 hyC
  have hQcard : Nat.card (zpowers ySeven) =
      5 ^ (Nat.card (centralizer ({xSeven} : Set NativeSporadic.B))).factorization 5 := by
    rw [Nat.card_zpowers, hyS, factorization_five_card_centralizer_xSeven, pow_one]
  obtain ⟨d, -, hdQ⟩ := @exists_conj_mem_of_card NativeSporadic.B Units.instGroup _ 5 _ _ _ hQle
    hQcard u huC hu5
  obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hdQ)
  have hm5 : ¬ 5 ∣ m := by
    intro h5m
    have h1 : ySeven ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 (hyS ▸ h5m)
    rw [hm, hu, show d * (c * zFive * c⁻¹) * d⁻¹ = (d * c) * zFive * (d * c)⁻¹ by group,
      conj_eq_one_iff] at h1
    rw [h1, orderOf_one] at hz5
    exact absurd hz5 (by norm_num)
  have hr := rank_bMat_conj (d * c) zFive
  rw [show (d * c) * zFive * (d * c)⁻¹ = d * u * d⁻¹ by rw [hu]; group, ← hm,
    rank_bMat_pow hyS hm5, rank_ySeven, bFiveAK_parts.2.2] at hr
  exact absurd hr (by norm_num)

end Baby

end CFSG.HardMathSupport.Dickson.I271.TabMFive
