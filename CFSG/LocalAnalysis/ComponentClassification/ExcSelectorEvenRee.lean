module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenOrders
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.RankThree.SteinbergR3ELargeReeOrder

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Simplicity CFSG.RankThree.LargeReeOrder
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem fixedSubgroup_finiteReeAut (m : ℕ) :
    fixedSubgroup (F4.finiteReeAut K m) = reeFixed F4 K m := by
  ext g
  change F4.finiteReeAut K m g = g ↔ F4.reeAut K m g = g
  have h : F4.finiteReeAut K m g = F4.reeAut K m g := by
    rw [reeAut_apply]
    exact DFunLike.congr_fun (finiteReeAut_toMonoidHom (t := F4) (K := K) m) g
  rw [h]

theorem odd_large_ree_factor {f : ℕ} (hf : 1 ≤ f) :
    Odd ((2 ^ f - 1) ^ 2 * (2 ^ f + 1) ^ 2 * ((2 ^ f) ^ 2 + 1) ^ 2 *
      ((2 ^ f) ^ 2 - 2 ^ f + 1) * ((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1)) := by
  set q := 2 ^ f with hq
  have hev : Even q := by rw [hq]; exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hq2 : 2 ≤ q := two_le_two_pow hf
  have o1 : Odd (q - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  have o2 : Odd (q + 1) := hev.add_one
  have o3 : Odd (q ^ 2 + 1) := (Nat.even_pow.2 ⟨hev, by norm_num⟩).add_one
  have esub : ∀ a b : ℕ, b ≤ a → Even a → Even b → Even (a - b) := fun a b hba ha hb =>
    (Nat.even_sub hba).2 (iff_of_true ha hb)
  have o4 : Odd (q ^ 2 - q + 1) := by
    have h1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    exact (esub _ _ h1 (Nat.even_pow.2 ⟨hev, by norm_num⟩) hev).add_one
  have o5 : Odd (q ^ 4 - q ^ 2 + 1) := by
    have h1 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact (esub _ _ h1 (Nat.even_pow.2 ⟨hev, by norm_num⟩)
      (Nat.even_pow.2 ⟨hev, by norm_num⟩)).add_one
  exact (((o1.pow.mul o2.pow).mul o3.pow).mul o4).mul o5

theorem large_ree_factor_le {f : ℕ} (hf : 1 ≤ f) :
    (2 ^ f - 1) ^ 2 * (2 ^ f + 1) ^ 2 * ((2 ^ f) ^ 2 + 1) ^ 2 *
      ((2 ^ f) ^ 2 - 2 ^ f + 1) * ((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1) ≤ (2 ^ f) ^ 18 := by
  set q := 2 ^ f with hq
  have hq2 : 2 ≤ q := two_le_two_pow hf
  have h1 : (q - 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (Nat.sub_le q 1) 2
  have h2 : (q + 1) ^ 2 ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left (by
    have := pow_add_one_le hq2 1
    simpa using this) 2
  have h3 : (q ^ 2 + 1) ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left (pow_add_one_le hq2 2) 2
  have h4 : q ^ 2 - q + 1 ≤ q ^ 2 := by
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have : 1 ≤ q := by omega
    omega
  have h5 : q ^ 4 - q ^ 2 + 1 ≤ q ^ 4 := by
    have : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  calc (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) ≤
        q ^ 2 * (q ^ 2) ^ 2 * (q ^ 3) ^ 2 * q ^ 2 * q ^ 4 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4) h5
    _ = q ^ 18 := by ring

theorem card_reeFixed_F4 {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card (reeFixed F4 K m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1) - 1) ^ 2 * (2 ^ (2 * m + 1) + 1) ^ 2 * ((2 ^ (2 * m + 1)) ^ 2 + 1) ^ 2 *
        ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) *
          ((2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1)) := by
  rw [Nat.card_congr (reeFixedEquivReeGamma K m).toEquiv,
    (large_Ree_exact_native_order_and_prime_factor_exhaustion m K hK).1]
  ring

theorem reeFixed_F4_simple_not_smallType {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    IsSimpleGroup (reeFixed F4 K m) ∧ ¬ SmallType (reeFixed F4 K m) := by
  have hK' : Nat.card K = F4.prime ^ (2 * m + 1) := hK
  have hZ : center (reeFixed F4 K m) = ⊥ := by
    have h := large_Ree_fixed_group_center_trivial m K hK
    rw [eq_bot_iff]
    intro z hz
    have hz' : reeFixedEquivReeGamma K m z ∈ center (F4.reeGamma K m) :=
      (MulEquivClass.apply_mem_center_iff (reeFixedEquivReeGamma K m)).2 hz
    rw [h, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 ((reeFixedEquivReeGamma K m).injective (hz'.trans (map_one _).symm))
  have hs := isSimpleGroup_quotient_center_reeFixed_F4 (K := K) m hm hK'
  have hsimple : IsSimpleGroup (reeFixed F4 K m) :=
    (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm).2 hs
  refine ⟨hsimple, not_smallType_of_pow_mul hZ (e := 2 * m + 1) (a := 12) (b := 18)
    (odd_large_ree_factor (by omega)) (large_ree_factor_le (by omega)) (card_reeFixed_F4 hK)
    (by omega) (by omega) (by omega) (by omega)⟩

section Tits

variable (hK2 : Nat.card K = 2)
include hK2

theorem isSimpleGroup_commutator_reeFixed_tits :
    IsSimpleGroup (commutator (reeFixed F4 K 0)) := by
  set T := titsData K hK2
  have hnt : Nontrivial (commutator (reeFixed F4 K 0)) :=
    ⟨⟨⟨T.g₀, T.g₀_mem⟩, 1, fun h => T.g₀_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  rcases T.eq_bot_or_eq_of_le hK2 (N.map (commutator (reeFixed F4 K 0)).subtype)
      (Subgroup.map_subtype_le N)
      (by
        rintro d hd _ ⟨n, hn, rfl⟩
        exact ⟨⟨d, hd⟩ * n * ⟨d, hd⟩⁻¹, hN.conj_mem n hn ⟨d, hd⟩, rfl⟩) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (x : reeFixed F4 K 0) ∈ N.map (commutator (reeFixed F4 K 0)).subtype := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : reeFixed F4 K 0) ∈ N.map (commutator (reeFixed F4 K 0)).subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    rw [← Subtype.ext hyx]
    exact hy

theorem index_commutator_reeFixed_tits_le :
    (commutator (reeFixed F4 K 0)).index ≤ 2 := by
  set T := titsData K hK2
  set D := commutator (reeFixed F4 K 0)
  have htop := T.commutator_sup_zpowers_eq_top hK2
  set π := QuotientGroup.mk' D
  have hsurj : ∀ y : reeFixed F4 K 0 ⧸ D, y ∈ zpowers (π T.g₁) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D y
    have hg : g ∈ D ⊔ zpowers T.g₁ := htop ▸ Subgroup.mem_top g
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨n, ?_⟩
    have hπd : π d = 1 := (QuotientGroup.eq_one_iff d).2 hd
    show π T.g₁ ^ n = π (d * T.g₁ ^ n)
    rw [map_mul, hπd, one_mul, map_zpow]
  have hsq : π T.g₁ ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 T.g₁_sq_mem
  have hord : orderOf (π T.g₁) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hsq
  have htop' : zpowers (π T.g₁) = ⊤ := eq_top_iff.2 fun y _ => hsurj y
  calc D.index = Nat.card (reeFixed F4 K 0 ⧸ D) := rfl
    _ = Nat.card (⊤ : Subgroup (reeFixed F4 K 0 ⧸ D)) := Subgroup.card_top.symm
    _ = Nat.card (zpowers (π T.g₁)) := by rw [htop']
    _ = orderOf (π T.g₁) := Nat.card_zpowers _
    _ ≤ 2 := hord

theorem not_smallType_of_isComponentOf_reeFixed_tits {L : Subgroup (adjointGroup F4.tag K)}
    (hL : Assembly.IsComponentOf L (reeFixed F4 K 0)) : ¬ SmallType L := by
  set D := commutator (reeFixed F4 K 0)
  set J := D.map (reeFixed F4 K 0).subtype with hJ
  have hDs := isSimpleGroup_commutator_reeFixed_tits hK2
  have eJ : D ≃* J := D.equivMapOfInjective _ Subtype.val_injective
  have : IsSimpleGroup J := (MulEquiv.isSimpleGroup_congr eJ.symm).2 hDs
  have hJF : J ≤ reeFixed F4 K 0 := Subgroup.map_subtype_le D
  have hJsub : J.subgroupOf (reeFixed F4 K 0) = D :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective D
  have hJn : (J.subgroupOf (reeFixed F4 K 0)).Normal := by
    rw [hJsub]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hsolv : Group.IsSolvable (reeFixed F4 K 0 ⧸ J.subgroupOf (reeFixed F4 K 0)) := by
    have : Group.IsSolvable (Abelianization (reeFixed F4 K 0)) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
  rw [eq_of_isComponentOf_of_normal_simple hJF hJn hsolv hL, ← smallType_congr eJ]
  have hZ : center D = ⊥ := center_eq_bot_of_isSimpleGroup' (by
    obtain ⟨x, hx, y, hy, hxy⟩ := (titsData K hK2).nonabelian
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩)
  have hidx := index_commutator_reeFixed_tits_le hK2
  have hcard := card_reeFixed_F4 (K := K) (m := 0) (by rw [hK2]; norm_num)
  norm_num at hcard
  have hmul := D.card_mul_index
  rw [hcard] at hmul
  have hpos : 0 < D.index := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hmul
    omega
  interval_cases hi : D.index
  · exact not_smallType_of_two_adic hZ (N := 12) (m := 8775) (by decide) (by omega)
      (by norm_num) (by norm_num) (by norm_num) (by omega)
  · exact not_smallType_of_two_adic hZ (N := 11) (m := 8775) (by decide) (by omega)
      (by norm_num) (by norm_num) (by norm_num) (by omega)

end Tits

end CFSG.ComponentClassification.ExcSelector
