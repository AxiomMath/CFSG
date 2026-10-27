module

public import CFSG.FeitThompson.Representations.CoprimeOrdersDisjointPuncturedSupports
public import CFSG.FeitThompson.Representations.OddCyclicFactorOrders
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

theorem conjugatesOfSet_eq_iUnion {G : Type*} [Group G] (S : Set G) :
    Group.conjugatesOfSet S = ⋃ g : G, (fun x => g⁻¹ * x * g) '' S := by
  ext x
  simp only [Group.mem_conjugatesOfSet_iff, Set.mem_iUnion, Set.mem_image, isConj_iff]
  constructor
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨c⁻¹, a, ha, by group⟩
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨a, ha, g⁻¹, by group⟩

variable {G : Type*} [Group G]

theorem mem_conjugatesOfSet_of_conj_mem {S : Set G} {x t : G} (hx : t⁻¹ * x * t ∈ S) :
    x ∈ Group.conjugatesOfSet S :=
  Group.mem_conjugatesOfSet_iff.2 ⟨_, hx, isConj_iff.2 ⟨t, by group⟩⟩

theorem puncturedConjSupport_eq_conjugatesOfSet (H : Subgroup G) :
    puncturedConjSupport H = Group.conjugatesOfSet ((H : Set G) \ {1}) := by
  ext x
  rw [mem_puncturedConjSupport_iff, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, hx1⟩
    exact ⟨g * x * g⁻¹, ⟨hg, by simpa using hx1⟩, isConj_iff.2 ⟨g⁻¹, by group⟩⟩
  · rintro ⟨a, ⟨haH, ha1⟩, hconj⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    exact ⟨⟨c⁻¹, by simpa [mul_assoc] using haH⟩, by simpa using ha1⟩

private theorem orderOf_conj_eq (t x : G) : orderOf (t⁻¹ * x * t) = orderOf x := by
  simpa [MulAut.conj, mul_assoc] using
    orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective x

structure IsFrobeniusPartnerConfig (N H U K W1 W2 : Subgroup G) : Prop where
  ne_bot_H : H ≠ ⊥
  ne_bot_U : U ≠ ⊥
  ne_bot_W1 : W1 ≠ ⊥
  ne_bot_W2 : W2 ≠ ⊥
  le_N_H : H ≤ N
  normal_subgroupOf_H : (H.subgroupOf N).Normal
  disjoint_H_U : Disjoint H U
  coe_K_eq : (K : Set G) = (H : Set G) * (U : Set G)
  normal_subgroupOf_K : (K.subgroupOf N).Normal
  coe_N_eq : (N : Set G) = (K : Set G) * (W2 : Set G)
  disjoint_K_W2 : Disjoint K W2
  coprime_natCard_K_W2 : (Nat.card K).Coprime (Nat.card W2)
  le_normalizer_H : U ≤ normalizer (H : Set G)
  le_normalizer_U : W2 ≤ normalizer (U : Set G)
  hall_H : (Nat.card H).Coprime H.index
  inf_centralizer_H_eq_bot : ∀ u ∈ U, u ≠ 1 → H ⊓ centralizer {u} = ⊥
  le_H_W1 : W1 ≤ H
  inf_centralizer_K_eq_W1 : ∀ w ∈ W2, w ≠ 1 → K ⊓ centralizer {w} = W1
  isCyclic_W1 : IsCyclic W1
  isCyclic_W2 : IsCyclic W2
  setOf_conj_eq_self : {g : G | (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1})
    = (H : Set G) \ {1}} = (N : Set G)
  inter_conj_image_eq_empty : ∀ g ∉ N,
    ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅

namespace IsFrobeniusPartnerConfig

variable {N H U K W1 W2 : Subgroup G} (hc : IsFrobeniusPartnerConfig N H U K W1 W2)

include hc

theorem le_K_H : H ≤ K := fun h hh => by
  rw [← SetLike.mem_coe, hc.coe_K_eq]; exact ⟨h, hh, 1, U.one_mem, mul_one h⟩

theorem le_K_U : U ≤ K := fun u hu => by
  rw [← SetLike.mem_coe, hc.coe_K_eq]; exact ⟨1, H.one_mem, u, hu, one_mul u⟩

theorem le_N_K : K ≤ N := fun k hk => by
  rw [← SetLike.mem_coe, hc.coe_N_eq]; exact ⟨k, hk, 1, W2.one_mem, mul_one k⟩

theorem le_N_W2 : W2 ≤ N := fun w hw => by
  rw [← SetLike.mem_coe, hc.coe_N_eq]; exact ⟨1, K.one_mem, w, hw, one_mul w⟩

theorem le_K_W1 : W1 ≤ K := hc.le_H_W1.trans hc.le_K_H

theorem sup_eq_K : H ⊔ U = K :=
  le_antisymm (sup_le hc.le_K_H hc.le_K_U) fun k hk => by
    rw [← SetLike.mem_coe, hc.coe_K_eq] at hk
    obtain ⟨h, hh, u, hu, rfl⟩ := hk
    exact mul_mem (le_sup_left (b := U) hh) (le_sup_right (a := H) hu)

theorem sup_eq_N : K ⊔ W2 = N :=
  le_antisymm (sup_le hc.le_N_K hc.le_N_W2) fun n hn => by
    rw [← SetLike.mem_coe, hc.coe_N_eq] at hn
    obtain ⟨k, hk, w, hw, rfl⟩ := hn
    exact mul_mem (le_sup_left (b := W2) hk) (le_sup_right (a := K) hw)

theorem normalizer_sdiff_eq : normalizer ((H : Set G) \ {1}) = N :=
  SetLike.coe_injective
    ((setOf_conj_eq_self_eq_normalizer _).symm.trans hc.setOf_conj_eq_self)

theorem isTIWithNormalizer : IsTIWithNormalizer ((H : Set G) \ {1}) N where
  nonempty := by
    obtain ⟨⟨x, hxH⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_H
    exact ⟨x, hxH, by simpa using hx⟩
  one_notMem := by simp
  normalizer_eq := hc.normalizer_sdiff_eq
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ N := fun hcon => hg (by simpa using N.inv_mem hcon)
    refine Set.disjoint_iff_inter_eq_empty.2
      (Eq.trans ?_ (hc.inter_conj_image_eq_empty g⁻¹ hg'))
    exact congrArg _ (Set.image_congr' fun x => by simp)

theorem le_normalizer_K : W2 ≤ normalizer (K : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  have key := (Subgroup.normal_subgroupOf_iff hc.le_N_K).1 hc.normal_subgroupOf_K
  have hwN : w ∈ N := hc.le_N_W2 hw
  intro k
  refine ⟨fun hk => key k w hk hwN, fun hk => ?_⟩
  simpa [mul_assoc] using key _ w⁻¹ hk (N.inv_mem hwN)

theorem inf_W1_W2_eq_bot : W1 ⊓ W2 = ⊥ :=
  le_bot_iff.1 (le_trans (inf_le_inf_right W2 hc.le_K_W1) hc.disjoint_K_W2.le_bot)

theorem commute_W1_W2 {c w : G} (hcm : c ∈ W1) (hw : w ∈ W2) : c * w = w * c := by
  rcases eq_or_ne w 1 with rfl | hw1
  · simp
  · have hm : c ∈ K ⊓ centralizer ({w} : Set G) := by
      rw [hc.inf_centralizer_K_eq_W1 w hw hw1]; exact hcm
    exact Subgroup.mem_centralizer_singleton_iff.1 hm.2

theorem le_centralizer_W1 : W2 ≤ centralizer (W1 : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_iff.2 fun _ hcm => hc.commute_W1_W2 hcm hw

theorem coe_sup_W1_W2_eq : ((W1 ⊔ W2 : Subgroup G) : Set G) = (W1 : Set G) * (W2 : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left W1 W2
    (hc.le_centralizer_W1.trans (Subgroup.centralizer_le_normalizer _))

theorem cyclicTIDiff_eq :
    cyclicTIDiff (W1 ⊔ W2) W1 W2
      = ((W1 : Set G) * (W2 : Set G)) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  ext x
  rw [mem_cyclicTIDiff, Set.mem_sdiff, ← hc.coe_sup_W1_W2_eq]
  simp [not_or]

theorem mul_mem_cyclicTIDiff {c w : G} (hcm : c ∈ W1) (hc1 : c ≠ 1) (hw : w ∈ W2)
    (hw1 : w ≠ 1) : c * w ∈ cyclicTIDiff (W1 ⊔ W2) W1 W2 := by
  have hb := hc.inf_W1_W2_eq_bot
  refine mem_cyclicTIDiff.2 ⟨mul_mem (le_sup_left (b := W2) hcm) (le_sup_right (a := W1) hw),
    ?_, ?_⟩
  · intro hmem
    have hx : w ∈ W1 ⊓ W2 := ⟨by simpa using mul_mem (W1.inv_mem hcm) hmem, hw⟩
    rw [hb, Subgroup.mem_bot] at hx
    exact hw1 hx
  · intro hmem
    have hx : c ∈ W1 ⊓ W2 := ⟨hcm, by simpa using mul_mem hmem (W2.inv_mem hw)⟩
    rw [hb, Subgroup.mem_bot] at hx
    exact hc1 hx

theorem mem_N_of_commute {b x : G} (hb : b ∈ H) (hb1 : b ≠ 1) (hx : x * b = b * x) : x ∈ N := by
  by_contra hxN
  have hmem : b ∈ ((H : Set G) \ {1}) ∩ (fun z => x⁻¹ * z * x) '' ((H : Set G) \ {1}) := by
    refine ⟨⟨hb, by simpa using hb1⟩, b, ⟨hb, by simpa using hb1⟩, ?_⟩
    change x⁻¹ * b * x = b
    rw [show x⁻¹ * b * x = x⁻¹ * (b * x) from by group, ← hx]
    group
  rw [hc.inter_conj_image_eq_empty x hxN] at hmem
  exact hmem

section Finite

variable [Finite G]

theorem coprime_natCard_H_U : (Nat.card H).Coprime (Nat.card U) := by
  have hprod : Nat.card K = Nat.card H * Nat.card U := by
    have h := natCard_mul_mul_natCard_inf H U
    rw [hc.disjoint_H_U.eq_bot] at h
    simp only [Subgroup.card_bot, mul_one] at h
    rw [← h]
    exact Nat.card_congr (Set.equivOfEq hc.coe_K_eq)
  have hdvd : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
  rw [hprod, ← Subgroup.card_mul_index H] at hdvd
  exact hc.hall_H.coprime_dvd_right
    ((mul_dvd_mul_iff_left (a := Nat.card H) Nat.card_pos.ne').1 hdvd)

theorem factorization_natCard_eq {r : ℕ} (hr : r.Prime) (hrH : r ∣ Nat.card H) :
    (Nat.card G).factorization r = (Nat.card H).factorization r := by
  have hidx : ¬ r ∣ H.index := fun h =>
    hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc.hall_H hrH h)
  rw [← Subgroup.card_mul_index H, Nat.factorization_mul (a := Nat.card H) (b := H.index)
    Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hidx]

theorem exists_conj_mem_H {r : ℕ} (hr : r.Prime) (hrH : r ∣ Nat.card H) {a : G}
    (ha : orderOf a = r) : ∃ t : G, t⁻¹ * a * t ∈ H := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨T, -, hTH, hT⟩ := exists_le_natCard_eq_pow_factorization (R := (⊥ : Subgroup G))
    (H := H) hr bot_le IsPGroup.of_bot
  rw [← hc.factorization_natCard_eq hr hrH] at hT
  obtain ⟨t, ht⟩ := exists_forall_inv_mul_mul_mem hT
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one]))
  exact ⟨t, hTH (ht a (mem_zpowers a))⟩

theorem mem_H_of_mem_K_of_commute {b y : G} (hb : b ∈ H) (hb1 : b ≠ 1) (hy : y ∈ K)
    (hcomm : b * y = y * b) : y ∈ H := by
  by_contra hyH
  rw [← SetLike.mem_coe, hc.coe_K_eq] at hy
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hy
  simp only [SetLike.mem_coe] at hh hu
  have hu1 : u ≠ 1 := by rintro rfl; exact hyH (by simpa using hh)
  have hCu : H ⊓ centralizer ({u} : Set G) = ⊥ := hc.inf_centralizer_H_eq_bot u hu hu1
  have hcop : (Nat.card H).Coprime (orderOf u) :=
    hc.coprime_natCard_H_U.coprime_dvd_right (U.orderOf_dvd_natCard hu)
  have hmem : h * u ∈ (H : Set G) * ({u} : Set G) := ⟨h, hh, u, rfl, rfl⟩
  rw [← sUnion_centralizerCosetConjugates hcop (isOfFinOrder_of_finite u)
    (hc.le_normalizer_H hu)] at hmem
  obtain ⟨S, hS, hyS⟩ := hmem
  obtain ⟨z, hz, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff, mem_centralizerCoset_iff, hCu, Subgroup.mem_bot] at hyS
  have hzy : z⁻¹ * (h * u) * z = u := by
    rw [← mul_inv_eq_one]; simpa using hyS
  have hbzc : z⁻¹ * b * z ∈ centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzy]
    calc z⁻¹ * b * z * (z⁻¹ * (h * u) * z) = z⁻¹ * (b * (h * u)) * z := by group
      _ = z⁻¹ * ((h * u) * b) * z := by rw [hcomm]
      _ = z⁻¹ * (h * u) * z * (z⁻¹ * b * z) := by group
  have hbz : z⁻¹ * b * z ∈ H ⊓ centralizer ({u} : Set G) :=
    Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem (H.inv_mem hz) hb) hz, hbzc⟩
  rw [hCu, Subgroup.mem_bot] at hbz
  refine hb1 ?_
  have hb' : b = z * (z⁻¹ * b * z) * z⁻¹ := by group
  rw [hb', hbz]; group

theorem exists_conj_mem_cyclicTIDiff {r : ℕ} (hr : r.Prime) (hrW1 : r ∣ Nat.card W1)
    {y : G} (hyN : y ∈ N) (hyK : y ∉ K) (hry : r ∣ orderOf y) :
    ∃ z : G, z⁻¹ * y * z ∈ cyclicTIDiff (W1 ⊔ W2) W1 W2 := by
  rw [← SetLike.mem_coe, hc.coe_N_eq] at hyN
  obtain ⟨k, hk, w, hw, hkw⟩ := Set.mem_mul.1 hyN
  simp only [SetLike.mem_coe] at hk hw
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hyK (by rw [← hkw, mul_one]; exact hk)
  have hcopK : (Nat.card K).Coprime (orderOf w) :=
    hc.coprime_natCard_K_W2.coprime_dvd_right (W2.orderOf_dvd_natCard hw)
  have hmem : y ∈ (K : Set G) * ({w} : Set G) := ⟨k, hk, w, rfl, hkw⟩
  rw [← sUnion_centralizerCosetConjugates hcopK (isOfFinOrder_of_finite w)
    (hc.le_normalizer_K hw)] at hmem
  obtain ⟨S, hS, hyS⟩ := hmem
  obtain ⟨z, hz, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff, mem_centralizerCoset_iff,
    hc.inf_centralizer_K_eq_W1 w hw hw1] at hyS
  refine ⟨z, ?_⟩
  have hczw : (z⁻¹ * y * z * w⁻¹) * w = z⁻¹ * y * z := by group
  have hcne : z⁻¹ * y * z * w⁻¹ ≠ 1 := by
    intro h0
    rw [h0, one_mul] at hczw
    have hord : orderOf y = orderOf w := by rw [← orderOf_conj_eq z y, hczw]
    have hrK : r ∣ Nat.card K := hrW1.trans (Subgroup.card_dvd_of_le hc.le_K_W1)
    have hrW2 : r ∣ Nat.card W2 := (hord ▸ hry).trans (W2.orderOf_dvd_natCard hw)
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc.coprime_natCard_K_W2 hrK hrW2)
  rw [← hczw]
  exact hc.mul_mem_cyclicTIDiff hyS hcne hw hw1

theorem mem_union_conjugatesOfSet {g : G} (hg : 1 < Nat.gcd (orderOf g) (Nat.card W1)) :
    g ∈ Group.conjugatesOfSet ((H : Set G) \ {1})
      ∪ Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2) := by
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd (orderOf g) (Nat.card W1))
    hg.ne'
  have hrg : r ∣ orderOf g := hrdvd.trans (Nat.gcd_dvd_left _ _)
  have hrW1 : r ∣ Nat.card W1 := hrdvd.trans (Nat.gcd_dvd_right _ _)
  have hrH : r ∣ Nat.card H := hrW1.trans (Subgroup.card_dvd_of_le hc.le_H_W1)
  have ha : orderOf (g ^ (orderOf g / r)) = r :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hrg
  have hag : g ^ (orderOf g / r) * g = g * g ^ (orderOf g / r) := (Commute.self_pow g _).symm.eq
  obtain ⟨t, ht⟩ := hc.exists_conj_mem_H hr hrH ha
  have hb1 : t⁻¹ * g ^ (orderOf g / r) * t ≠ 1 := by
    intro h0
    have h1 : orderOf (t⁻¹ * g ^ (orderOf g / r) * t) = 1 := by rw [h0, orderOf_one]
    rw [orderOf_conj_eq, ha] at h1
    exact hr.one_lt.ne' h1
  have hyord : orderOf (t⁻¹ * g * t) = orderOf g := orderOf_conj_eq t g
  have hry : r ∣ orderOf (t⁻¹ * g * t) := hyord ▸ hrg
  have hby : (t⁻¹ * g ^ (orderOf g / r) * t) * (t⁻¹ * g * t)
      = (t⁻¹ * g * t) * (t⁻¹ * g ^ (orderOf g / r) * t) := by
    calc t⁻¹ * g ^ (orderOf g / r) * t * (t⁻¹ * g * t)
        = t⁻¹ * (g ^ (orderOf g / r) * g) * t := by group
      _ = t⁻¹ * (g * g ^ (orderOf g / r)) * t := by rw [hag]
      _ = t⁻¹ * g * t * (t⁻¹ * g ^ (orderOf g / r) * t) := by group
  have hyN : t⁻¹ * g * t ∈ N := hc.mem_N_of_commute ht hb1 hby.symm
  by_cases hyK : t⁻¹ * g * t ∈ K
  ·
    refine Or.inl (mem_conjugatesOfSet_of_conj_mem (t := t) ⟨?_, ?_⟩)
    · exact hc.mem_H_of_mem_K_of_commute ht hb1 hyK hby
    · simp only [Set.mem_singleton_iff]
      intro h0
      have h1 : orderOf (t⁻¹ * g * t) = 1 := by rw [h0, orderOf_one]
      exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one (h1 ▸ hry))
  ·
    obtain ⟨z, hz⟩ := hc.exists_conj_mem_cyclicTIDiff hr hrW1 hyN hyK hry
    refine Or.inr (mem_conjugatesOfSet_of_conj_mem (t := t * z) ?_)
    rw [show (t * z)⁻¹ * g * (t * z) = z⁻¹ * (t⁻¹ * g * t) * z from by group]
    exact hz

theorem mem_union_puncturedConjSupport {g : G}
    (hg : 1 < Nat.gcd (orderOf g) (Nat.card W1)) :
    g ∈ puncturedConjSupport H
      ∪ Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2) := by
  rw [puncturedConjSupport_eq_conjugatesOfSet]
  exact hc.mem_union_conjugatesOfSet hg

end Finite

end IsFrobeniusPartnerConfig

end CFSG.FeitThompson
