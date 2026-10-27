module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped commutatorElement

namespace ToralReduce

variable {Y : Type} [Group Y]

@[expose] def twoCenter (L : Subgroup Y) : Subgroup Y where
  carrier := {y | y ∈ L ∧ (∀ l ∈ L, y * l = l * y) ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
  mul_mem' := by
    rintro a b ⟨haL, hac, k, hk⟩ ⟨hbL, hbc, m, hm⟩
    refine ⟨L.mul_mem haL hbL, fun l hl => ?_, k + m, ?_⟩
    · rw [mul_assoc, hbc l hl, ← mul_assoc, hac l hl, mul_assoc]
    · have hab : Commute a b := hac b hbL
      rw [hab.mul_pow, pow_add, pow_mul, hk, one_pow, one_mul, mul_comm, pow_mul, hm, one_pow]
  one_mem' := ⟨L.one_mem, fun l _ => by rw [one_mul, mul_one], 0, by simp⟩
  inv_mem' := by
    rintro a ⟨haL, hac, k, hk⟩
    refine ⟨L.inv_mem haL, fun l hl => ?_, k, by rw [inv_pow, hk, inv_one]⟩
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hac l hl, mul_assoc, mul_inv_cancel, mul_one]

variable {L : Subgroup Y}

theorem twoCenter_le : twoCenter L ≤ L := fun _ h => h.1

theorem mul_comm_of_mem_twoCenter {z l : Y} (hz : z ∈ twoCenter L) (hl : l ∈ L) :
    z * l = l * z :=
  hz.2.1 l hl

theorem eq_one_of_mem_twoCenter {z : Y} (hz : z ∈ twoCenter L) {m : ℕ} (hm : Odd m)
    (hzm : z ^ m = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hz.2.2
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have := pow_gcd_eq_one.mpr ⟨hk, hzm⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem mem_twoCenter_of {z : Y} (hzL : z ∈ L) (hzc : ∀ l ∈ L, z * l = l * z) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z ∈ twoCenter L :=
  ⟨hzL, hzc, k, hk⟩

instance twoCenter_normal (L : Subgroup Y) :
    ((twoCenter L).subgroupOf (Subgroup.normalizer (L : Set Y))).Normal where
  conj_mem := by
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hzL, hzc, k, hk⟩ := hn
    have hg := g.2
    change (g : Y) * n * (g : Y)⁻¹ ∈ twoCenter L
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg n).mp hzL, fun l hl => ?_, k, ?_⟩
    · have hl' : (g : Y)⁻¹ * l * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
        rwa [inv_inv] at this
      have h := hzc _ hl'
      calc (g : Y) * n * (g : Y)⁻¹ * l = g * (n * ((g : Y)⁻¹ * l * g)) * (g : Y)⁻¹ := by group
        _ = g * (((g : Y)⁻¹ * l * g) * n) * (g : Y)⁻¹ := by rw [h]
        _ = l * (g * n * (g : Y)⁻¹) := by group
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]

abbrev TwoCenterQuot (L : Subgroup Y) : Type :=
  ↥(Subgroup.normalizer (L : Set Y)) ⧸ (twoCenter L).subgroupOf (Subgroup.normalizer (L : Set Y))

abbrev twoCenterMk (L : Subgroup Y) : ↥(Subgroup.normalizer (L : Set Y)) →* TwoCenterQuot L :=
  QuotientGroup.mk' _

@[expose] def twoCenterHom (L : Subgroup Y) : ↥L →* TwoCenterQuot L :=
  (twoCenterMk L).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem twoCenterHom_eq_iff {a b : ↥L} :
    twoCenterHom L a = twoCenterHom L b ↔ (a : Y)⁻¹ * b ∈ twoCenter L := by
  rw [twoCenterHom, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem twoCenterHom_eq_one_iff {a : ↥L} : twoCenterHom L a = 1 ↔ (a : Y) ∈ twoCenter L := by
  rw [← map_one (twoCenterHom L), twoCenterHom_eq_iff]
  simp

theorem ker_twoCenterHom_le_center : (twoCenterHom L).ker ≤ Subgroup.center ↥L := by
  intro a ha
  rw [MonoidHom.mem_ker, twoCenterHom_eq_one_iff] at ha
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subtype.ext (mul_comm_of_mem_twoCenter ha b.2).symm

theorem twoCenterMk_conj (n : ↥(Subgroup.normalizer (L : Set Y))) (a : ↥L) :
    twoCenterMk L n * twoCenterHom L a * (twoCenterMk L n)⁻¹ =
      twoCenterHom L ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 a).mp a.2⟩ := by
  rw [twoCenterHom, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
    ← map_mul]
  rfl

instance range_twoCenterHom_normal (L : Subgroup Y) : (twoCenterHom L).range.Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact ⟨_, (twoCenterMk_conj n a).symm⟩

theorem isQuasisimple_of_isQuasisimple_open {Q : Type*} [Group Q] (h : Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem exists_twoCenterHom_ne_one (hL : Open.IsQuasisimple ↥L) : ∃ a, twoCenterHom L a ≠ 1 := by
  have := hL.2
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨a, fun h => ha ?_⟩
  exact (QuotientGroup.eq_one_iff a).mpr (ker_twoCenterHom_le_center h)

noncomputable def centerQuotEquiv (hL : Open.IsQuasisimple ↥L) :
    ↥L ⧸ Subgroup.center ↥L ≃* ↥(twoCenterHom L).range ⧸ Subgroup.center ↥(twoCenterHom L).range :=
  CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple
    (isQuasisimple_of_isQuasisimple_open hL) (twoCenterHom L).rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact ker_twoCenterHom_le_center)

theorem isComponentOf_range (hL : Open.IsComponentOf L ⊤) :
    Open.IsComponentOf (twoCenterHom L).range ⊤ := by
  refine ⟨le_top, Open.IsSubnormal.step le_top Subgroup.normal_subgroupOf (Open.IsSubnormal.refl ⊤),
    ?_⟩
  have hq := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (isQuasisimple_of_isQuasisimple_open hL.2.2) (twoCenterHom L).rangeRestrict_surjective
    (by
      obtain ⟨a, ha⟩ := exists_twoCenterHom_ne_one hL.2.2
      exact ⟨a, fun h => ha (by simpa using congrArg Subtype.val h)⟩)
  exact ⟨hq.1.commutator_eq_top, hq.2.1⟩

theorem odd_card_center_range [Finite Y] (hL : Open.IsQuasisimple ↥L) :
    Odd (Nat.card (Subgroup.center ↥(twoCenterHom L).range)) := by
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (isQuasisimple_of_isQuasisimple_open hL) (twoCenterHom L).rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact ker_twoCenterHom_le_center)
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hwZ : (w : ↥(twoCenterHom L).range) ∈ (Subgroup.center ↥L).map
      (twoCenterHom L).rangeRestrict := hZ ▸ w.2
  obtain ⟨z, hz, hzw⟩ := hwZ
  have hw2 : (w : ↥(twoCenterHom L).range) ^ 2 = 1 := by
    rw [← hw]
    have := pow_orderOf_eq_one w
    exact congrArg Subtype.val this
  have hz2 : twoCenterHom L (z ^ 2) = 1 := by
    rw [map_pow]
    have := congrArg Subtype.val (show ((twoCenterHom L).rangeRestrict z) ^ 2 = 1 by
      rw [hzw]; exact hw2)
    simpa using this
  obtain ⟨k, hk⟩ := (twoCenterHom_eq_one_iff.mp hz2).2.2
  have hzc : ∀ l ∈ L, (z : Y) * l = l * z := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩).symm
  have hzT : (z : Y) ∈ twoCenter L :=
    mem_twoCenter_of z.2 hzc (k := k + 1) (by
      rw [pow_succ, mul_comm, pow_mul]
      simpa using hk)
  have hz1 : (twoCenterHom L).rangeRestrict z = 1 :=
    Subtype.ext (by simpa using twoCenterHom_eq_one_iff.mpr hzT)
  have hw1 : w = 1 := by
    apply Subtype.ext
    rw [← hzw, hz1]
    rfl
  rw [hw1, orderOf_one] at hw
  exact absurd hw (by norm_num)

theorem commute_of_twoCenterHom_conj {x l : ↥L} {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (h : twoCenterHom L (x * l * x⁻¹) = twoCenterHom L l) : x * l * x⁻¹ = l := by
  rw [twoCenterHom_eq_iff] at h
  have hxm' : (x : Y) ^ m = 1 := by simpa using congrArg Subtype.val hxm
  set z : Y := ((x * l * x⁻¹ : ↥L) : Y)⁻¹ * l with hzdef
  have hz : z⁻¹ * x = (l : Y)⁻¹ * x * l := by
    rw [hzdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcomm : Commute z⁻¹ (x : Y) := mul_comm_of_mem_twoCenter ((twoCenter L).inv_mem h) x.2
  have hzm : (z ^ m)⁻¹ = 1 := by
    have h1 : (z⁻¹ * x) ^ m = 1 := by
      rw [hz, show (l : Y)⁻¹ * x * l = (l : Y)⁻¹ * x * (l : Y)⁻¹⁻¹ by rw [inv_inv], conj_pow,
        hxm', mul_one, inv_inv, inv_mul_cancel]
    rwa [hcomm.mul_pow, hxm', mul_one, inv_pow] at h1
  have hz1 : z = 1 := eq_one_of_mem_twoCenter h hm (inv_eq_one.mp hzm)
  rw [hzdef, inv_mul_eq_one] at hz1
  exact Subtype.ext hz1

end ToralReduce

end CFSG.AGLEmbedding
