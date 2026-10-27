module

public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.OddOrder.CyclicDirectProductCoprimeFactors

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

def cyclicTIDiff (W W1 W2 : Subgroup G) : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))

@[simp]
theorem mem_cyclicTIDiff {W W1 W2 : Subgroup G} {x : G} :
    x ∈ cyclicTIDiff W W1 W2 ↔ x ∈ W ∧ x ∉ W1 ∧ x ∉ W2 := by
  simp [cyclicTIDiff, not_or]

theorem cyclicTIDiff_subset {W W1 W2 : Subgroup G} : cyclicTIDiff W W1 W2 ⊆ (W : Set G) :=
  Set.sdiff_subset

theorem setOf_conj_eq_self_eq_normalizer (D : Set G) :
    {g : G | (fun x => g⁻¹ * x * g) '' D = D} = (Subgroup.normalizer D : Set G) := by
  ext g
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  rw [← Subgroup.inv_mem_iff (H := Subgroup.normalizer D),
    Subgroup.mem_normalizer_iff_conj_image_eq]
  exact ⟨fun hg => Eq.trans (Set.image_congr' fun x => by simp) hg,
    fun hg => Eq.trans (Set.image_congr' fun x => by simp) hg⟩

structure IsCyclicTIPair (W W1 W2 : Subgroup G) : Prop where
  left_ne_bot : W1 ≠ ⊥
  right_ne_bot : W2 ≠ ⊥
  mul_eq : (W1 : Set G) * (W2 : Set G) = (W : Set G)
  inf_eq_bot : W1 ⊓ W2 = ⊥
  commute : ∀ x ∈ W1, ∀ y ∈ W2, x * y = y * x
  isCyclic : IsCyclic ↥W
  odd_natCard : Odd (Nat.card ↥W)
  setOf_conj_eq_self : {g : G | (fun x => g⁻¹ * x * g) '' cyclicTIDiff W W1 W2
    = cyclicTIDiff W W1 W2} = (W : Set G)
  inter_eq_empty : ∀ g ∉ W,
    (fun x => g⁻¹ * x * g) '' cyclicTIDiff W W1 W2 ∩ cyclicTIDiff W W1 W2 = ∅

namespace IsCyclicTIPair

variable {W W1 W2 : Subgroup G} (h : IsCyclicTIPair W W1 W2)

include h

theorem left_le : W1 ≤ W := fun a ha => by
  rw [← SetLike.mem_coe, ← h.mul_eq]; exact ⟨a, ha, 1, one_mem _, mul_one a⟩

theorem right_le : W2 ≤ W := fun a ha => by
  rw [← SetLike.mem_coe, ← h.mul_eq]; exact ⟨1, one_mem _, a, ha, one_mul a⟩

theorem normalizer_cyclicTIDiff : Subgroup.normalizer (cyclicTIDiff W W1 W2) = W :=
  SetLike.coe_injective ((setOf_conj_eq_self_eq_normalizer _).symm.trans h.setOf_conj_eq_self)

theorem odd_natCard_left : Odd (Nat.card W1) :=
  h.odd_natCard.of_dvd_nat (Subgroup.card_dvd_of_le h.left_le)

theorem odd_natCard_right : Odd (Nat.card W2) :=
  h.odd_natCard.of_dvd_nat (Subgroup.card_dvd_of_le h.right_le)

theorem finite_coe : Finite W := Nat.finite_of_card_ne_zero h.odd_natCard.pos.ne'

theorem finite_left : Finite W1 := Nat.finite_of_card_ne_zero h.odd_natCard_left.pos.ne'

theorem finite_right : Finite W2 := Nat.finite_of_card_ne_zero h.odd_natCard_right.pos.ne'

theorem inf_subgroupOf_eq_bot : W1.subgroupOf W ⊓ W2.subgroupOf W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : G) ∈ W1 ⊓ W2 := ⟨hx.1, hx.2⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem coprime_natCard : (Nat.card W1).Coprime (Nat.card W2) := by
  have := h.isCyclic
  have := h.finite_coe
  have hc := coprime_natCard_of_inf_eq_bot h.inf_subgroupOf_eq_bot
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.left_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.right_le).toEquiv] at hc

theorem three_le_natCard_left : 3 ≤ Nat.card W1 := by
  have := h.finite_left
  have h1 : 1 < Nat.card W1 := W1.one_lt_card_iff_ne_bot.mpr h.left_ne_bot
  obtain ⟨k, hk⟩ := h.odd_natCard_left
  omega

theorem three_le_natCard_right : 3 ≤ Nat.card W2 := by
  have := h.finite_right
  have h1 : 1 < Nat.card W2 := W2.one_lt_card_iff_ne_bot.mpr h.right_ne_bot
  obtain ⟨k, hk⟩ := h.odd_natCard_right
  omega

theorem natCard_ne : Nat.card W1 ≠ Nat.card W2 := by
  intro he
  have hco := h.coprime_natCard
  rw [Nat.Coprime, he, Nat.gcd_self] at hco
  have := h.three_le_natCard_right
  omega

theorem commute_of_mem {x y : G} (hx : x ∈ W1) (hy : y ∈ W2) : x * y = y * x :=
  h.commute x hx y hy

theorem nonempty_cyclicTIDiff : (cyclicTIDiff W W1 W2).Nonempty := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.left_ne_bot
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.right_ne_bot
  simp only [ne_eq, Subtype.ext_iff, OneMemClass.coe_one] at ha1 hb1
  refine ⟨a * b, mem_cyclicTIDiff.mpr ⟨mul_mem (h.left_le ha) (h.right_le hb), ?_, ?_⟩⟩
  · intro hmem
    have hb' : b ∈ W1 ⊓ W2 := ⟨by simpa using mul_mem (W1.inv_mem ha) hmem, hb⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at hb'
    exact hb1 hb'
  · intro hmem
    have ha' : a ∈ W1 ⊓ W2 := ⟨ha, by simpa using mul_mem hmem (W2.inv_mem hb)⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at ha'
    exact ha1 ha'

theorem isTIWithNormalizer : IsTIWithNormalizer (cyclicTIDiff W W1 W2) W where
  nonempty := h.nonempty_cyclicTIDiff
  one_notMem := by simp
  normalizer_eq := h.normalizer_cyclicTIDiff
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ W := fun hc => hg (by simpa using W.inv_mem hc)
    refine Set.disjoint_iff_inter_eq_empty.2 (Eq.trans ?_ (h.inter_eq_empty _ hg'))
    rw [Set.inter_comm]
    congr 1
    exact Set.image_congr' fun x => by simp [MulAut.conj]

theorem even_natCard_sub_one_left : Even (Nat.card W1 - 1) :=
  Nat.Odd.sub_odd h.odd_natCard_left odd_one

theorem even_natCard_sub_one_right : Even (Nat.card W2 - 1) :=
  Nat.Odd.sub_odd h.odd_natCard_right odd_one

theorem two_le_natCard_sub_one_left : 2 ≤ Nat.card W1 - 1 := by
  have := h.three_le_natCard_left; omega

theorem two_le_natCard_sub_one_right : 2 ≤ Nat.card W2 - 1 := by
  have := h.three_le_natCard_right; omega

theorem natCard_sub_one_ne : Nat.card W1 - 1 ≠ Nat.card W2 - 1 := by
  have h1 := h.three_le_natCard_left
  have h2 := h.three_le_natCard_right
  have := h.natCard_ne
  omega

end IsCyclicTIPair

theorem isCyclicTIPair_top {G : Type*} [CommGroup G] [IsCyclic G] {W1 W2 : Subgroup G}
    (hodd : Odd (Nat.card G)) (h1 : W1 ≠ ⊥) (h2 : W2 ≠ ⊥) (hinf : W1 ⊓ W2 = ⊥)
    (hmul : (W1 : Set G) * (W2 : Set G) = Set.univ) : IsCyclicTIPair ⊤ W1 W2 where
  left_ne_bot := h1
  right_ne_bot := h2
  mul_eq := by simpa using hmul
  inf_eq_bot := hinf
  commute := fun x _ y _ => mul_comm x y
  isCyclic := (Subgroup.topEquiv (G := G)).isCyclic.mpr ‹_›
  odd_natCard := by simpa using hodd
  setOf_conj_eq_self := by
    ext g
    simp only [Set.mem_ofPred_eq, Subgroup.coe_top, Set.mem_univ, iff_true]
    rw [show (fun x : G => g⁻¹ * x * g) = id from funext fun x => by simp [mul_comm]]
    simp
  inter_eq_empty := fun g hg => absurd (Subgroup.mem_top g) hg

theorem IsCyclicTIPair.odd_three_le_coprime_natCard_ne {W W1 W2 : Subgroup G}
    (h : IsCyclicTIPair W W1 W2) :
    (Odd (Nat.card W1) ∧ 3 ≤ Nat.card W1) ∧ (Odd (Nat.card W2) ∧ 3 ≤ Nat.card W2) ∧
      (Nat.card W1).Coprime (Nat.card W2) ∧ Nat.card W1 ≠ Nat.card W2 :=
  ⟨⟨h.odd_natCard_left, h.three_le_natCard_left⟩,
    ⟨h.odd_natCard_right, h.three_le_natCard_right⟩, h.coprime_natCard, h.natCard_ne⟩

theorem IsCyclicTIPair.even_two_le_natCard_sub_one_ne {W W1 W2 : Subgroup G}
    (h : IsCyclicTIPair W W1 W2) :
    (Even (Nat.card W1 - 1) ∧ 2 ≤ Nat.card W1 - 1) ∧
      (Even (Nat.card W2 - 1) ∧ 2 ≤ Nat.card W2 - 1) ∧
        Nat.card W1 - 1 ≠ Nat.card W2 - 1 :=
  ⟨⟨h.even_natCard_sub_one_left, h.two_le_natCard_sub_one_left⟩,
    ⟨h.even_natCard_sub_one_right, h.two_le_natCard_sub_one_right⟩, h.natCard_sub_one_ne⟩

end CFSG.FeitThompson
