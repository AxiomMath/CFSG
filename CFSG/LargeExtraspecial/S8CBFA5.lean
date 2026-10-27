module

public import CFSG.LargeExtraspecial.S8CBFSect
public import CFSG.Foundations.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup

variable {X : Type*} [Group X]

theorem exists_mul_ne_of_card_sixty {G : Type*} [Group G] [IsSimpleGroup G]
    (h : Nat.card G = 60) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have := Fact.mk Nat.prime_two
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [h]; norm_num)
  have hn : (zpowers g).Normal := by
    constructor
    intro n _ x
    rwa [hc x n, mul_inv_cancel_right]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with hb | ht
  · rw [zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have := congrArg (fun H : Subgroup G => Nat.card H) ht
    simp only [Nat.card_zpowers, hg, card_top, h] at this
    exact absurd this (by norm_num)

theorem exists_mul_ne_of_normalClosure {t : X}
    (h : ∃ a ∈ normalClosure ({t} : Set X), ∃ b ∈ normalClosure ({t} : Set X), a * b ≠ b * a) :
    ∃ u ∈ normalClosure ({t} : Set X), u * t ≠ t * u := by
  by_contra hc
  push Not at hc
  have ht : t ∈ centralizer (normalClosure ({t} : Set X) : Set X) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact hc u hu
  have hle : normalClosure ({t} : Set X) ≤ centralizer (normalClosure ({t} : Set X) : Set X) :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr ht)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact hab ((mem_centralizer_iff.mp (hle hb)) a ha)

theorem exists_mul_ne_of_section_nonabelian {t : X} {R N : Subgroup X}
    (hRU : R ≤ normalClosure ({t} : Set X)) [(N.subgroupOf R).Normal]
    (hab : ∃ a b : ↥R ⧸ N.subgroupOf R, a * b ≠ b * a) :
    ∃ u ∈ normalClosure ({t} : Set X), u * t ≠ t * u := by
  refine exists_mul_ne_of_normalClosure ?_
  by_contra hc
  push Not at hc
  obtain ⟨a, b, hab⟩ := hab
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hc a (hRU a.2) b (hRU b.2)))

theorem false_of_section_sixty_of_isSolvable {t : X} (hto : orderOf t = 2)
    (hS : ∀ s : ↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)),
      orderOf s = 2 → Group.IsSolvable (centralizer ({s} : Set _)))
    {R N : Subgroup X} (hNR : N ≤ R) (hRU : R ≤ normalClosure ({t} : Set X))
    (hRt : R ≤ centralizer ({t} : Set X)) [(N.subgroupOf R).Normal]
    [IsSimpleGroup (↥R ⧸ N.subgroupOf R)] (h60 : Nat.card (↥R ⧸ N.subgroupOf R) = 60) :
    False := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_card_sixty h60
  have hnc := exists_mul_ne_of_section_nonabelian hRU ⟨a, b, hab⟩
  have htU : t ∈ normalClosure ({t} : Set X) := subset_normalClosure (Set.mem_singleton t)
  exact hab (comm_of_section_of_isSolvable_centralizer _ hS htU hto hnc hNR
    (le_inf hRU hRt) a b)

theorem card_dvd_card_quotient_center_of_extraspecial [Finite X] {U N : Subgroup X} {t : X}
    (hNU : N ≤ U) (htN : t ∈ N) (hto : orderOf t = 2) (hNt : N ≤ centralizer ({t} : Set X))
    (hnc : ∃ u ∈ U, u * t ≠ t * u) (hN : CFSG.IsExtraspecialPGroup 2 N) :
    Nat.card N ∣ Nat.card (↥U ⧸ center ↥U) := by
  let φ : N →* ↥U ⧸ center ↥U :=
    (QuotientGroup.mk' (center ↥U)).comp (Subgroup.inclusion hNU)
  have htc : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro n
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hNt n.2))
  have hzp : zpowers (⟨t, htN⟩ : N) = center N := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr htc)
    rw [hN.2.2.2, Nat.card_zpowers, Subgroup.orderOf_mk, hto]
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    have hnZ : Subgroup.inclusion hNU n ∈ center ↥U :=
      (QuotientGroup.eq_one_iff _).mp hn
    have hnN : n ∈ center N := by
      rw [mem_center_iff]
      intro m
      have h1 := congrArg (fun x : U => (x : X)) (mem_center_iff.mp hnZ (Subgroup.inclusion hNU m))
      exact Subtype.ext h1
    rw [← hzp] at hnN
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hnN
    have hot : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk, hto]
    rw [mem_bot, ← zpow_mod_orderOf, hot]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [Nat.cast_two, hk, zpow_zero]
    · exfalso
      obtain ⟨u, hu, hut⟩ := hnc
      apply hut
      have hk' : (⟨t, htN⟩ : N) ^ k = ⟨t, htN⟩ := by
        rw [← zpow_mod_orderOf, hot, Nat.cast_two, hk, zpow_one]
      have := mem_center_iff.mp hnZ ⟨u, hu⟩
      rw [hk'] at this
      exact congrArg Subtype.val this
  exact Subgroup.card_dvd_of_injective φ hφ

theorem card_lt_of_two_pow_nine_not_dvd {P : Type*} [Group P] [Finite P] {n : ℕ}
    (hP : CFSG.IsExtraspecialPGroup 2 P) (hdvd : Nat.card P ∣ n) (hn : ¬ 2 ^ 9 ∣ n) :
    Nat.card P < 2 ^ 9 := by
  have := Fact.mk Nat.prime_two
  obtain ⟨k, hk⟩ := hP.1.exists_card_eq
  rw [hk] at hdvd ⊢
  by_contra hle
  push Not at hle
  have h9 : 9 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  exact hn ((Nat.pow_dvd_pow 2 h9).trans hdvd)

end CFSG.LargeExtraspecial.S8
