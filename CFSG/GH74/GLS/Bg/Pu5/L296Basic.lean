module

public import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
public import CFSG.GH74.GLS.Bg.Pu5.LPTPBasic
public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G]


theorem ncard_four_eq {a b : G} (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : ({1, a, b, a * b} : Set G).ncard = 4 := by
  classical
  have h1 : (1 : G) ≠ a := ha1.symm
  have h2 : (1 : G) ≠ b := hb1.symm
  have h3 : (1 : G) ≠ a * b := by
    intro h
    apply hne
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hb)
  have h4 : a ≠ a * b := by
    intro h
    apply hb1
    have := mul_left_cancel (a := a) (b := 1) (c := b) (by rw [mul_one]; exact h)
    exact this.symm
  have h5 : b ≠ a * b := by
    intro h
    apply ha1
    exact mul_right_cancel (a := a) (b := b) (c := 1) (by rw [one_mul]; exact h.symm)
  rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3]),
    Set.ncard_insert_of_notMem (by simp [hne, h4]),
    Set.ncard_insert_of_notMem (by simp [h5]), Set.ncard_singleton]

theorem closure_pair_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {p : G} (hp : p ∈ Subgroup.closure ({a, b} : Set G)) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hSa : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (a * y = 1 ∨ a * y = a ∨ a * y = b ∨ a * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one a))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
  have hSb : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (b * y = 1 ∨ b * y = a ∨ b * y = b ∨ b * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one b)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
  induction hp using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ hy =>
    rcases hx with rfl | rfl
    · exact hSa y hy
    · exact hSb y hy
  | inv_mul_cancel x hx y _ hy =>
    rcases hx with rfl | rfl
    · rw [hainv]
      exact hSa y hy
    · rw [hbinv]
      exact hSb y hy

theorem isFour_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : IsFour (Subgroup.closure ({a, b} : Set G)) := by
  have hel := isElemAbelian_closure_pair ha hb hab
  refine ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).2 hel, ?_⟩
  have hset : (Subgroup.closure ({a, b} : Set G) : Set G) = {1, a, b, a * b} := by
    ext x
    constructor
    · intro hx
      have := closure_pair_cases ha hb hab hx
      simpa using this
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  show Nat.card ((Subgroup.closure ({a, b} : Set G) : Set G)) = 4
  rw [Nat.card_coe_set_eq, hset]
  exact ncard_four_eq hb ha1 hb1 hne


section Fin

variable [Finite G]

theorem isPCompIn_of_le' {W W' Λ : Subgroup G} (h : IsPCompIn 2 W Λ) (hΛ : Λ ≤ W') (hW' : W' ≤ W) :
    IsPCompIn 2 W' Λ := by
  obtain ⟨-, h2⟩ := TwoThin.isPCompIn_two_iff.mp h
  exact TwoThin.isPCompIn_two_iff.mpr
    ⟨hΛ, ComponentClassification.TwoComponentTransport.restrict_nested Λ W' W hΛ hW' h2⟩

theorem mem_zStar_rigidProduct_of_involution (h44 : II4_44) (hG : IsKProperSimple G) {a : G}
    {K : Subgroup G} (hK : IsRigidRankOneComp a K) {y : G} (hyK : y ∈ K) (hy2 : orderOf y = 2) :
    y ∈ zStar (rigidProduct a) := by
  have hyX : y ∈ rigidProduct a := le_rigidProduct hK hyK
  have hcS : ∀ M, IsRigidRankOneComp a M → y ∈ cSec M := fun M hM => by
    by_cases h : K = M
    · rw [← h]
      exact rr_inv_mem_cSec h44 hG hK hyK hy2
    · exact le_cSec_of_ne (rr_pcomp hK) (rr_pcomp hM) h hyK
  refine ⟨hyX, le_normalizer hyX, TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hyX),
    fun k hk => ?_⟩
  refine commutator_mem_of_le_sSup (C := rigidProduct a) (N := pPrimeCoreOf 2 (rigidProduct a))
    (y := y) (fun g hg => TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hg))
    (S := {M | IsRigidRankOneComp a M}) (fun M hM => le_rigidProduct hM) (fun M hM m hm => ?_) k hk
  have h1 : ⁅m, y⁆ ∈ pPrimeCoreOf 2 M := (hcS M hM).2.2 m hm
  exact pPrimeCoreOf_le_of_isPCompIn
    (isPCompIn_of_le' (rr_pcomp hM) (le_rigidProduct hM) (rigidProduct_le_centralizer a)) h1

theorem one_le_pRank_of_involution' {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx2 : orderOf x = 2) :
    1 ≤ CFSG.pRank 2 ↥H := by
  rw [Bg.pRank_subgroup_eq_open]
  have hxx : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp hx2).1
  have helem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxx, one_zpow]
  exact CFSG.SectionRank.le_pRank one_lt_two ((Subgroup.zpowers_le).mpr hxH) helem
    (by rw [Nat.card_zpowers, hx2, pow_one])

theorem exists_involution_not_mem_zpowers {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    (h : 2 ≤ CFSG.pRank 2 ↥H) : ∃ i ∈ H, orderOf i = 2 ∧ i ∉ Subgroup.zpowers z := by
  rw [Bg.pRank_subgroup_eq_open] at h
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two H
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) h
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers z := by
    intro i hi
    by_contra hiz
    have hi1 : i ≠ 1 := fun h1 => hiz (by rw [h1]; exact one_mem _)
    have hi2 : orderOf i = 2 := orderOf_eq_prime (hE.2 i hi) hi1
    exact hiz (hcon i (hEH hi) hi2)
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hz] at this
  omega

theorem exists_odd_pow_isPGroup (x : G) : ∃ m : ℕ, Odd m ∧ IsPGroup 2 ↥(Subgroup.zpowers (x ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h1 : orderOf (x ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 ⟨2 ^ a, by rw [hord, mul_comm]⟩, hord, Nat.mul_div_cancel _ hm.pos]
  exact ⟨m, hm, IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, h1])⟩

end Fin

end CFSG.GH74.GLS.Bg.Pu5
