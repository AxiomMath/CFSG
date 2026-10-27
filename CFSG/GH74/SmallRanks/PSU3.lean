module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.GH74.SmallRanks

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg

theorem wreath_sq_eq_one {X : Type*} [Group X] {s t : X}
    (hcomm : Commute s t) (hs : orderOf s = 4) (ht : orderOf t = 4)
    (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥) (i j : ℤ)
    (h : (s ^ i * t ^ j) ^ 2 = 1) :
    s ^ i * t ^ j = 1 ∨ s ^ i * t ^ j = s ^ 2 ∨ s ^ i * t ^ j = t ^ 2 ∨
      s ^ i * t ^ j = s ^ 2 * t ^ 2 := by
  have hc : s ^ i * t ^ j = t ^ j * s ^ i := (hcomm.zpow_zpow i j).eq
  have h' : s ^ (2 * i) * t ^ (2 * j) = 1 := by
    have : (s ^ i * t ^ j) ^ 2 = s ^ (2 * i) * t ^ (2 * j) := by
      rw [sq, mul_assoc, ← mul_assoc (t ^ j), ← hc, mul_assoc, ← mul_assoc, ← zpow_add,
        ← zpow_add]
      congr 2 <;> ring
    rw [← this]
    exact h
  have h1 : s ^ (2 * i) = 1 := by
    have : s ^ (2 * i) = t ^ (-(2 * j)) := by
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_left h'
    have hm : s ^ (2 * i) ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
      ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) _,
        this ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) _⟩
    rw [hinter, Subgroup.mem_bot] at hm
    exact hm
  have h2 : t ^ (2 * j) = 1 := by
    rw [h1, one_mul] at h'
    exact h'
  have hi : (4 : ℤ) ∣ 2 * i := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hs] at this
    exact_mod_cast this
  have hj : (4 : ℤ) ∣ 2 * j := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [ht] at this
    exact_mod_cast this
  have hsi : s ^ i = 1 ∨ s ^ i = s ^ 2 := by
    have := zpow_mod_orderOf s i
    rw [hs] at this
    have h4 : i % 4 = 0 ∨ i % 4 = 2 := by omega
    rcases h4 with h4 | h4
    · left
      rw [← this]
      simp only [Nat.cast_ofNat, h4, zpow_zero]
    · right
      rw [← this]
      simp only [Nat.cast_ofNat, h4]
      norm_cast
  have htj : t ^ j = 1 ∨ t ^ j = t ^ 2 := by
    have := zpow_mod_orderOf t j
    rw [ht] at this
    have h4 : j % 4 = 0 ∨ j % 4 = 2 := by omega
    rcases h4 with h4 | h4
    · left
      rw [← this]
      simp only [Nat.cast_ofNat, h4, zpow_zero]
    · right
      rw [← this]
      simp only [Nat.cast_ofNat, h4]
      norm_cast
  rcases hsi with hsi | hsi <;> rcases htj with htj | htj <;> rw [hsi, htj] <;> simp

theorem wreath_conj_sq {X : Type*} [Group X] {s t w : X}
    (hcomm : Commute s t) (hws : w⁻¹ * s * w = t) (hwt : w⁻¹ * t * w = s) (hw2 : w ^ 2 = 1)
    (a b : ℤ) :
    (s ^ a * t ^ b * w) * s ^ 2 * (s ^ a * t ^ b * w)⁻¹ = t ^ 2 ∧
    (s ^ a * t ^ b * w) * t ^ 2 * (s ^ a * t ^ b * w)⁻¹ = s ^ 2 := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq, hw2])
  have h1 : w * s * w⁻¹ = t := by
    rw [hwinv]
    rw [hwinv] at hws
    exact hws
  have h1' : w * t * w⁻¹ = s := by
    rw [hwinv]
    rw [hwinv] at hwt
    exact hwt
  have h2 : w * s ^ 2 * w⁻¹ = t ^ 2 := by rw [← h1, conj_pow]
  have h2' : w * t ^ 2 * w⁻¹ = s ^ 2 := by rw [← h1', conj_pow]
  have hcs : Commute (s ^ a * t ^ b) (s ^ 2) :=
    (((Commute.refl s).zpow_left a).pow_right 2).mul_left ((hcomm.symm.zpow_left b).pow_right 2)
  have hct : Commute (s ^ a * t ^ b) (t ^ 2) :=
    ((hcomm.zpow_left a).pow_right 2).mul_left (((Commute.refl t).zpow_left b).pow_right 2)
  constructor
  · calc (s ^ a * t ^ b * w) * s ^ 2 * (s ^ a * t ^ b * w)⁻¹
        = (s ^ a * t ^ b) * (w * s ^ 2 * w⁻¹) * (s ^ a * t ^ b)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = (s ^ a * t ^ b) * t ^ 2 * (s ^ a * t ^ b)⁻¹ := by rw [h2]
      _ = t ^ 2 := by rw [hct.eq, mul_inv_cancel_right]
  · calc (s ^ a * t ^ b * w) * t ^ 2 * (s ^ a * t ^ b * w)⁻¹
        = (s ^ a * t ^ b) * (w * t ^ 2 * w⁻¹) * (s ^ a * t ^ b)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = (s ^ a * t ^ b) * s ^ 2 * (s ^ a * t ^ b)⁻¹ := by rw [h2']
      _ = s ^ 2 := by rw [hcs.eq, mul_inv_cancel_right]

theorem wreath_inv_mul {X : Type*} [Group X] {s t w : X}
    (hcomm : Commute s t) (hws : w⁻¹ * s * w = t) (hwt : w⁻¹ * t * w = s)
    (a b c d : ℤ) :
    ∃ i j : ℤ, (s ^ a * t ^ b * w)⁻¹ * (s ^ c * t ^ d * w) = s ^ i * t ^ j := by
  have hk1 : ∀ k : ℤ, w⁻¹ * s ^ k * w = t ^ k := fun k => by
    have h : (w⁻¹ * s * w⁻¹⁻¹) ^ k = w⁻¹ * s ^ k * w⁻¹⁻¹ := conj_zpow
    rw [inv_inv, hws] at h
    exact h.symm
  have hk2 : ∀ k : ℤ, w⁻¹ * t ^ k * w = s ^ k := fun k => by
    have h : (w⁻¹ * t * w⁻¹⁻¹) ^ k = w⁻¹ * t ^ k * w⁻¹⁻¹ := conj_zpow
    rw [inv_inv, hwt] at h
    exact h.symm
  refine ⟨d - b, c - a, ?_⟩
  have e1 : (s ^ a * t ^ b * w)⁻¹ * (s ^ c * t ^ d * w) =
      w⁻¹ * (t ^ (-b) * (s ^ (-a) * s ^ c) * t ^ d) * w := by
    simp only [mul_inv_rev, ← zpow_neg, mul_assoc]
  have e2 : t ^ (-b) * (s ^ (-a) * s ^ c) * t ^ d = s ^ (c - a) * t ^ (d - b) := by
    have h1 : s ^ (-a) * s ^ c = s ^ (c - a) := by
      rw [← zpow_add]
      congr 1
      ring
    have hcm : t ^ (-b) * s ^ (c - a) = s ^ (c - a) * t ^ (-b) :=
      (hcomm.zpow_zpow (c - a) (-b)).eq.symm
    rw [h1, hcm, mul_assoc, ← zpow_add]
    congr 2
    ring
  rw [e1, e2]
  have e3 : w⁻¹ * (s ^ (c - a) * t ^ (d - b)) * w =
      (w⁻¹ * s ^ (c - a) * w) * (w⁻¹ * t ^ (d - b) * w) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e3, hk1, hk2]
  exact (hcomm.zpow_zpow (d - b) (c - a)).eq.symm

theorem card_le_four_of_wreath {X : Type*} [Group X] {s t w : X}
    (hst : s * t = t * s) (hws : w⁻¹ * s * w = t) (hwt : w⁻¹ * t * w = s) (hw2 : w ^ 2 = 1)
    (hs : orderOf s = 4) (ht : orderOf t = 4)
    (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥)
    {E : Subgroup X} (hES : E ≤ Subgroup.closure {s, t, w}) (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 4 := by
  classical
  have hcomm : Commute s t := hst
  have hs2 : s ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hs]; norm_num)
  have hst2 : s ^ 2 ≠ t ^ 2 := by
    intro h
    have hm : s ^ 2 ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
      ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 2,
        h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers t) 2⟩
    rw [hinter, Subgroup.mem_bot] at hm
    exact hs2 hm
  have hsplit : ∀ g ∈ Subgroup.closure {s, t, w},
      (∃ i j : ℤ, g = s ^ i * t ^ j) ∨ (∃ i j : ℤ, g = s ^ i * t ^ j * w) := by
    intro g hg
    obtain ⟨i, j, e, he, rfl⟩ := exists_zpow_mul_zpow_mul_pow hcomm hws.symm hw2 hg
    interval_cases e
    · left
      exact ⟨i, j, by simp⟩
    · right
      exact ⟨i, j, by simp⟩
  have hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1
    have := mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hcard : ∀ a b c d : X, (E : Set X) ⊆ {a, b, c, d} → Nat.card E ≤ 4 := by
    intro a b c d h
    calc Nat.card E = Set.ncard (E : Set X) := Nat.card_coe_set_eq (E : Set X)
      _ ≤ Set.ncard ({a, b, c, d} : Set X) := Set.ncard_le_ncard h (Set.toFinite _)
      _ ≤ 4 := by
        have : ({a, b, c, d} : Set X) = ↑({a, b, c, d} : Finset X) := by simp
        rw [this, Set.ncard_coe_finset]
        exact Finset.card_le_four
  have hP : ∀ y ∈ E, (∃ i j : ℤ, y = s ^ i * t ^ j) →
      y = 1 ∨ y = s ^ 2 ∨ y = t ^ 2 ∨ y = s ^ 2 * t ^ 2 := by
    rintro y hy ⟨i, j, rfl⟩
    exact wreath_sq_eq_one hcomm hs ht hinter i j (hE.2 _ hy)
  by_cases hcase : ∃ g₀ ∈ E, ∀ i j : ℤ, g₀ ≠ s ^ i * t ^ j
  · obtain ⟨g₀, hg₀E, hg₀P⟩ := hcase
    obtain ⟨a, b, hg₀⟩ : ∃ a b : ℤ, g₀ = s ^ a * t ^ b * w := by
      rcases hsplit g₀ (hES hg₀E) with ⟨i, j, h⟩ | h
      · exact absurd h (hg₀P i j)
      · exact h
    obtain ⟨hK2s, hK2t⟩ := wreath_conj_sq hcomm hws hwt hw2 a b
    rw [← hg₀] at hK2s hK2t
    have hP' : ∀ y ∈ E, (∃ i j : ℤ, y = s ^ i * t ^ j) → y = 1 ∨ y = s ^ 2 * t ^ 2 := by
      intro y hy hyP
      rcases hP y hy hyP with h | h | h | h
      · exact Or.inl h
      · exfalso
        have := hab g₀ hg₀E y hy
        rw [h] at this
        have h2 : g₀ * s ^ 2 * g₀⁻¹ = s ^ 2 := by rw [this, mul_inv_cancel_right]
        exact hst2 (h2.symm.trans hK2s)
      · exfalso
        have := hab g₀ hg₀E y hy
        rw [h] at this
        have h2 : g₀ * t ^ 2 * g₀⁻¹ = t ^ 2 := by rw [this, mul_inv_cancel_right]
        exact hst2 (hK2t.symm.trans h2)
      · exact Or.inr h
    apply hcard 1 (s ^ 2 * t ^ 2) g₀ (g₀ * (s ^ 2 * t ^ 2))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hsplit x (hES hx) with hxP | ⟨c, d, hxQ⟩
    · rcases hP' x hx hxP with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨i, j, hij⟩ := wreath_inv_mul hcomm hws hwt a b c d
      rw [← hg₀, ← hxQ] at hij
      have hyE : g₀⁻¹ * x ∈ E := E.mul_mem (E.inv_mem hg₀E) hx
      rcases hP' _ hyE ⟨i, j, hij⟩ with h | h
      · right
        right
        left
        rw [inv_mul_eq_one] at h
        exact h.symm
      · right
        right
        right
        rw [inv_mul_eq_iff_eq_mul] at h
        exact h
  · push Not at hcase
    apply hcard 1 (s ^ 2) (t ^ 2) (s ^ 2 * t ^ 2)
    intro x hx
    obtain ⟨i, j, hij⟩ := hcase x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hP x hx ⟨i, j, hij⟩

theorem twoRank_le_two_of_statedClassicalModel_PSU_three_three {G : Type} [Group G] [Finite G]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 3 1) : CFSG.Open.twoRank G ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have hbot := CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hK9
  let e2 : StatedProj (StatedSU 3 3 K) ≃* StatedSU 3 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have e1 : G ≃* StatedSU 3 3 K := e.trans e2
  have : Finite (StatedSU 3 3 K) := Finite.of_equiv G e1.toEquiv
  rw [twoRank_eq_of_mulEquiv e1]
  obtain ⟨i, hi⟩ := CFSG.LinearGroups.UnitaryThreeOverNine.exists_units_orderOf_eq_four hK9
  obtain ⟨⟨s, t, w, hs, ht, hw⟩, hall⟩ :=
    CFSG.LinearGroups.UnitaryThreeOverNine.wreath_sylow_model hK9 i hi
  obtain ⟨hst, hs4, ht4, hinter, hw2, -, hws, hwt, -, ⟨P, hP⟩, -⟩ := hall s t w hs ht hw
  have hw2' : w ^ 2 = 1 := by
    rw [← hw2]
    exact pow_orderOf_eq_one w
  refine twoRank_le_of_sylow P (r := 2) (fun E hEP hE => ?_)
  rw [hP] at hEP
  simpa using card_le_four_of_wreath hst hws hwt hw2' hs4 ht4 hinter hEP hE

theorem twoRank_le_two_of_statedClassicalModel_PSU_three_four {G : Type} [Group G] [Finite G]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2) : CFSG.Open.twoRank G ≤ 2 := by
  obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := CFSG.RankTwoShapes.nonempty_sylow_equiv_unitaryFourW h U (GaloisField 2 4) hK
  have hfin : Finite (CFSG.RankTwoShapes.unitaryFourW (GaloisField 2 4) hK) :=
    CFSG.RankTwoShapes.UnitaryFourW.finite_unitaryFourW
  refine twoRank_le_of_sylow U (r := 2) (fun E hEU hE => ?_)
  have key : ∀ x : E, e ⟨x.1, hEU x.2⟩ ∈
      (CFSG.RankTwoShapes.UnitaryFourW.firstCoord hK).ker := by
    intro x
    have hx2 : (⟨x.1, hEU x.2⟩ : ↥(U : Subgroup G)) ^ 2 = 1 := Subtype.ext (hE.2 x.1 x.2)
    have hw2 : (e ⟨x.1, hEU x.2⟩) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    have h1 := CFSG.RankTwoShapes.UnitaryFourW.snd_sq (e ⟨x.1, hEU x.2⟩)
    rw [hw2, CFSG.RankTwoShapes.UnitaryFourW.snd_one] at h1
    exact CFSG.RankTwoShapes.UnitaryFourW.mem_ker_firstCoord.mpr
      ((pow_eq_zero_iff (by norm_num)).mp h1.symm)
  have hle : Nat.card E ≤ Nat.card (CFSG.RankTwoShapes.UnitaryFourW.firstCoord hK).ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨e ⟨x.1, hEU x.2⟩, key x⟩) ?_
    intro x y hxy
    have h1 := e.injective (congrArg Subtype.val hxy)
    exact Subtype.ext (Subtype.mk.inj h1)
  rw [CFSG.RankTwoShapes.UnitaryFourW.natCard_ker_firstCoord] at hle
  simpa using hle

end CFSG.GH74.SmallRanks
