module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C]

private theorem zpowers_mul_comm {z : C} (hzc : ∀ c : C, c * z = z * c) {x : C}
    (hx : x ∈ zpowers z) (y : C) : x * y = y * x := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hn]
  exact (Commute.zpow_left (show Commute z y from (hzc y).symm) n).eq

theorem N_le_of_normal_of_center {z : C} (hz2 : z ^ 2 = 1) (hzne : z ≠ 1) {R W : Subgroup C}
    (hR2 : IsPGroup 2 ↥R) (hzR : z ∈ R)
    (hcen : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x ∈ zpowers z) (hW : W ≤ R)
    (hWn : ∀ r ∈ R, ∀ w ∈ W, r * w * r⁻¹ ∈ W) (hWne : W ≠ ⊥) : z ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  have hW2 : IsPGroup 2 ↥W := hR2.to_le hW
  have hWdvd : 2 ∣ Nat.card ↥W := by
    obtain ⟨n, hn, hcard⟩ := hW2.nontrivial_iff_card.mp hWnt
    rw [hcard]
    exact dvd_pow_self 2 (ne_of_gt hn)
  have hWnorm : R ≤ normalizer (W : Set C) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hWn r hr w
    · intro hw
      have h := hWn r⁻¹ (R.inv_mem hr) (r * w * r⁻¹) hw
      have he : r⁻¹ * (r * w * r⁻¹) * (r⁻¹)⁻¹ = w := by group
      rwa [he] at h
  letI := Subgroup.conjMulDistribMulActionOfLeNormalizer R W hWnorm
  have hsmul : ∀ (r : ↥R) (k : ↥W),
      ((r • k : ↥W) : C) = (r : C) * (k : C) * (r : C)⁻¹ := fun r k =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R W hWnorm r k
  have h1fix : (1 : ↥W) ∈ MulAction.fixedPoints ↥R ↥W := by
    rw [MulAction.mem_fixedPoints]
    intro r
    apply Subtype.ext
    rw [hsmul]
    simp
  obtain ⟨w, hwfix, hwne1⟩ :=
    hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W hWdvd h1fix
  have hwR : (w : C) ∈ R := hW w.2
  have hwcen : ∀ y ∈ R, (w : C) * y = y * (w : C) := by
    intro y hy
    have hrfix : (⟨y, hy⟩ : ↥R) • w = w := (MulAction.mem_fixedPoints.mp hwfix) ⟨y, hy⟩
    have hval : y * (w : C) * y⁻¹ = (w : C) := by
      have h := congrArg Subtype.val hrfix
      rw [hsmul] at h
      simpa using h
    have hyw : y * (w : C) = (w : C) * y := by
      calc y * (w : C) = (y * (w : C) * y⁻¹) * y := by group
        _ = (w : C) * y := by rw [hval]
    exact hyw.symm
  have hwz : (w : C) ∈ zpowers z := hcen (w : C) hwR hwcen
  have hwCne : (w : C) ≠ 1 := by
    intro h
    exact hwne1 (Subtype.ext h).symm
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hzne
  have hwdvd : orderOf (w : C) ∣ 2 := by
    rw [← hzord]
    exact orderOf_dvd_of_mem_zpowers hwz
  have hword : orderOf (w : C) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hwdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hwCne
    · exact h2
  have hle : zpowers (w : C) ≤ zpowers z := Subgroup.zpowers_le.mpr hwz
  have hcard : Nat.card (zpowers z) ≤ Nat.card (zpowers (w : C)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hword]
  have heq : zpowers (w : C) = zpowers z := Subgroup.eq_of_le_of_card_ge hle hcard
  have hzmem : z ∈ zpowers (w : C) := by
    rw [heq]
    exact Subgroup.mem_zpowers z
  exact (Subgroup.zpowers_le.mpr w.2) hzmem

theorem exists_perfect_cover {z : C} (hzc : ∀ c : C, c * z = z * c) (hz2 : z ^ 2 = 1)
    (hzne : z ≠ 1) {P : Subgroup C} (hzP : z ∈ P) (hperf : ⁅P, P⁆ ⊔ zpowers z = P) :
    ∃ L : Subgroup C, L ≤ P ∧ ⁅L, L⁆ = L ∧ L ⊔ zpowers z = P := by
  classical
  set H : Subgroup C := zpowers z with hH
  haveI : H.Normal := Subgroup.normal_of_le_center (by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    rw [hH] at hx
    exact (zpowers_mul_comm hzc hx y).symm)
  let S : Set ℕ := {n | ∃ L : Subgroup C, L ≤ P ∧ L ⊔ H = P ∧ Nat.card L = n}
  have hS : ∃ n, n ∈ S := by
    refine ⟨Nat.card P, P, le_rfl, ?_, rfl⟩
    rw [sup_eq_left, hH]
    exact Subgroup.zpowers_le.mpr hzP
  obtain ⟨L, hLP, hLz, hLcard⟩ := Nat.find_spec hS
  have hcomm_ge : ⁅L, L⁆ ≤ ⁅L ⊔ H, L ⊔ H⁆ :=
    Subgroup.commutator_mono le_sup_left le_sup_left
  have hcomm_le : ⁅L ⊔ H, L ⊔ H⁆ ≤ ⁅L, L⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_sup_of_normal_right] at ha hb
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := ha
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hb
    have ha2c : ∀ y : C, a2 * y = y * a2 := fun y => zpowers_mul_comm hzc ha2 y
    have hb2c : ∀ y : C, b2 * y = y * b2 := fun y => zpowers_mul_comm hzc hb2 y
    have h1 : (commutatorElement : Bracket C C).bracket a2 (b1 * b2) = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (ha2c (b1 * b2))
    have h2 : (commutatorElement : Bracket C C).bracket a1 b2 = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hb2c a1).symm
    rw [commutatorElement_mul_left_eq_conj_mul, h1,
      commutatorElement_mul_right_eq_mul_conj, h2]
    simpa using Subgroup.commutator_mem_commutator ha1 hb1
  have hcomm_eq : ⁅L ⊔ H, L ⊔ H⁆ = ⁅L, L⁆ := le_antisymm hcomm_le hcomm_ge
  have hPL : ⁅P, P⁆ = ⁅L, L⁆ := by
    rw [← hLz]
    exact hcomm_eq
  have hLsupH : ⁅L, L⁆ ⊔ H = P := by rw [← hPL, hperf]
  have hcard : Nat.card L ≤ Nat.card ↥(⁅L, L⁆ : Subgroup C) := by
    have hmem : Nat.card ↥(⁅L, L⁆ : Subgroup C) ∈ S :=
      ⟨⁅L, L⁆, (Subgroup.commutator_le_self L).trans hLP, hLsupH, rfl⟩
    rw [hLcard]
    exact Nat.find_min' hS hmem
  refine ⟨L, hLP, ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge (Subgroup.commutator_le_self L) hcard
  · exact hLz

theorem z_mem_of_perfect_cover {z : C} (hzc : ∀ c : C, c * z = z * c) (hz2 : z ^ 2 = 1)
    (hzne : z ≠ 1) {P R L : Subgroup C} (hRP : R ≤ P) (hzR : z ∈ R) (hR2 : IsPGroup 2 ↥R)
    (hRcard : 2 < Nat.card ↥R)
    (hcen : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x ∈ zpowers z) (hLP : L ≤ P)
    (hLz : L ⊔ zpowers z = P) : z ∈ L := by
  haveI : (zpowers z).Normal := Subgroup.normal_of_le_center (by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact (zpowers_mul_comm hzc hx y).symm)
  by_contra hzL
  have hWne : R ⊓ L ≠ ⊥ := by
    intro hbot
    have hzcard : Nat.card (zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hzne]
    have hzlt : zpowers z < R := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hzR) ?_
      intro heq
      rw [← heq, hzcard] at hRcard
      exact absurd hRcard (lt_irrefl 2)
    obtain ⟨r, hrR, hrH⟩ := SetLike.exists_of_lt hzlt
    have hrP : r ∈ L ⊔ zpowers z := by
      rw [hLz]
      exact hRP hrR
    rw [Subgroup.mem_sup_of_normal_right] at hrP
    obtain ⟨l, hlL, h, hhH, hlh⟩ := hrP
    have hhR : h ∈ R := Subgroup.zpowers_le.mpr hzR hhH
    have hlR : l ∈ R := by
      have hleq : l = r * h⁻¹ := by rw [← hlh]; group
      rw [hleq]
      exact R.mul_mem hrR (R.inv_mem hhR)
    have hl1 : l ≠ 1 := by
      intro hl
      apply hrH
      rw [← hlh, hl, one_mul]
      exact hhH
    have hlbot : l ∈ (⊥ : Subgroup C) := by
      rw [← hbot]
      exact ⟨hlR, hlL⟩
    exact hl1 (Subgroup.mem_bot.mp hlbot)
  have hWn : ∀ r ∈ R, ∀ w ∈ R ⊓ L, r * w * r⁻¹ ∈ R ⊓ L := by
    intro r hr w hw
    refine ⟨R.mul_mem (R.mul_mem hr hw.1) (R.inv_mem hr), ?_⟩
    have hrP : r ∈ L ⊔ zpowers z := by
      rw [hLz]
      exact hRP hr
    rw [Subgroup.mem_sup_of_normal_right] at hrP
    obtain ⟨l, hlL, h, hhH, hlh⟩ := hrP
    have hhw : h * (w : C) * h⁻¹ = (w : C) := by
      have hc : h * (w : C) = (w : C) * h := zpowers_mul_comm hzc hhH (w : C)
      rw [hc, mul_inv_cancel_right]
    rw [← hlh]
    rw [show (l * h) * (w : C) * (l * h)⁻¹ = l * (h * (w : C) * h⁻¹) * l⁻¹ by group]
    rw [hhw]
    exact L.mul_mem (L.mul_mem hlL hw.2) (L.inv_mem hlL)
  have hzW : z ∈ R ⊓ L :=
    N_le_of_normal_of_center hz2 hzne hR2 hzR hcen (inf_le_left : R ⊓ L ≤ R) hWn hWne
  exact hzL hzW.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
