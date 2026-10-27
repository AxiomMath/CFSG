module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem d4iso_zpow_eq_of_cast_eq {G : Type} [Group G] {a : G} (ha4 : a ^ 4 = 1) {k l : ℤ}
    (h : (k : ZMod 4) = (l : ZMod 4)) : a ^ k = a ^ l := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k l 4).mp h
  have hl : l = k + 4 * m := by push_cast at hm; omega
  have h4 : a ^ (4 : ℤ) = 1 := by simpa using ha4
  rw [hl, zpow_add, zpow_mul, h4, one_zpow, mul_one]

theorem d4iso_cast_val (k : ZMod 4) : (((k.val : ℕ) : ℤ) : ZMod 4) = k := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem d4iso_conj_zpow {G : Type} [Group G] {a b : G} (hba : b * a * b⁻¹ = a⁻¹) (k : ℤ) :
    a ^ k * b = b * a ^ (-k) := by
  have h1 : b * a ^ (-k) * b⁻¹ = a ^ k := by
    rw [← conj_zpow, hba, inv_zpow', neg_neg]
  calc a ^ k * b = (b * a ^ (-k) * b⁻¹) * b := by rw [h1]
    _ = b * a ^ (-k) := by simp [mul_assoc]

@[expose] def d4iso_map {G : Type} [Group G] (a b : G) : DihedralGroup 4 → G
  | .r i => a ^ ((i.val : ℕ) : ℤ)
  | .sr i => b * a ^ ((i.val : ℕ) : ℤ)

theorem d4iso_map_mul {G : Type} [Group G] {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (x y : DihedralGroup 4) :
    d4iso_map a b (x * y) = d4iso_map a b x * d4iso_map a b y := by
  have hc := d4iso_conj_zpow hba
  have E1 : ∀ p q : ℤ, a ^ p * (b * a ^ q) = b * a ^ (-p + q) := by
    intro p q
    rw [← mul_assoc, hc p, mul_assoc, ← zpow_add]
  have E2 : ∀ p q : ℤ, b * a ^ p * a ^ q = b * a ^ (p + q) := by
    intro p q
    rw [mul_assoc, ← zpow_add]
  have E3 : ∀ p q : ℤ, b * a ^ p * (b * a ^ q) = a ^ (-p + q) := by
    intro p q
    rw [mul_assoc, E1, ← mul_assoc, hb2, one_mul]
  rcases x with i | i <;> rcases y with j | j
  · simp only [DihedralGroup.r_mul_r, d4iso_map]
    rw [← zpow_add]
    apply d4iso_zpow_eq_of_cast_eq ha4
    simp only [Int.cast_add, d4iso_cast_val]
  · simp only [DihedralGroup.r_mul_sr, d4iso_map]
    rw [E1]
    congr 1
    apply d4iso_zpow_eq_of_cast_eq ha4
    simp only [Int.cast_add, Int.cast_neg, d4iso_cast_val]
    ring
  · simp only [DihedralGroup.sr_mul_r, d4iso_map]
    rw [E2]
    congr 1
    apply d4iso_zpow_eq_of_cast_eq ha4
    simp only [Int.cast_add, d4iso_cast_val]
  · simp only [DihedralGroup.sr_mul_sr, d4iso_map]
    rw [E3]
    apply d4iso_zpow_eq_of_cast_eq ha4
    simp only [Int.cast_add, Int.cast_neg, d4iso_cast_val]
    ring

@[expose] def d4iso_hom {G : Type} [Group G] {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : DihedralGroup 4 →* G :=
  MonoidHom.mk' (d4iso_map a b) (d4iso_map_mul ha4 hb2 hba)

theorem d4iso_hom_apply {G : Type} [Group G] {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (x : DihedralGroup 4) :
    d4iso_hom ha4 hb2 hba x = d4iso_map a b x :=
  rfl

theorem exists_dihedral4_equiv {G : Type} [Group G] {a b : G} (ha4 : a ^ 4 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 8) :
    ∃ e : ↥(Subgroup.closure ({a, b} : Set G)) ≃* DihedralGroup 4,
      e ⟨a, Subgroup.subset_closure (by simp)⟩ = DihedralGroup.r 1 ∧
      e ⟨b, Subgroup.subset_closure (by simp)⟩ = DihedralGroup.sr 0 := by
  have ha_mem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hval1 : (1 : ZMod 4).val = 1 := rfl
  have hval0 : (0 : ZMod 4).val = 0 := ZMod.val_zero
  have hFa : d4iso_hom ha4 hb2 hba (DihedralGroup.r 1) = a := by
    rw [d4iso_hom_apply]
    simp [d4iso_map, hval1]
  have hFb : d4iso_hom ha4 hb2 hba (DihedralGroup.sr 0) = b := by
    rw [d4iso_hom_apply]
    simp [d4iso_map, hval0]
  have hmem : ∀ x : DihedralGroup 4,
      d4iso_hom ha4 hb2 hba x ∈ Subgroup.closure ({a, b} : Set G) := by
    intro x
    rcases x with i | i
    · simp only [d4iso_hom_apply, d4iso_map]
      exact Subgroup.zpow_mem _ ha_mem _
    · simp only [d4iso_hom_apply, d4iso_map]
      exact Subgroup.mul_mem _ hb_mem (Subgroup.zpow_mem _ ha_mem _)
  have hle : Subgroup.closure ({a, b} : Set G) ≤ (d4iso_hom ha4 hb2 hba).range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.r 1, hFa⟩
    · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 0, hFb⟩
  let F : DihedralGroup 4 →* ↥(Subgroup.closure ({a, b} : Set G)) :=
    MonoidHom.mk' (fun x => ⟨d4iso_hom ha4 hb2 hba x, hmem x⟩)
      (fun x y => Subtype.ext (map_mul (d4iso_hom ha4 hb2 hba) x y))
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hle y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hcard' : Nat.card (DihedralGroup 4) ≤ Nat.card ↥(Subgroup.closure ({a, b} : Set G)) :=
    le_of_eq (by rw [DihedralGroup.nat_card, hcard])
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le hcard'
  refine ⟨(MulEquiv.ofBijective F hbij).symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hFa.symm
  · rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hFb.symm

end CFSG.EvenSporadicStandard.Fin76b
