module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem d8iso_zpow_eq_of_cast_eq {G : Type} [Group G] {a : G} (ha8 : a ^ 8 = 1) {k l : ℤ}
    (h : (k : ZMod 8) = (l : ZMod 8)) : a ^ k = a ^ l := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k l 8).mp h
  have hl : l = k + 8 * m := by push_cast at hm; omega
  have h8 : a ^ (8 : ℤ) = 1 := by simpa using ha8
  rw [hl, zpow_add, zpow_mul, h8, one_zpow, mul_one]

theorem d8iso_cast_val (k : ZMod 8) : (((k.val : ℕ) : ℤ) : ZMod 8) = k := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem d8iso_conj_zpow {G : Type} [Group G] {a b : G} (hba : b * a * b⁻¹ = a⁻¹) (k : ℤ) :
    a ^ k * b = b * a ^ (-k) := by
  have h1 : b * a ^ (-k) * b⁻¹ = a ^ k := by
    rw [← conj_zpow, hba, inv_zpow', neg_neg]
  calc a ^ k * b = (b * a ^ (-k) * b⁻¹) * b := by rw [h1]
    _ = b * a ^ (-k) := by simp [mul_assoc]

@[expose] def d8iso_map {G : Type} [Group G] (a b : G) : DihedralGroup 8 → G
  | .r i => a ^ ((i.val : ℕ) : ℤ)
  | .sr i => b * a ^ ((i.val : ℕ) : ℤ)

theorem d8iso_map_mul {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (x y : DihedralGroup 8) :
    d8iso_map a b (x * y) = d8iso_map a b x * d8iso_map a b y := by
  have hc := d8iso_conj_zpow hba
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
  · simp only [DihedralGroup.r_mul_r, d8iso_map]
    rw [← zpow_add]
    apply d8iso_zpow_eq_of_cast_eq ha8
    simp only [Int.cast_add, d8iso_cast_val]
  · simp only [DihedralGroup.r_mul_sr, d8iso_map]
    rw [E1]
    congr 1
    apply d8iso_zpow_eq_of_cast_eq ha8
    simp only [Int.cast_add, Int.cast_neg, d8iso_cast_val]
    ring
  · simp only [DihedralGroup.sr_mul_r, d8iso_map]
    rw [E2]
    congr 1
    apply d8iso_zpow_eq_of_cast_eq ha8
    simp only [Int.cast_add, d8iso_cast_val]
  · simp only [DihedralGroup.sr_mul_sr, d8iso_map]
    rw [E3]
    apply d8iso_zpow_eq_of_cast_eq ha8
    simp only [Int.cast_add, Int.cast_neg, d8iso_cast_val]
    ring

@[expose] def d8iso_hom {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : DihedralGroup 8 →* G :=
  MonoidHom.mk' (d8iso_map a b) (d8iso_map_mul ha8 hb2 hba)

theorem d8iso_hom_apply {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (x : DihedralGroup 8) :
    d8iso_hom ha8 hb2 hba x = d8iso_map a b x :=
  rfl

theorem d8iso_hom_r1 {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : d8iso_hom ha8 hb2 hba (DihedralGroup.r 1) = a := by
  have hval1 : (1 : ZMod 8).val = 1 := rfl
  rw [d8iso_hom_apply]
  simp [d8iso_map, hval1]

theorem d8iso_hom_sr0 {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : d8iso_hom ha8 hb2 hba (DihedralGroup.sr 0) = b := by
  have hval0 : (0 : ZMod 8).val = 0 := ZMod.val_zero
  rw [d8iso_hom_apply]
  simp [d8iso_map, hval0]

theorem d8iso_hom_mem {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (x : DihedralGroup 8) :
    d8iso_hom ha8 hb2 hba x ∈ Subgroup.closure ({a, b} : Set G) := by
  have ha_mem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  rcases x with i | i
  · simp only [d8iso_hom_apply, d8iso_map]
    exact Subgroup.zpow_mem _ ha_mem _
  · simp only [d8iso_hom_apply, d8iso_map]
    exact Subgroup.mul_mem _ hb_mem (Subgroup.zpow_mem _ ha_mem _)

theorem d8iso_closure_eq_range {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1)
    (hb2 : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹) :
    Subgroup.closure ({a, b} : Set G) = (d8iso_hom ha8 hb2 hba).range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.r 1, d8iso_hom_r1 ha8 hb2 hba⟩
    · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 0, d8iso_hom_sr0 ha8 hb2 hba⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact d8iso_hom_mem ha8 hb2 hba x

theorem d8iso_key {G : Type} [Group G] {a : G} (hord : orderOf a = 8) {k l : ℤ}
    (h : a ^ k = a ^ l) : (k : ZMod 8) = (l : ZMod 8) := by
  have h1 : a ^ (k - l) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have h2 : ((orderOf a : ℕ) : ℤ) ∣ k - l := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hord] at h2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub k l 8]
  exact dvd_sub_comm.mp h2

theorem d8iso_hom_injective {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hord : orderOf a = 8) (hb : ∀ k : ℤ, b ≠ a ^ k) :
    Function.Injective (d8iso_hom ha8 hb2 hba) := by
  intro x y hxy
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [d8iso_hom_apply, d8iso_map] at hxy
  · have h := d8iso_key hord hxy
    rw [d8iso_cast_val, d8iso_cast_val] at h
    rw [h]
  · exfalso
    refine hb (((i.val : ℕ) : ℤ) - ((j.val : ℕ) : ℤ)) ?_
    rw [zpow_sub, hxy, mul_inv_cancel_right]
  · exfalso
    refine hb (((j.val : ℕ) : ℤ) - ((i.val : ℕ) : ℤ)) ?_
    rw [zpow_sub, ← hxy, mul_inv_cancel_right]
  · have h := d8iso_key hord (mul_left_cancel hxy)
    rw [d8iso_cast_val, d8iso_cast_val] at h
    rw [h]

theorem exists_dihedral8_equiv {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 16) :
    ∃ e : ↥(Subgroup.closure ({a, b} : Set G)) ≃* DihedralGroup 8,
      e ⟨a, Subgroup.subset_closure (by simp)⟩ = DihedralGroup.r 1 ∧
      e ⟨b, Subgroup.subset_closure (by simp)⟩ = DihedralGroup.sr 0 := by
  have hFa := d8iso_hom_r1 ha8 hb2 hba
  have hFb := d8iso_hom_sr0 ha8 hb2 hba
  have hle : Subgroup.closure ({a, b} : Set G) ≤ (d8iso_hom ha8 hb2 hba).range :=
    le_of_eq (d8iso_closure_eq_range ha8 hb2 hba)
  let F : DihedralGroup 8 →* ↥(Subgroup.closure ({a, b} : Set G)) :=
    MonoidHom.mk' (fun x => ⟨d8iso_hom ha8 hb2 hba x, d8iso_hom_mem ha8 hb2 hba x⟩)
      (fun x y => Subtype.ext (map_mul (d8iso_hom ha8 hb2 hba) x y))
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hle y.2)
    exact ⟨x, Subtype.ext hx⟩
  have hcard' : Nat.card (DihedralGroup 8) ≤ Nat.card ↥(Subgroup.closure ({a, b} : Set G)) :=
    le_of_eq (by rw [DihedralGroup.nat_card, hcard])
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le hcard'
  refine ⟨(MulEquiv.ofBijective F hbij).symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hFa.symm
  · rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hFb.symm

theorem dihedral8_of_rel {G : Type} [Group G] {a b : G} (ha8 : a ^ 8 = 1) (ha4 : a ^ 4 ≠ 1)
    (hb2 : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹) (hb : ∀ i : ℕ, b ≠ a ^ i) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 16 := by
  have hord : orderOf a = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4 : ¬ a ^ 2 ^ 2 = 1 := ha4
    have h8 : a ^ 2 ^ (2 + 1) = 1 := ha8
    simpa using orderOf_eq_prime_pow h4 h8
  have hb' : ∀ k : ℤ, b ≠ a ^ k := by
    intro k hk
    have hne : (orderOf a : ℤ) ≠ 0 := by rw [hord]; norm_num
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ k = a ^ n :=
      ⟨(k % (orderOf a : ℤ)).toNat, by
        rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k hne), zpow_mod_orderOf]⟩
    exact hb n (hk.trans hn)
  have hinj := d8iso_hom_injective ha8 hb2 hba hord hb'
  have hcardE : Nat.card ↥(d8iso_hom ha8 hb2 hba).range = Nat.card (DihedralGroup 8) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [d8iso_closure_eq_range ha8 hb2 hba, hcardE, DihedralGroup.nat_card]

end CFSG.EvenSporadicStandard.Fin76b
