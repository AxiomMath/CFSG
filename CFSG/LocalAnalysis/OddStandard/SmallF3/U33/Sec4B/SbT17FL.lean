module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

private lemma card_le_sixteen {P : Type*} [CommGroup P] [Finite P] (Y : Subgroup P)
    (φ : P →* P) (K : Subgroup P)
    (hT : Nat.card {y : P // y ∈ Y ∧ φ y = y} ≤ 4)
    (himg : ∀ x ∈ K, x ^ 2 ∈ Y ∧ φ (x ^ 2) = x ^ 2)
    (hker : ∀ x ∈ K, x ^ 2 = 1 → x ∈ Y ∧ φ x = x) :
    Nat.card K ≤ 16 := by
  let s : P →* P := powMonoidHom 2
  let f : K →* P := s.comp K.subtype
  have hcardf := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card f.range ≤ 4 := by
    have hz : ∀ z : f.range, z.1 ∈ Y ∧ φ z.1 = z.1 := by
      intro z
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp z.2
      have hfy : f y = (y.1 : P) ^ 2 := by simp [f, s]
      rw [← hy, hfy]
      exact himg y.1 y.2
    let g : f.range → {y : P // y ∈ Y ∧ φ y = y} := fun z => ⟨z.1, (hz z).1, (hz z).2⟩
    have hinj : Function.Injective g := by
      intro a b hab
      have h1 : (g a : P) = (g b : P) := congrArg Subtype.val hab
      exact Subtype.ext h1
    exact le_trans (Nat.card_le_card_of_injective _ hinj) hT
  have hker4 : Nat.card f.ker ≤ 4 := by
    have hz : ∀ z : f.ker, z.1.1 ∈ Y ∧ φ z.1.1 = z.1.1 := by
      intro z
      have hz2 : (z.1.1 : P) ^ 2 = 1 := by
        have h := MonoidHom.mem_ker.mp z.2
        simpa [f, s] using h
      exact hker z.1.1 z.1.2 hz2
    let g : f.ker → {y : P // y ∈ Y ∧ φ y = y} := fun z => ⟨z.1.1, (hz z).1, (hz z).2⟩
    have hinj : Function.Injective g := by
      intro a b hab
      have h1 : (g a : P) = (g b : P) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact le_trans (Nat.card_le_card_of_injective _ hinj) hT
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := hcardf.symm
    _ ≤ 4 * 4 := Nat.mul_le_mul hker4 hrange
    _ = 16 := by norm_num

theorem fl_abstract {P : Type*} [CommGroup P] [Finite P] (Y : Subgroup P)
    (hexp : ∀ x : P, x ^ 4 = 1) (hY : ∀ x : P, x ^ 2 = 1 → x ∈ Y) (hcard : Nat.card P = 256)
    (φ : P →* P) (hφ : ∀ x, φ (φ x) = x)
    (hcY : Nat.card {y : P // y ∈ Y ∧ φ y = y} ≤ 4) {x : P} (hx : φ x * x = 1) :
    ∃ p : P, φ p * p⁻¹ = x := by
  let β : P →* P :=
    { toFun := fun p => φ p * p⁻¹
      map_one' := by show φ 1 * 1⁻¹ = 1; simp
      map_mul' := fun p q => by
        show φ (p * q) * (p * q)⁻¹ = (φ p * p⁻¹) * (φ q * q⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  let γ : P →* P :=
    { toFun := fun x => φ x * x
      map_one' := by show φ 1 * 1 = 1; simp
      map_mul' := fun p q => by
        show φ (p * q) * (p * q) = (φ p * p) * (φ q * q)
        rw [map_mul]
        ac_rfl }
  have hγβ : ∀ p : P, γ (β p) = 1 := by
    intro p
    show φ (φ p * p⁻¹) * (φ p * p⁻¹) = 1
    rw [map_mul, map_inv, hφ]
    group
  have hC16 : Nat.card β.ker ≤ 16 := by
    apply card_le_sixteen Y φ β.ker hcY
    · intro x hxmem
      have hxC : φ x = x := by
        have h := MonoidHom.mem_ker.mp hxmem
        simp only [β, MonoidHom.coe_mk, OneHom.coe_mk] at h
        exact mul_inv_eq_one.mp h
      exact ⟨by
        apply hY
        rw [← pow_mul]
        norm_num
        exact hexp x, by rw [map_pow, hxC]⟩
    · intro x hxmem hx2
      have hxC : φ x = x := by
        have h := MonoidHom.mem_ker.mp hxmem
        simp only [β, MonoidHom.coe_mk, OneHom.coe_mk] at h
        exact mul_inv_eq_one.mp h
      exact ⟨hY x hx2, hxC⟩
  have hK16 : Nat.card γ.ker ≤ 16 := by
    apply card_le_sixteen Y φ γ.ker hcY
    · intro x hxmem
      have hxK : φ x = x⁻¹ := by
        have h := MonoidHom.mem_ker.mp hxmem
        simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk] at h
        exact eq_inv_of_mul_eq_one_left h
      have hx22 : x ^ 2 * x ^ 2 = 1 := by
        have h := hexp x
        rw [show (4:ℕ) = 2 + 2 by norm_num, pow_add] at h
        exact h
      exact ⟨by
        apply hY
        rw [← pow_mul]
        norm_num
        exact hexp x, by
          rw [map_pow, hxK, inv_pow, inv_eq_of_mul_eq_one_right hx22]⟩
    · intro x hxmem hx2
      have hxK : φ x = x⁻¹ := by
        have h := MonoidHom.mem_ker.mp hxmem
        simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk] at h
        exact eq_inv_of_mul_eq_one_left h
      refine ⟨hY x hx2, ?_⟩
      rw [hxK]
      exact (inv_eq_iff_mul_eq_one).mpr (by simpa [pow_two] using hx2)
  have hle : β.range ≤ γ.ker := by
    rintro y ⟨p, rfl⟩
    exact hγβ p
  have hrange_ge : 16 ≤ Nat.card β.range := by
    have hCpos : 0 < Nat.card β.ker := Finite.card_pos
    have hprod : Nat.card β.ker * Nat.card β.range = 256 := by
      simpa [hcard] using Subgroup.card_ker_mul_card_range β
    apply Nat.le_of_mul_le_mul_left _ hCpos
    rw [hprod]
    calc Nat.card β.ker * 16 ≤ 16 * 16 := Nat.mul_le_mul_right 16 hC16
      _ = 256 := by norm_num
  have heq : β.range = γ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (le_trans hK16 hrange_ge)
  have hxmem : x ∈ γ.ker := MonoidHom.mem_ker.mpr (by simpa [γ] using hx)
  have hxrange : x ∈ β.range := by
    rw [heq]
    exact hxmem
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hxrange
  exact ⟨p, by simpa [β] using hp⟩

theorem fl_group {G : Type*} [Group G] [Finite G] {P Y : Subgroup G}
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hexp : ∀ x ∈ P, x ^ 4 = 1)
    (hYP : Y ≤ P) (hY : ∀ x ∈ P, x ^ 2 = 1 → x ∈ Y) (hcard : Nat.card P = 256) {g : G}
    (hg2 : g * g = 1) (hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hcY : Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4) :
    ∀ x ∈ P, (g * x) * (g * x) = 1 → ∃ p ∈ P, g * x = p * g * p⁻¹ := by
  letI : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with
      mul_comm := fun a b => Subtype.ext (hPab a.1 a.2 b.1 b.2) }
  have hg_inv : g⁻¹ = g := (inv_eq_iff_mul_eq_one).mpr hg2
  let φ' : ↥P →* ↥P :=
    { toFun := fun x => ⟨g * x.1 * g⁻¹, hgP x.1 x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        show g * (a.1 * b.1) * g⁻¹ = (g * a.1 * g⁻¹) * (g * b.1 * g⁻¹)
        group }
  have hφ' : ∀ x : ↥P, φ' (φ' x) = x := by
    intro x
    ext
    show g * (g * (x : G) * g⁻¹) * g⁻¹ = (x : G)
    rw [hg_inv]
    calc g * (g * (x : G) * g) * g = (g * g) * (x : G) * (g * g) := by group
      _ = (x : G) := by rw [hg2]; simp
  have hexp' : ∀ x : ↥P, x ^ 4 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hexp x.1 x.2
  have hY' : ∀ x : ↥P, x ^ 2 = 1 → x ∈ Y.subgroupOf P := by
    intro x hx
    have hxG : (x : G) ^ 2 = 1 := by
      have h := congrArg (Subtype.val) hx
      simpa using h
    have hxY : (x : G) ∈ Y := hY x.1 x.2 hxG
    simpa [Subgroup.mem_subgroupOf] using hxY
  have hcY' : Nat.card {y : ↥P // y ∈ Y.subgroupOf P ∧ φ' y = y} ≤ 4 := by
    let gmap : {y : ↥P // y ∈ Y.subgroupOf P ∧ φ' y = y} →
        {y : G // y ∈ Y ∧ g * y = y * g} := fun y =>
      ⟨(y.1 : G),
        by
          have h := y.2.1
          simpa [Subgroup.mem_subgroupOf] using h,
        by
          have h := congrArg Subtype.val y.2.2
          show g * (y.1 : G) = (y.1 : G) * g
          simp only [φ', MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk] at h
          exact (mul_inv_eq_iff_eq_mul).mp h⟩
    have hinj : Function.Injective gmap := by
      intro a b hab
      have h1 : (gmap a : G) = (gmap b : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact le_trans (Nat.card_le_card_of_injective _ hinj) hcY
  intro x hxP hx2
  have hx' : φ' ⟨x, hxP⟩ * ⟨x, hxP⟩ = 1 := by
    apply Subtype.ext
    show g * x * g⁻¹ * x = 1
    rw [hg_inv]
    simpa [mul_assoc] using hx2
  obtain ⟨p, hp⟩ := fl_abstract (Y.subgroupOf P) hexp' hY' hcard φ' hφ' hcY' hx'
  have hpG : (g * (p : G) * g⁻¹) * (p : G)⁻¹ = x := by
    have h := congrArg Subtype.val hp
    simpa [φ', mul_assoc] using h
  refine ⟨(p : G), p.2, ?_⟩
  rw [← hpG]
  calc g * (g * (p : G) * g⁻¹ * (p : G)⁻¹)
      = (g * g) * ((p : G) * g⁻¹ * (p : G)⁻¹) := by group
    _ = (p : G) * g⁻¹ * (p : G)⁻¹ := by rw [hg2, one_mul]
    _ = (p : G) * g * (p : G)⁻¹ := by rw [hg_inv]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
