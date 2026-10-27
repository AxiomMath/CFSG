module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

section Dihedral

variable {m : ℕ}

theorem zmod_eq_zero_of_two_pow_mul_eq_zero (hm : Odd m) {k : ℕ} {j : ZMod m}
    (h : (2 : ZMod m) ^ k * j = 0) : j = 0 := by
  have hu : IsUnit ((2 : ZMod m) ^ k) := by
    refine IsUnit.pow k ?_
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hm)).isUnit
    simpa using this
  exact hu.mul_right_eq_zero.mp h

theorem dihedral_eq_one_of_two_pow_eq_one_r (hm : Odd m) {i : ZMod m} {k : ℕ}
    (h : (DihedralGroup.r i) ^ (2 ^ k) = 1) : i = 0 := by
  rw [DihedralGroup.r_pow, DihedralGroup.one_def] at h
  have h1 : i * ((2 ^ k : ℕ) : ZMod m) = 0 := DihedralGroup.r.inj h
  apply zmod_eq_zero_of_two_pow_mul_eq_zero hm (k := k)
  rw [mul_comm]
  simpa using h1

theorem dihedral_pow_eq_one_or_sq_eq_one (g : DihedralGroup m) : g ^ m = 1 ∨ g ^ 2 = 1 := by
  rcases g with i | i
  · left
    rw [DihedralGroup.r_pow, DihedralGroup.one_def]
    congr 1
    simp
  · right
    rw [sq, DihedralGroup.sr_mul_self]

theorem dihedral_eq_one_or_eq_one_of_commutator (hm : Odd m) {g h : DihedralGroup m}
    {a b c : ℕ} (hg : g ^ (2 ^ a) = 1) (hh : h ^ b = 1) (hb : Odd b)
    (hc : ⁅g, h⁆ ^ (2 ^ c) = 1) : g = 1 ∨ h = 1 := by
  rcases g with i | i
  · left
    rw [dihedral_eq_one_of_two_pow_eq_one_r hm hg, DihedralGroup.r_zero]
  · rcases h with j | j
    · right
      have e : ⁅DihedralGroup.sr i, DihedralGroup.r j⁆ = DihedralGroup.r (-j - j) := by
        simp only [commutatorElement_def, DihedralGroup.sr_mul_r, DihedralGroup.inv_sr,
          DihedralGroup.sr_mul_sr, DihedralGroup.inv_r, DihedralGroup.r_mul_r]
        congr 1
        ring
      rw [e] at hc
      have h1 := dihedral_eq_one_of_two_pow_eq_one_r hm hc
      have h2 : (2 : ZMod m) ^ 1 * j = 0 := by
        rw [pow_one]
        linear_combination (-1 : ZMod m) * h1
      rw [zmod_eq_zero_of_two_pow_mul_eq_zero hm h2, DihedralGroup.r_zero]
    · exfalso
      have h1 : orderOf (DihedralGroup.sr j) ∣ b := orderOf_dvd_of_pow_eq_one hh
      rw [DihedralGroup.orderOf_sr] at h1
      exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr h1)

end Dihedral

section Complement

variable {X : Type*} [Group X]

theorem exists_proj_of_complement {N D Y : Subgroup X} (hinf : N ⊓ D = ⊥) (hsup : N ⊔ D = Y)
    (hnorm : (N.subgroupOf Y).Normal) :
    ∃ π : Y →* D, (∀ y : Y, ∃ n ∈ N, (y : X) = (π y : X) * n) ∧
      ∀ y : Y, π y = 1 ↔ (y : X) ∈ N := by
  have hDY : D ≤ Y := hsup ▸ le_sup_right
  have hNY : N ≤ Y := hsup ▸ le_sup_left
  set N' := N.subgroupOf Y with hN'
  set φ : D →* Y ⧸ N' := (QuotientGroup.mk' N').comp (inclusion hDY) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN',
      mem_subgroupOf, coe_inclusion] at hd
    have h1 : (d : X) ∈ N ⊓ D := mem_inf.mpr ⟨hd, d.2⟩
    rw [hinf, mem_bot] at h1
    exact Subtype.ext h1
  have hDN : D ≤ normalizer (N : Set X) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := hnorm.conj_mem ⟨x, hNY hx⟩ (mem_subgroupOf.mpr hx) ⟨d, hDY hd⟩
      rw [mem_subgroupOf] at h1
      simpa using h1
    · intro hx
      have h1 := hnorm.conj_mem ⟨d * x * d⁻¹, hNY hx⟩ (mem_subgroupOf.mpr hx) (⟨d, hDY hd⟩)⁻¹
      rw [mem_subgroupOf] at h1
      simpa [mul_assoc] using h1
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : X) ∈ ((D ⊔ N : Subgroup X) : Set X) := by
      rw [sup_comm, hsup]
      exact y.2
    rw [coe_mul_of_left_le_normalizer_right D N hDN] at hy
    obtain ⟨d, hd, n, hn, hdn⟩ := hy
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN', mem_subgroupOf]
    have e : (((inclusion hDY ⟨d, hd⟩)⁻¹ * y : Y) : X) = n := by
      rw [coe_mul, coe_inv, coe_inclusion, ← hdn]
      group
    rw [e]
    exact hn
  set e := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩ with he
  have hkey : ∀ y : Y, (e.symm (QuotientGroup.mk' N' y) : X)⁻¹ * y ∈ N := by
    intro y
    have h1 : φ (e.symm (QuotientGroup.mk' N' y)) = QuotientGroup.mk' N' y :=
      MulEquiv.ofBijective_apply_symm_apply φ ⟨hinj, hsurj⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 : ((inclusion hDY) (e.symm (QuotientGroup.mk' N' y)))⁻¹ * y ∈ N.subgroupOf Y := h1
    rw [mem_subgroupOf] at h2
    simpa using h2
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N'), fun y => ?_, fun y => ?_⟩
  · refine ⟨_, hkey y, ?_⟩
    simp
  · constructor
    · intro h1
      have h2 := hkey y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      rw [h1] at h2
      simpa using h2
    · intro hy
      apply Subtype.ext
      have h2 := hkey y
      have h3 : (e.symm (QuotientGroup.mk' N' y) : X) ∈ N := by
        have := mul_mem hy (inv_mem h2)
        simpa using this
      have h4 : (e.symm (QuotientGroup.mk' N' y) : X) ∈ N ⊓ D := mem_inf.mpr ⟨h3, Subtype.prop _⟩
      rw [hinf, mem_bot] at h4
      simpa using h4

end Complement

end CFSG.SeitzReduction.RankOne
