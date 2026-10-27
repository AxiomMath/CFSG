module

public import CFSG.LocalAnalysis.OddStandard.ThmCTGen
public import CFSG.LocalAnalysis.OddStandard.ThmCTSub

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

theorem extremal_lemma : ∀ a1 a2 ζ : F4c, (a1 ≠ 0 ∨ a2 ≠ 0) → ζ ≠ 0 →
    ∃ s t : F4c × F4c, (symp s (a1, a2) = 0 ∨ symp s (a1, a2) = ζ) ∧
      (symp t (a1, a2) = 0 ∨ symp t (a1, a2) = ζ) ∧ symp s t ≠ 0 ∧ symp s t ≠ ζ := by
  decide +kernel

theorem mem_zpowers_iff_of_sq_eq_one {G : Type*} [Group G] {g : G} (h : g * g = 1) {x : G} :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk']
    have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [hk, h1, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_zpowers_central_iff {ζ d : F4c} :
    (⟨0, 0, d⟩ : Tc) ∈ Subgroup.zpowers (⟨0, 0, ζ⟩ : Tc) ↔ d = 0 ∨ d = ζ := by
  rw [mem_zpowers_iff_of_sq_eq_one (central_sq ζ)]
  constructor
  · rintro (h | h)
    · left; exact congrArg UT3.c h
    · right; exact congrArg UT3.c h
  · rintro (h | h)
    · left; rw [h]; rfl
    · right; rw [h]

theorem extremal_tc {z a : Tc} (hz : z ∈ Subgroup.center Tc) (hz1 : z ≠ 1)
    (ha : a ∉ Subgroup.center Tc) :
    ∃ s t : Tc, ⁅s, a⁆ ∈ Subgroup.zpowers z ∧ ⁅t, a⁆ ∈ Subgroup.zpowers z ∧
      ⁅s, t⁆ ∉ Subgroup.zpowers z := by
  rw [mem_center_iff] at hz ha
  have hzz : z = ⟨0, 0, z.c⟩ := UT3.ext hz.1 hz.2 rfl
  have hζ : z.c ≠ 0 := by
    intro h
    apply hz1
    rw [hzz, h]
    rfl
  have ha' : a.a ≠ 0 ∨ a.b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha hcon
  obtain ⟨s, t, hs, ht, hst1, hst2⟩ := extremal_lemma a.a a.b z.c ha' hζ
  refine ⟨⟨s.1, s.2, 0⟩, ⟨t.1, t.2, 0⟩, ?_, ?_, ?_⟩
  · rw [hzz, comm_eq, mem_zpowers_central_iff]
    exact hs
  · rw [hzz, comm_eq, mem_zpowers_central_iff]
    exact ht
  · rw [hzz, comm_eq, mem_zpowers_central_iff]
    intro h
    rcases h with h | h
    · exact hst1 h
    · exact hst2 h


theorem F4c_cube : ∀ l : F4c, l ≠ 0 → l * l * l = 1 := by decide +kernel

theorem coord_psi (ψ : Tc ≃* Tc) (hZ : ∀ z ∈ Subgroup.center Tc, ψ z = z)
    (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (x : Tc) :
    (ψ x).a = (ψ ⟨x.a, 0, 0⟩).a ∧ (ψ x).b = (ψ ⟨0, x.b, 0⟩).b := by
  have hx : ψ x = ψ ⟨x.a, 0, 0⟩ * ψ ⟨0, x.b, 0⟩ * ψ ⟨0, 0, x.c + x.a * x.b⟩ := by
    conv_lhs => rw [decomp x]
    rw [map_mul, map_mul]
  have h1 : (ψ ⟨x.a, 0, 0⟩).b = 0 := hA _ rfl
  have h2 : (ψ ⟨0, x.b, 0⟩).a = 0 := hB _ rfl
  have h3 : ψ ⟨0, 0, x.c + x.a * x.b⟩ = ⟨0, 0, x.c + x.a * x.b⟩ :=
    hZ _ ((mem_center_iff _).2 ⟨rfl, rfl⟩)
  rw [hx, h3]
  constructor
  · simp [mul_a, h2]
  · simp [mul_b, h1]


theorem diag_tc (ψ : Tc ≃* Tc) (hZ : ∀ z ∈ Subgroup.center Tc, ψ z = z)
    (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) :
    (∀ s, ψ s * s⁻¹ ∈ Subgroup.center Tc) ∨
      ((∀ s, ψ s * s⁻¹ ∈ Subgroup.center Tc → s ∈ Subgroup.center Tc) ∧
        ∀ s, ψ (ψ (ψ s)) * s⁻¹ ∈ Subgroup.center Tc) := by
  have hcoord := coord_psi ψ hZ hA hB
  have hAb : ∀ a : F4c, (ψ ⟨a, 0, 0⟩).b = 0 := fun a => hA _ rfl
  have hBa : ∀ b : F4c, (ψ ⟨0, b, 0⟩).a = 0 := fun b => hB _ rfl
  have hab : ∀ a b : F4c, (ψ ⟨a, 0, 0⟩).a * (ψ ⟨0, b, 0⟩).b = a * b := by
    intro a b
    have h1 : ⁅(⟨a, 0, 0⟩ : Tc), (⟨0, b, 0⟩ : Tc)⁆ = (⟨0, 0, a * b⟩ : Tc) := by
      rw [comm_eq]
      refine UT3.ext rfl rfl ?_
      show a * b + 0 * 0 = a * b
      rw [mul_zero, add_zero]
    have h2 := congrArg ψ h1
    rw [map_commutatorElement, hZ (⟨0, 0, a * b⟩ : Tc) ((mem_center_iff _).2 ⟨rfl, rfl⟩),
      comm_eq] at h2
    have h3 := congrArg UT3.c h2
    simp only [hAb, hBa] at h3
    simpa using h3
  set l : F4c := (ψ ⟨1, 0, 0⟩).a with hl
  set m : F4c := (ψ ⟨0, 1, 0⟩).b with hm
  have hlm : l * m = 1 := by simpa using hab 1 1
  have hα : ∀ a : F4c, (ψ ⟨a, 0, 0⟩).a = a * l := by
    intro a
    have h := hab a 1
    simp only [mul_one] at h
    linear_combination l * h - (ψ ⟨a, 0, 0⟩).a * hlm
  have hβ : ∀ b : F4c, (ψ ⟨0, b, 0⟩).b = b * m := by
    intro b
    have h := hab 1 b
    simp only [one_mul] at h
    linear_combination m * h - (ψ ⟨0, b, 0⟩).b * hlm
  have hpa : ∀ x : Tc, (ψ x).a = x.a * l := fun x => by rw [(hcoord x).1, hα]
  have hpb : ∀ x : Tc, (ψ x).b = x.b * m := fun x => by rw [(hcoord x).2, hβ]
  have hmem : ∀ x : Tc, ψ x * x⁻¹ ∈ Subgroup.center Tc ↔
      x.a * l - x.a = 0 ∧ x.b * m - x.b = 0 := by
    intro x
    rw [mem_center_iff, mul_a, mul_b, hpa, hpb]
    show x.a * l + -x.a = 0 ∧ x.b * m + -x.b = 0 ↔ _
    simp only [← sub_eq_add_neg]
  have hl0 : l ≠ 0 := fun h => by rw [h, zero_mul] at hlm; exact zero_ne_one hlm
  have hm0 : m ≠ 0 := fun h => by rw [h, mul_zero] at hlm; exact zero_ne_one hlm
  by_cases hl1 : l = 1
  · left
    have hm1 : m = 1 := by rw [hl1, one_mul] at hlm; exact hlm
    intro s
    rw [hmem, hl1, hm1]
    simp
  · right
    have hm1 : m ≠ 1 := fun h => hl1 (by rw [h, mul_one] at hlm; exact hlm)
    have hl' : l - 1 ≠ 0 := sub_ne_zero.2 hl1
    have hm' : m - 1 ≠ 0 := sub_ne_zero.2 hm1
    constructor
    · intro s hs
      rw [hmem] at hs
      rw [mem_center_iff]
      constructor
      · have : s.a * (l - 1) = 0 := by linear_combination hs.1
        exact (mul_eq_zero.1 this).resolve_right hl'
      · have : s.b * (m - 1) = 0 := by linear_combination hs.2
        exact (mul_eq_zero.1 this).resolve_right hm'
    · intro s
      rw [mem_center_iff, mul_a, mul_b, hpa, hpb, hpa, hpb, hpa, hpb]
      have h1 := F4c_cube l hl0
      have h2 := F4c_cube m hm0
      show s.a * l * l * l + -s.a = 0 ∧ s.b * m * m * m + -s.b = 0
      constructor
      · have : s.a * l * l * l = s.a := by
          calc s.a * l * l * l = s.a * (l * l * l) := by ring
            _ = s.a := by rw [h1, mul_one]
        rw [this]; exact add_neg_cancel _
      · have : s.b * m * m * m = s.b := by
          calc s.b * m * m * m = s.b * (m * m * m) := by ring
            _ = s.b := by rw [h2, mul_one]
        rw [this]; exact add_neg_cancel _

end CFSG.OddStandard.ThmC.T
