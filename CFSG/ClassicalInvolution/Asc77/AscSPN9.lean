module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace SPN

set_option linter.unusedSectionVars false

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint

variable {G : Type} [Group G]

section Action

variable (Y : Subgroup G)

@[expose] def conjOn (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G)) : MulAut ↥Y where
  toFun y := ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha y).mp y.2⟩
  invFun y := ⟨a⁻¹ * y * a, by
    have h := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Y : Set G)).inv_mem ha) y
    rw [inv_inv] at h
    exact h.mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    (conjOn Y a ha y : G) = a * y * a⁻¹ := rfl

@[expose] def conjAct (c : G) (hc : c ∈ Subgroup.normalizer (Y : Set G)) :
    ↥(Subgroup.zpowers c) →* MulAut ↥Y where
  toFun a := conjOn Y a.1 (Subgroup.zpowers_le.mpr hc a.2)
  map_one' := by
    ext y
    simp [conjOn_apply]
  map_mul' a b := by
    ext y
    simp [conjOn_apply, mul_assoc]

end Action

theorem zpow_eq_one_or_self {c : G} (hc2 : c * c = 1) (k : ℤ) : c ^ k = 1 ∨ c ^ k = c := by
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, hc2]
  have hk : c ^ k = c ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h, zpow_zero]
  · right; rw [hk, h]; exact zpow_one c

theorem mem_zpowers_eq_one_or_self {c : G} (hc2 : c * c = 1) {a : G}
    (ha : a ∈ Subgroup.zpowers c) : a = 1 ∨ a = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact zpow_eq_one_or_self hc2 k

theorem isPGroup_zpowers_two {c : G} (hc2 : c * c = 1) : IsPGroup 2 ↥(Subgroup.zpowers c) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rcases mem_zpowers_eq_one_or_self hc2 g.2 with h | h
  · simp [h]
  · simp [h, pow_two, hc2]

section Lift

variable [Finite G] {H : Type*} [Group H] (Y : Subgroup G) (π : ↥Y →* H)

theorem exists_fixed_lift (hodd : Odd (Nat.card π.ker)) (c : G)
    (hc : c ∈ Subgroup.normalizer (Y : Set G)) (hc2 : c * c = 1) (s : H)
    (hs : ∀ y : ↥Y, π (conjOn Y c hc y) = s * π y * s⁻¹) {q : H} (hqr : q ∈ π.range)
    (hq : s * q * s⁻¹ = q) : ∃ y : ↥Y, π y = q ∧ c * y = y * c := by
  obtain ⟨y₀, rfl⟩ := hqr
  have hA : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_two hc2
  have hcop : ¬ 2 ∣ Nat.card π.ker := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  have hinv : ∀ (a : ↥(Subgroup.zpowers c)) (x : ↥Y), y₀⁻¹ * x ∈ π.ker →
      y₀⁻¹ * conjAct Y c hc a x ∈ π.ker := by
    intro a x hx
    have hπx : π x = π y₀ := by
      have h1 : π (y₀⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rcases mem_zpowers_eq_one_or_self hc2 a.2 with h | h
    · have : a = 1 := Subtype.ext h
      subst this
      rw [map_one]
      exact hπx.symm
    · have : a = ⟨c, Subgroup.mem_zpowers c⟩ := Subtype.ext h
      subst this
      show π y₀ = π (conjOn Y c hc x)
      rw [hs, hπx, hq]
  obtain ⟨y, hy1, hy2⟩ := (coprime_invariant_coset_fixed 2 hA (conjAct Y c hc) π.ker hcop y₀).2
    hinv
  refine ⟨y, ?_, ?_⟩
  · have h1 : π (y₀⁻¹ * y) = 1 := hy1
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  · have h1 := congrArg Subtype.val (hy2 ⟨c, Subgroup.mem_zpowers c⟩)
    have h2 : c * (y : G) * c⁻¹ = y := h1
    calc c * (y : G) = c * y * c⁻¹ * c := by group
      _ = y * c := by rw [h2]

theorem le_of_closure (S : Subgroup G) (s₁ s₂ : H)
    (hlift₁ : ∀ q ∈ π.range, s₁ * q = q * s₁ →
      ∃ y : ↥Y, π y = q ∧ (y : G) ∈ S)
    (hlift₂ : ∀ q ∈ π.range, s₂ * q = q * s₂ →
      ∃ y : ↥Y, π y = q ∧ (y : G) ∈ S)
    (hker : ∀ n : ↥Y, n ∈ π.ker → (n : G) ∈ S)
    (hgen : ∀ q ∈ π.range, q ∈ Subgroup.closure
      ({q | q ∈ π.range ∧ s₁ * q = q * s₁} ∪ {q | q ∈ π.range ∧ s₂ * q = q * s₂})) :
    Y ≤ S := by
  set T : Subgroup H := (S.subgroupOf Y).map π with hT
  have hsub : ({q | q ∈ π.range ∧ s₁ * q = q * s₁} ∪ {q | q ∈ π.range ∧ s₂ * q = q * s₂} :
      Set H) ⊆ T := by
    rintro q (⟨hq, hc⟩ | ⟨hq, hc⟩)
    · obtain ⟨y, hy, hyS⟩ := hlift₁ q hq hc
      exact ⟨y, hyS, hy⟩
    · obtain ⟨y, hy, hyS⟩ := hlift₂ q hq hc
      exact ⟨y, hyS, hy⟩
  intro y hy
  have hmem : π ⟨y, hy⟩ ∈ T :=
    (Subgroup.closure_le T).mpr hsub (hgen _ ⟨⟨y, hy⟩, rfl⟩)
  obtain ⟨s, hs, hsy⟩ := hmem
  have hsy' : s⁻¹ * ⟨y, hy⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsy, inv_mul_cancel]
  have h3 : ((s⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ S := hker _ hsy'
  have hs' : (s : G) ∈ S := hs
  have : y = (s : G) * ((s⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
  rw [this]
  exact S.mul_mem hs' h3

end Lift

end SPN

end CFSG.ClassicalInvolution.Asc77
