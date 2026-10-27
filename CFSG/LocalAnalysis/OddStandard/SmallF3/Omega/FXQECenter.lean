module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

private lemma fx_qe_a2_sq :
    (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by decide

private lemma fx_qe_a2_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

private lemma fx_qe_a2_central :
    ∀ g : QuaternionGroup 2,
      (QuaternionGroup.a 2 : QuaternionGroup 2) * g = g * QuaternionGroup.a 2 := by
  decide

private lemma fx_qe_a2_center :
    ∀ g : QuaternionGroup 2, (∀ h, g * h = h * g) →
      g = 1 ∨ g = QuaternionGroup.a 2 := by
  decide

private lemma fx_qe_mem_centerIn_iff {G : Type} [Group G] {X : Subgroup G} {x : G} :
    x ∈ centerIn X ↔ x ∈ X ∧ ∀ y ∈ X, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (h g g.2).symm

theorem fx_qe_center_data {G : Type} [Group G] {Q₁ Q₂ : Subgroup G} {z : G}
    (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hz : centerIn (Q₁ ⊔ Q₂) = zpowers z) :
    z * z = 1 ∧ z ≠ 1 ∧ ∃ (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂),
      e₁ ⟨z, hz₁⟩ = QuaternionGroup.a 2 ∧ e₂ ⟨z, hz₂⟩ = QuaternionGroup.a 2 := by
  let c₁ : G := ((e₁.symm (QuaternionGroup.a 2) : ↥Q₁) : G)
  let c₂ : G := ((e₂.symm (QuaternionGroup.a 2) : ↥Q₂) : G)
  have hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer (Q₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  have hc1Q1 : c₁ ∈ Q₁ := (e₁.symm (QuaternionGroup.a 2)).2
  have hc2Q2 : c₂ ∈ Q₂ := (e₂.symm (QuaternionGroup.a 2)).2
  have hc1cent : ∀ g : ↥Q₁, c₁ * (g : G) = (g : G) * c₁ := by
    intro g
    have h : (e₁.symm (QuaternionGroup.a 2)) * g = g * (e₁.symm (QuaternionGroup.a 2)) := by
      apply e₁.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using fx_qe_a2_central (e₁ g)
    simpa using congrArg Subtype.val h
  have hc2cent : ∀ g : ↥Q₂, c₂ * (g : G) = (g : G) * c₂ := by
    intro g
    have h : (e₂.symm (QuaternionGroup.a 2)) * g = g * (e₂.symm (QuaternionGroup.a 2)) := by
      apply e₂.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using fx_qe_a2_central (e₂ g)
    simpa using congrArg Subtype.val h
  have hc1sq : c₁ * c₁ = 1 := by
    have h : (e₁.symm (QuaternionGroup.a 2)) * (e₁.symm (QuaternionGroup.a 2)) = 1 := by
      apply e₁.injective
      simpa only [map_mul, map_one, MulEquiv.apply_symm_apply] using fx_qe_a2_sq
    simpa using congrArg Subtype.val h
  have hc2sq : c₂ * c₂ = 1 := by
    have h : (e₂.symm (QuaternionGroup.a 2)) * (e₂.symm (QuaternionGroup.a 2)) = 1 := by
      apply e₂.injective
      simpa only [map_mul, map_one, MulEquiv.apply_symm_apply] using fx_qe_a2_sq
    simpa using congrArg Subtype.val h
  have hc1ne : c₁ ≠ 1 := by
    intro h
    have hsub : (e₁.symm (QuaternionGroup.a 2) : ↥Q₁) = 1 := Subtype.ext h
    exact fx_qe_a2_ne_one (by simpa using congrArg e₁ hsub)
  have hc2ne : c₂ ≠ 1 := by
    intro h
    have hsub : (e₂.symm (QuaternionGroup.a 2) : ↥Q₂) = 1 := Subtype.ext h
    exact fx_qe_a2_ne_one (by simpa using congrArg e₂ hsub)
  have hle_norm : Q₁ ≤ Subgroup.normalizer (Q₂ : Set G) :=
    le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
      (Subgroup.centralizer_le_normalizer (Q₂ : Set G))
  have hc1Z : c₁ ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [fx_qe_mem_centerIn_iff]
    refine ⟨Subgroup.mem_sup_left hc1Q1, fun y hy => ?_⟩
    have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({c₁} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc1cent ⟨x, hx⟩).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm c₁ hc1Q1 y hy).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hc2Z : c₂ ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [fx_qe_mem_centerIn_iff]
    refine ⟨Subgroup.mem_sup_right hc2Q2, fun y hy => ?_⟩
    have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({c₂} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm x hx c₂ hc2Q2
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc2cent ⟨y, hy⟩).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hcenter_sq : ∀ g ∈ centerIn (Q₁ ⊔ Q₂), g * g = 1 := by
    intro g hg
    obtain ⟨hgmem, hgcomm⟩ := fx_qe_mem_centerIn_iff.mp hg
    have hgprod : g ∈ (Q₁ : Set G) * (Q₂ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hle_norm]
      exact hgmem
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hgprod
    rw [← hxy] at hgcomm ⊢
    have hxcent : ∀ h ∈ Q₁, x * h = h * x := by
      intro h hh
      have h1 : (x * y) * h = h * (x * y) := hgcomm h (Subgroup.mem_sup_left hh)
      have hyh : y * h = h * y := (hcomm h hh y hy).symm
      have h2 : (x * h) * y = (h * x) * y := by
        calc (x * h) * y = x * (h * y) := by rw [mul_assoc]
          _ = x * (y * h) := by rw [← hyh]
          _ = (x * y) * h := by rw [← mul_assoc]
          _ = h * (x * y) := h1
          _ = (h * x) * y := by rw [← mul_assoc]
      exact mul_right_cancel h2
    have hxQ8 : e₁ ⟨x, hx⟩ = 1 ∨ e₁ ⟨x, hx⟩ = QuaternionGroup.a 2 := by
      refine fx_qe_a2_center _ fun t => ?_
      have h : (⟨x, hx⟩ : ↥Q₁) * (e₁.symm t) = (e₁.symm t) * ⟨x, hx⟩ :=
        Subtype.ext (hxcent (e₁.symm t) (e₁.symm t).2)
      simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e₁ h
    have hxcases : x = 1 ∨ x = c₁ := by
      rcases hxQ8 with h | h
      · left
        have : (⟨x, hx⟩ : ↥Q₁) = 1 := by simpa using congrArg e₁.symm h
        exact congrArg Subtype.val this
      · right
        have : (⟨x, hx⟩ : ↥Q₁) = e₁.symm (QuaternionGroup.a 2) := by
          simpa using congrArg e₁.symm h
        exact congrArg Subtype.val this
    have hycent : ∀ k ∈ Q₂, y * k = k * y := by
      intro k hk
      have h1 : (x * y) * k = k * (x * y) := hgcomm k (Subgroup.mem_sup_right hk)
      have hxk : x * k = k * x := hcomm x hx k hk
      have h2 : x * (y * k) = x * (k * y) := by
        calc x * (y * k) = (x * y) * k := by rw [← mul_assoc]
          _ = k * (x * y) := h1
          _ = (k * x) * y := by rw [← mul_assoc]
          _ = (x * k) * y := by rw [hxk]
          _ = x * (k * y) := by rw [mul_assoc]
      exact mul_left_cancel h2
    have hyQ8 : e₂ ⟨y, hy⟩ = 1 ∨ e₂ ⟨y, hy⟩ = QuaternionGroup.a 2 := by
      refine fx_qe_a2_center _ fun t => ?_
      have h : (⟨y, hy⟩ : ↥Q₂) * (e₂.symm t) = (e₂.symm t) * ⟨y, hy⟩ :=
        Subtype.ext (hycent (e₂.symm t) (e₂.symm t).2)
      simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e₂ h
    have hycases : y = 1 ∨ y = c₂ := by
      rcases hyQ8 with h | h
      · left
        have : (⟨y, hy⟩ : ↥Q₂) = 1 := by simpa using congrArg e₂.symm h
        exact congrArg Subtype.val this
      · right
        have : (⟨y, hy⟩ : ↥Q₂) = e₂.symm (QuaternionGroup.a 2) := by
          simpa using congrArg e₂.symm h
        exact congrArg Subtype.val this
    rcases hxcases with rfl | rfl <;> rcases hycases with rfl | rfl
    · simp
    · simpa using hc2sq
    · simpa using hc1sq
    · have hc12 : c₁ * c₂ = c₂ * c₁ := hcomm c₁ hc1Q1 c₂ hc2Q2
      have hc12' : c₂ * c₁ = c₁ * c₂ := hc12.symm
      calc (c₁ * c₂) * (c₁ * c₂)
          = c₁ * (c₂ * (c₁ * c₂)) := by rw [mul_assoc c₁ c₂ (c₁ * c₂)]
        _ = c₁ * ((c₂ * c₁) * c₂) := by rw [← mul_assoc c₂ c₁ c₂]
        _ = c₁ * ((c₁ * c₂) * c₂) := by rw [hc12']
        _ = c₁ * (c₁ * (c₂ * c₂)) := by rw [mul_assoc c₁ c₂ c₂]
        _ = (c₁ * c₁) * (c₂ * c₂) := by rw [← mul_assoc c₁ c₁ (c₂ * c₂)]
        _ = 1 := by rw [hc1sq, hc2sq, one_mul]
  have hzZ : z ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hzz : z * z = 1 := hcenter_sq z hzZ
  have hzpow : ∀ n : ℤ, z ^ n = 1 ∨ z ^ n = z := by
    intro n
    have h2 : z ^ (2 : ℕ) = 1 := by simpa [pow_two] using hzz
    rw [zpow_eq_zpow_emod' n h2]
    have hpar : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one n
    rcases hpar with h | h
    · left
      rw [h]
      simp
    · right
      rw [h]
      simp
  have hc1zp : c₁ ∈ zpowers z := hz ▸ hc1Z
  have hc1eq : c₁ = z := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc1zp
    rcases hzpow n with h | h
    · exact (hc1ne (by rw [← hn, h])).elim
    · rw [← hn, h]
  have hc2zp : c₂ ∈ zpowers z := hz ▸ hc2Z
  have hc2eq : c₂ = z := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc2zp
    rcases hzpow n with h | h
    · exact (hc2ne (by rw [← hn, h])).elim
    · rw [← hn, h]
  have hzQ1 : z ∈ Q₁ := hc1eq ▸ hc1Q1
  have hzQ2 : z ∈ Q₂ := hc2eq ▸ hc2Q2
  refine ⟨hzz, hc1eq ▸ hc1ne, hzQ1, hzQ2, ?_, ?_⟩
  · have hsub : (e₁.symm (QuaternionGroup.a 2) : ↥Q₁) = ⟨z, hzQ1⟩ := Subtype.ext hc1eq
    rw [← hsub, MulEquiv.apply_symm_apply]
  · have hsub : (e₂.symm (QuaternionGroup.a 2) : ↥Q₂) = ⟨z, hzQ2⟩ := Subtype.ext hc2eq
    rw [← hsub, MulEquiv.apply_symm_apply]

end CFSG.OddStandard.SmallF3.Omega
