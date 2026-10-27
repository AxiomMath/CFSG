module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxLAbstract

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex

variable {X : Type*} [Group X]

section ChainNoT

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

@[expose] def PointClosedP (P : Subgroup X → Prop) (U : Subgroup X) (root : ℤ → Subgroup X)
    (k : ℤ) : Prop :=
  ∀ H₀ : Subgroup X, longSub 6 root ≤ H₀ → ∀ v ∈ U, (∀ y ∈ root k, v * y * v⁻¹ ∈ H₀) →
    (∃ y ∈ root k, v * y * v⁻¹ ∉ PLset root) → P H₀

theorem PointClosedP_of_move {P : Subgroup X → Prop} {r : X} {k k' : ℤ}
    (hr : GoodActEven 6 root r)
    (hP : ∀ H₀ : Subgroup X, P (H₀.map (MulAut.conj r).toMonoidHom) → P H₀)
    (hk : ∀ y ∈ root k, r * y * r⁻¹ ∈ root k') (hk' : ∀ z ∈ root k', r⁻¹ * z * r ∈ root k)
    (hmove : ∀ v ∈ U, ∃ v' ∈ U, ∀ y ∈ root k, r * (v * y * v⁻¹) * r⁻¹ = v' * (r * y * r⁻¹) * v'⁻¹)
    (hS : PointClosedP P U root k') : PointClosedP P U root k := by
  intro H₀ hL v hv hH hnP
  obtain ⟨v', hv', hvv⟩ := hmove v hv
  set H₁ : Subgroup X := H₀.map (MulAut.conj r).toMonoidHom with hH₁
  have memH₁ : ∀ z, r⁻¹ * z * r ∈ H₀ → z ∈ H₁ := fun z hz =>
    ⟨r⁻¹ * z * r, hz, by show r * (r⁻¹ * z * r) * r⁻¹ = z; group⟩
  have hL₁ : longSub 6 root ≤ H₁ := fun ℓ hℓ => by
    have h1 := conj_mem_longSub (by norm_num) (by norm_num) hr.inv hℓ
    rw [inv_inv] at h1
    exact memH₁ ℓ (hL h1)
  have hres : (∀ z ∈ root k', v' * z * v'⁻¹ ∈ H₁) := by
    intro z hz
    have hy := hk' z hz
    have e : v' * z * v'⁻¹ = r * (v * (r⁻¹ * z * r) * v⁻¹) * r⁻¹ := by
      rw [hvv _ hy]; group
    rw [e]
    exact ⟨_, hH _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀n⟩ := hnP
  have hz₀ := hk y₀ hy₀
  have hn : v' * (r * y₀ * r⁻¹) * v'⁻¹ ∉ PLset root := by
    intro hmem
    apply hy₀n
    have e : r * (v * y₀ * v⁻¹) * r⁻¹ = v' * (r * y₀ * r⁻¹) * v'⁻¹ := hvv y₀ hy₀
    rw [← e] at hmem
    have := PLset_conj hr.inv hmem
    simpa [mul_assoc] using this
  exact hP H₀ (hS H₁ hL₁ v' hv' hres ⟨_, hz₀, hn⟩)

variable (R : RGD2 6 H r₁ r₂ U root)

include R in
theorem pointClosedP_chain {P : Subgroup X → Prop}
    (hP₁ : ∀ H₀ : Subgroup X, P (H₀.map (MulAut.conj r₁).toMonoidHom) → P H₀)
    (hP₂ : ∀ H₀ : Subgroup X, P (H₀.map (MulAut.conj r₂).toMonoidHom) → P H₀)
    (c66 : ∀ b ∈ root (-6), ∀ z ∈ root (-6), b * z = z * b)
    (c64 : ∀ b ∈ root (-6), ∀ z ∈ root (-4), b * z = z * b)
    (c16 : ∀ b ∈ root (-1), ∀ z ∈ root 6, b * z = z * b)
    (c12 : ∀ b ∈ root (-1), ∀ z ∈ root (-2), b * z = z * b)
    (hS4 : PointClosedP P U root (-4)) :
    PointClosedP P U root (-2) ∧ PointClosedP P U root (-6) ∧ PointClosedP P U root 6 ∧
      PointClosedP P U root 2 := by
  have hr₁ := R.goodActEven_r₁ (by norm_num : 6 % 2 = 0)
  have hr₂ := R.goodActEven_r₂ (by norm_num : 6 % 2 = 0)
  have a₁ := actsPos_r₁' R
  have a₁' := actsPos_r₁_inv' R
  have a₂ := actsPos_r₂' R
  have a₂' := actsPos_r₂_inv' R
  have p24 : PointClosedP P U root (-2) := by
    have hk : ∀ y ∈ root (-2), r₂ * y * r₂⁻¹ ∈ root (-4) := fun y hy =>
      actsPos_root a₂ (q := 7) (k := -2) (k' := -4) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-4), r₂⁻¹ * z * r₂ ∈ root (-2) := fun z hz => by
      have := actsPos_root a₂' (q := 9) (k := -4) (k' := -2) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosedP_of_move hr₂ hP₂ hk hk' (fun v hv => move_r₂ R hk c64 hv) hS4
  have p62 : PointClosedP P U root (-6) := by
    have hk : ∀ y ∈ root (-6), r₁ * y * r₁⁻¹ ∈ root (-2) := fun y hy =>
      actsPos_root a₁ (q := 11) (k := -6) (k' := -2) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-2), r₁⁻¹ * z * r₁ ∈ root (-6) := fun z hz => by
      have := actsPos_root a₁' (q := 7) (k := -2) (k' := -6) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosedP_of_move hr₁ hP₁ hk hk' (fun v hv => move_r₁ R hk c12 hv) p24
  have p6 : PointClosedP P U root 6 := by
    have hk : ∀ y ∈ root 6, r₂ * y * r₂⁻¹ ∈ root (-6) := fun y hy =>
      actsPos_root a₂ (q := 5) (k := 6) (k' := -6) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-6), r₂⁻¹ * z * r₂ ∈ root 6 := fun z hz => by
      have := actsPos_root a₂' (q := 11) (k := -6) (k' := 6) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosedP_of_move hr₂ hP₂ hk hk' (fun v hv => move_r₂ R hk c66 hv) p62
  have p2 : PointClosedP P U root 2 := by
    have hk : ∀ y ∈ root 2, r₁ * y * r₁⁻¹ ∈ root 6 := fun y hy =>
      actsPos_root a₁ (q := 1) (k := 2) (k' := 6) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root 6, r₁⁻¹ * z * r₁ ∈ root 2 := fun z hz => by
      have := actsPos_root a₁' (q := 5) (k := 6) (k' := 2) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosedP_of_move hr₁ hP₁ hk hk' (fun v hv => move_r₁ R hk c16 hv) p6
  exact ⟨p24, p62, p6, p2⟩

end ChainNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
