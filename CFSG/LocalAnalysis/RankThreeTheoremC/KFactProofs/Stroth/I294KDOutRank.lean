module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.StatedDefs
import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open (StatedScalars StatedProj)

@[expose] def orderThreeHom {G : Type*} [Group G] (x : G) (hx : x ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun t := x ^ (Multiplicative.toAdd t).val
  map_one' := by simp
  map_mul' s t := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, pow_add]

theorem pow_three_eq_one_of_multiplicative_zmod (m : Multiplicative (ZMod 3)) : m ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
  have : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [this, zero_mul]

theorem four_le_pRank_of_commuting_order_three {G : Type*} [Group G] [Finite G]
    (x₁ x₂ x₃ x₄ : G) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1) (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1)
    (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃) (c₁₄ : Commute x₁ x₄) (c₂₃ : Commute x₂ x₃)
    (c₂₄ : Commute x₂ x₄) (c₃₄ : Commute x₃ x₄)
    (hind : ∀ a b c d : ℕ, x₁ ^ a * x₂ ^ b * x₃ ^ c * x₄ ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  set M := Multiplicative (ZMod 3) with hM
  let φ₁ := orderThreeHom x₁ h₁
  let φ₂ := orderThreeHom x₂ h₂
  let φ₃ := orderThreeHom x₃ h₃
  let φ₄ := orderThreeHom x₄ h₄
  have k₁₂ : ∀ s t : M, Commute (φ₁ s) (φ₂ t) := fun s t => c₁₂.pow_pow _ _
  have k₃₄ : ∀ s t : M, Commute (φ₃ s) (φ₄ t) := fun s t => c₃₄.pow_pow _ _
  let ψ₁ : M × M →* G := φ₁.noncommCoprod φ₂ k₁₂
  let ψ₂ : M × M →* G := φ₃.noncommCoprod φ₄ k₃₄
  have kk : ∀ s t : M × M, Commute (ψ₁ s) (ψ₂ t) := by
    intro s t
    rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply]
    exact ((c₁₃.pow_pow _ _).mul_right (c₁₄.pow_pow _ _)).mul_left
      ((c₂₃.pow_pow _ _).mul_right (c₂₄.pow_pow _ _))
  let f : (M × M) × (M × M) →* G := ψ₁.noncommCoprod ψ₂ kk
  have hf : ∀ s : (M × M) × (M × M), f s =
      x₁ ^ (Multiplicative.toAdd s.1.1).val * x₂ ^ (Multiplicative.toAdd s.1.2).val *
        x₃ ^ (Multiplicative.toAdd s.2.1).val * x₄ ^ (Multiplicative.toAdd s.2.2).val := by
    intro s
    simp only [f, ψ₁, ψ₂, MonoidHom.noncommCoprod_apply, mul_assoc]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨s₁, s₂⟩, ⟨s₃, s₄⟩⟩ hs
    obtain ⟨ha, hb, hc, hd⟩ := hind _ _ _ _ ((hf _).symm.trans hs)
    have hz : ∀ s : M, 3 ∣ (Multiplicative.toAdd s).val → s = 1 := by
      intro s hs'
      have h3 := ZMod.val_lt (Multiplicative.toAdd s)
      have h0 : (Multiplicative.toAdd s).val = 0 := by omega
      exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h0)
    exact Prod.ext (Prod.ext (hz _ ha) (hz _ hb)) (Prod.ext (hz _ hc) (hz _ hd))
  have hM3 : Nat.card M = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : M ≃ ZMod 3), Nat.card_zmod]
  have hcard : Nat.card ((M × M) × (M × M)) = 3 ^ 4 := by
    rw [Nat.card_prod, Nat.card_prod, hM3]
    norm_num
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ hcard f hinj
    (le_top : f.range ≤ ⊤)
  · intro a b
    exact mul_comm a b
  · intro a
    exact Prod.ext (Prod.ext (pow_three_eq_one_of_multiplicative_zmod _)
      (pow_three_eq_one_of_multiplicative_zmod _))
      (Prod.ext (pow_three_eq_one_of_multiplicative_zmod _)
        (pow_three_eq_one_of_multiplicative_zmod _))

theorem four_le_pRank_of_mulEquiv {X Q : Type*} [Group X] [Finite X] [Group Q] (e : X ≃* Q)
    (y₁ y₂ y₃ y₄ : Q) (h₁ : y₁ ^ 3 = 1) (h₂ : y₂ ^ 3 = 1) (h₃ : y₃ ^ 3 = 1) (h₄ : y₄ ^ 3 = 1)
    (c₁₂ : Commute y₁ y₂) (c₁₃ : Commute y₁ y₃) (c₁₄ : Commute y₁ y₄) (c₂₃ : Commute y₂ y₃)
    (c₂₄ : Commute y₂ y₄) (c₃₄ : Commute y₃ y₄)
    (hind : ∀ a b c d : ℕ, y₁ ^ a * y₂ ^ b * y₃ ^ c * y₄ ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hs : ∀ y : Q, y ^ 3 = 1 → (e.symm y) ^ 3 = 1 := fun y hy => by
    rw [← map_pow, hy, map_one]
  refine four_le_pRank_of_commuting_order_three (e.symm y₁) (e.symm y₂) (e.symm y₃) (e.symm y₄)
    (hs _ h₁) (hs _ h₂) (hs _ h₃) (hs _ h₄) (c₁₂.map e.symm.toMonoidHom)
    (c₁₃.map e.symm.toMonoidHom) (c₁₄.map e.symm.toMonoidHom) (c₂₃.map e.symm.toMonoidHom)
    (c₂₄.map e.symm.toMonoidHom) (c₃₄.map e.symm.toMonoidHom) ?_
  intro a b c d h
  refine hind a b c d ?_
  have := congrArg e h
  simpa [map_mul, map_pow] using this

theorem four_le_pRank_statedProj {X : Type} [Group X] [Finite X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] (H : Subgroup (GL ι F)) (e : X ≃* StatedProj H)
    (A₁ A₂ A₃ A₄ : GL ι F) (m₁ : A₁ ∈ H) (m₂ : A₂ ∈ H) (m₃ : A₃ ∈ H) (m₄ : A₄ ∈ H)
    (h₁ : A₁ ^ 3 = 1) (h₂ : A₂ ^ 3 = 1) (h₃ : A₃ ^ 3 = 1) (h₄ : A₄ ^ 3 = 1)
    (c₁₂ : Commute A₁ A₂) (c₁₃ : Commute A₁ A₃) (c₁₄ : Commute A₁ A₄) (c₂₃ : Commute A₂ A₃)
    (c₂₄ : Commute A₂ A₄) (c₃₄ : Commute A₃ A₄)
    (hind : ∀ a b c d : ℕ, A₁ ^ a * A₂ ^ b * A₃ ^ c * A₄ ^ d ∈ StatedScalars ι F →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  let π : H →* StatedProj H := QuotientGroup.mk' _
  let B₁ : H := ⟨A₁, m₁⟩
  let B₂ : H := ⟨A₂, m₂⟩
  let B₃ : H := ⟨A₃, m₃⟩
  let B₄ : H := ⟨A₄, m₄⟩
  have pw : ∀ (B : H) (A : GL ι F), (B : GL ι F) = A → A ^ 3 = 1 → π B ^ 3 = 1 := by
    intro B A hBA hA
    rw [← map_pow]
    have : B ^ 3 = 1 := Subtype.ext (by simpa [hBA] using hA)
    rw [this, map_one]
  have cm : ∀ (B B' : H) (A A' : GL ι F), (B : GL ι F) = A → (B' : GL ι F) = A' →
      Commute A A' → Commute (π B) (π B') := by
    intro B B' A A' hB hB' hc
    have hc' : Commute B B' := Subtype.ext (by simpa [hB, hB'] using hc.eq)
    exact hc'.map π
  refine four_le_pRank_of_mulEquiv e (π B₁) (π B₂) (π B₃) (π B₄) (pw B₁ A₁ rfl h₁)
    (pw B₂ A₂ rfl h₂) (pw B₃ A₃ rfl h₃) (pw B₄ A₄ rfl h₄) (cm B₁ B₂ A₁ A₂ rfl rfl c₁₂)
    (cm B₁ B₃ A₁ A₃ rfl rfl c₁₃) (cm B₁ B₄ A₁ A₄ rfl rfl c₁₄) (cm B₂ B₃ A₂ A₃ rfl rfl c₂₃)
    (cm B₂ B₄ A₂ A₄ rfl rfl c₂₄) (cm B₃ B₄ A₃ A₄ rfl rfl c₃₄) ?_
  intro a b c d h
  refine hind a b c d ?_
  rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have := Subgroup.mem_subgroupOf.mp h
  simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
