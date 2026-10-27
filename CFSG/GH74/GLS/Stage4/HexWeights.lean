module

public import CFSG.GH74.GLS.Stage4.HexSL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.SP.GlueDefs

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Hex

section Scalars

variable {F : Type*} [Field F]

theorem sl2D_mul_sl2U (t : Fˣ) (c : F) : sl2D t * sl2U c = sl2U ((t : F) ^ 2 * c) * sl2D t := by
  apply sl2_ext
  have ht : (t : F) ≠ 0 := t.ne_zero
  simp [Matrix.SpecialLinearGroup.coe_mul]
  field_simp

theorem ringHom_eq_id_of_sq (hF2 : (2 : F) ≠ 0) (σ : F →+* F) (h : ∀ t, σ t ^ 2 = t ^ 2) (t : F) :
    σ t = t := by
  have key : ∀ x, σ x = x ∨ σ x = -x := fun x => by
    have : (σ x - x) * (σ x + x) = 0 := by linear_combination h x
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  rcases key t with h1 | h1
  · exact h1
  · by_cases ht : t = 0
    · simp [ht]
    · rcases key (t + 1) with h2 | h2
      · rw [map_add, map_one, h1] at h2
        exfalso
        apply ht
        have : 2 * t = 0 := by linear_combination -h2
        exact (mul_eq_zero.1 this).resolve_left hF2
      · rw [map_add, map_one, h1] at h2
        exfalso
        have : (2 : F) = 0 := by linear_combination h2
        exact hF2 this

variable {G : Type*} [Group G]

theorem exists_scalar_of_normalizes (hF2 : (2 : F) ≠ 0) (φ : SL2 F →* G)
    (hφ : Function.Injective φ) {Hs : Subgroup G}
    (hcomm : ∀ a ∈ Hs, ∀ b ∈ Hs, a * b = b * a) (hD : ∀ t : Fˣ, φ (sl2D t) ∈ Hs) {h : G}
    (hh : h ∈ Hs) (hU : ∀ c, ∃ d, h * φ (sl2U c) * h⁻¹ = φ (sl2U d))
    (hL : ∀ c, ∃ d, h * φ (sl2L c) * h⁻¹ = φ (sl2L d)) :
    ∃ a : F, a ≠ 0 ∧ (∀ c, h * φ (sl2U c) * h⁻¹ = φ (sl2U (a * c))) ∧
      ∀ c, h * φ (sl2L c) * h⁻¹ = φ (sl2L (a⁻¹ * c)) := by
  choose A hA using hU
  choose B hB using hL
  obtain ⟨a, σ, ha, hAσ, hBσ⟩ := sl2_conj_weight hF2 φ hφ h A B hA hB
  have hσ : ∀ t : F, σ t ^ 2 = t ^ 2 := by
    intro t
    by_cases ht : t = 0
    · simp [ht]
    · let u : Fˣ := Units.mk0 t ht
      have hc : Commute h (φ (sl2D u)) := hcomm h hh _ (hD u)
      have hconj : ∀ c, φ (sl2D u) * φ (sl2U c) * (φ (sl2D u))⁻¹ = φ (sl2U ((u : F) ^ 2 * c)) :=
        fun c => by
          rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, sl2D_mul_sl2U]
      have hAt : ∀ c, A ((u : F) ^ 2 * c) = (u : F) ^ 2 * A c := by
        intro c
        apply sl2U_injective
        apply hφ
        calc φ (sl2U (A ((u : F) ^ 2 * c))) = h * φ (sl2U ((u : F) ^ 2 * c)) * h⁻¹ := (hA _).symm
          _ = h * (φ (sl2D u) * φ (sl2U c) * (φ (sl2D u))⁻¹) * h⁻¹ := by rw [hconj]
          _ = (h * φ (sl2D u)) * φ (sl2U c) * ((φ (sl2D u))⁻¹ * h⁻¹) := by group
          _ = (φ (sl2D u) * h) * φ (sl2U c) * (h⁻¹ * (φ (sl2D u))⁻¹) := by
              rw [hc.eq, hc.symm.inv_inv.eq]
          _ = φ (sl2D u) * (h * φ (sl2U c) * h⁻¹) * (φ (sl2D u))⁻¹ := by group
          _ = φ (sl2D u) * φ (sl2U (A c)) * (φ (sl2D u))⁻¹ := by rw [hA]
          _ = φ (sl2U ((u : F) ^ 2 * A c)) := hconj _
      have h1 := hAt 1
      rw [hAσ, hAσ, mul_one] at h1
      simp only [map_pow, map_one, mul_one] at h1
      have h3 : σ u ^ 2 = (u : F) ^ 2 := mul_left_cancel₀ ha (by linear_combination h1)
      simpa [u] using h3
  have hσid : ∀ t, σ t = t := ringHom_eq_id_of_sq hF2 σ hσ
  refine ⟨a, ha, fun c => ?_, fun c => ?_⟩
  · rw [hA, hAσ, hσid]
  · rw [hB, hBσ, hσid]

end Scalars

section RankOne

open CFSG.GH74.GLS.SP

variable {G : Type} [Group G] {H : Subgroup G} {root : ℤ → Subgroup G}

structure RankOneAt (H : Subgroup G) (root : ℤ → Subgroup G) (i : ℤ) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  φ : SL2 F →* G
  inj : Function.Injective φ
  hU : ∀ x, x ∈ root i ↔ ∃ c, φ (sl2U c) = x
  hL : ∀ x, x ∈ root (-i) ↔ ∃ c, φ (sl2L c) = x
  hD : ∀ t : Fˣ, φ (sl2D t) ∈ H

attribute [instance] RankOneAt.field RankOneAt.finite

theorem RankOneAt.card_root {i : ℤ} (E : RankOneAt H root i) :
    Nat.card (root i) = Nat.card E.F := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : E.F => (⟨E.φ (sl2U c),
    (E.hU _).2 ⟨c, rfl⟩⟩ : root i)) ⟨fun c d h => ?_, fun ⟨x, hx⟩ => ?_⟩)
  · exact sl2U_injective (E.inj (congrArg Subtype.val h))
  · obtain ⟨c, hc⟩ := (E.hU x).1 hx
    exact ⟨c, Subtype.ext hc⟩

end RankOne

section Actions

open CFSG.GH74.GLS.SP CFSG.GH74.BNPair

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} (R : RGD2 6 H r₁ r₂ U root)

theorem mem_iff_conj_of_conjBy {m : G} {A B : Subgroup G} (h : conjBy m⁻¹ A = B) (x : G) :
    x ∈ A ↔ m * x * m⁻¹ ∈ B := by
  rw [← h, mem_conjBy_iff]
  simp [mul_assoc]

include R in
theorem RGD2.mem_iff_r₂ {i : ℤ} (h1 : 1 ≤ i) (h5 : i ≤ 5) (x : G) :
    x ∈ root i ↔ r₂ * x * r₂⁻¹ ∈ root (6 - i) := by
  have := (R.act₂.2.2 i h1 (by exact_mod_cast h5)).1
  exact mem_iff_conj_of_conjBy (by simpa using this) x

include R in
theorem RGD2.mem_iff_r₂_neg {i : ℤ} (h1 : 1 ≤ i) (h5 : i ≤ 5) (x : G) :
    x ∈ root (-i) ↔ r₂ * x * r₂⁻¹ ∈ root (-(6 - i)) := by
  have := (R.act₂.2.2 i h1 (by exact_mod_cast h5)).2
  exact mem_iff_conj_of_conjBy (by simpa using this) x

include R in
theorem RGD2.mem_iff_r₁ {i : ℤ} (h2 : 2 ≤ i) (h6 : i ≤ 6) (x : G) :
    x ∈ root i ↔ r₁ * x * r₁⁻¹ ∈ root (8 - i) := by
  have := (R.act₁.2.2 i h2 (by exact_mod_cast h6)).1
  exact mem_iff_conj_of_conjBy (by simpa using this) x

include R in
theorem RGD2.mem_iff_r₁_neg {i : ℤ} (h2 : 2 ≤ i) (h6 : i ≤ 6) (x : G) :
    x ∈ root (-i) ↔ r₁ * x * r₁⁻¹ ∈ root (-(8 - i)) := by
  have := (R.act₁.2.2 i h2 (by exact_mod_cast h6)).2
  exact mem_iff_conj_of_conjBy (by simpa using this) x

end Actions

end CFSG.GH74.GLS.Stage4.Hex
