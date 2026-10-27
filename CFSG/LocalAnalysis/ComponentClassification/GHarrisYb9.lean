module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb8

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_b_cases : ∀ u : UT3 F4c, u.b = 0 ∨ u.b = (toUT (gen 6)).b ∨
    u.b = (toUT (gen 7)).b ∨ u.b = (toUT (gen 6)).b + (toUT (gen 7)).b := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

abbrev yX : D.Xt := D.piX ⟨D.toG (SE.gen 7), D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩

theorem pCore_eq_Et
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hle : (pCore 2 D.Xt : Subgroup D.Xt) ≤ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    (h16 : Nat.card (pCore 2 D.Xt) = 16) (h2 : ∀ b ∈ pCore 2 D.Xt, b * b = 1)
    (hc : ∀ b ∈ pCore 2 D.Xt, ∀ c ∈ pCore 2 D.Xt, b * c = c * b)
    (htr : ∀ u ∈ pCore 2 D.Xt, ∀ v ∈ pCore 2 D.Xt, u ≠ 1 → v ≠ 1 → ∃ g : D.Xt, g⁻¹ * u * g = v) :
    pCore 2 D.Xt = D.Et := by
  rcases D.eq_Et_or_Ft hO hz hle h2 hc h16 with h | h
  · exact h
  · exfalso
    rw [h] at htr
    exact D.not_conj_xX_tX (htr _ D.xX_mem_Ft _ D.tX_mem_Ft D.xX_ne_one D.tX_ne_one)

omit [Finite Y] in
theorem preS1_eq {s : D.S1Y} {s₀ : SE} (h : ((s : D.Y1) : Y) = D.toG s₀) : D.preS1 s = s₀ :=
  D.toG_injective (by rw [D.toG_preS1, h])

theorem image_T_cases (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) {τ : D.Xt}
    (hτ : τ ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    τ ∈ D.Et ∨ τ * D.xX⁻¹ ∈ D.Et ∨ τ * D.yX⁻¹ ∈ D.Et ∨ τ * (D.xX * D.yX)⁻¹ ∈ D.Et := by
  set T := ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)
  set sx : D.S1Y := ⟨⟨D.toG (SE.gen 6), D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩,
    mem_subgroupOf.mpr (D.toG_mem_S1 (s₀ := SE.gen 6) (by decide))⟩
  set sy : D.S1Y := ⟨⟨D.toG (SE.gen 7), D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩,
    mem_subgroupOf.mpr (D.toG_mem_S1 (s₀ := SE.gen 7) (by decide))⟩
  have hx : D.xX ∈ T := D.mem_sylowXt hO hz sx
  have hy : D.yX ∈ T := D.mem_sylowXt hO hz sy
  have hxb : (D.tUT hO hz ⟨D.xX, hx⟩).b = (SE.toUT (SE.gen 6)).b := by
    rw [show (⟨D.xX, hx⟩ : T) = ⟨D.piX sx, D.mem_sylowXt hO hz sx⟩ from rfl, D.tUT_apply,
      D.preS1_eq (s := sx) rfl]
  have hyb : (D.tUT hO hz ⟨D.yX, hy⟩).b = (SE.toUT (SE.gen 7)).b := by
    rw [show (⟨D.yX, hy⟩ : T) = ⟨D.piX sy, D.mem_sylowXt hO hz sy⟩ from rfl, D.tUT_apply,
      D.preS1_eq (s := sy) rfl]
  have hb : ∀ (w v : D.Xt) (hw : w ∈ T) (hv : v ∈ T),
      (D.tUT hO hz ⟨w * v⁻¹, mul_mem hw (inv_mem hv)⟩).b =
        (D.tUT hO hz ⟨w, hw⟩).b - (D.tUT hO hz ⟨v, hv⟩).b := by
    intro w v hw hv
    rw [show (⟨w * v⁻¹, mul_mem hw (inv_mem hv)⟩ : T) = ⟨w, hw⟩ * (⟨v, hv⟩ : T)⁻¹ from rfl,
      map_mul, map_inv, UT3.mul_def, UT3.inv_def]
    simp only
    ring
  rcases SE.ut_b_cases (D.tUT hO hz ⟨τ, hτ⟩) with h | h | h | h
  · left; exact (D.mem_Et_iff_tUT hO hz hτ).mpr h
  · right; left
    rw [D.mem_Et_iff_tUT hO hz (mul_mem hτ (inv_mem hx)), hb τ _ hτ hx, h, hxb, sub_self]
  · right; right; left
    rw [D.mem_Et_iff_tUT hO hz (mul_mem hτ (inv_mem hy)), hb τ _ hτ hy, h, hyb, sub_self]
  · right; right; right
    have hxy : D.xX * D.yX ∈ T := mul_mem hx hy
    have hxyb : (D.tUT hO hz ⟨D.xX * D.yX, hxy⟩).b =
        (SE.toUT (SE.gen 6)).b + (SE.toUT (SE.gen 7)).b := by
      rw [show (⟨D.xX * D.yX, hxy⟩ : T) = ⟨D.xX, hx⟩ * ⟨D.yX, hy⟩ from rfl, map_mul,
        UT3.mul_def, hxb, hyb]
    rw [D.mem_Et_iff_tUT hO hz (mul_mem hτ (inv_mem hxy)), hb τ _ hτ hxy, h, hxyb, sub_self]

end GHSylow

end CFSG.ComponentClassification.GHarris
