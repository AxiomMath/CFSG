module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

@[expose] def conjAut {G : Type*} [Group G] (K : Subgroup G) (g : G)
    (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hg' : ∀ k ∈ K, g⁻¹ * k * g ∈ K) : ↥K ≃* ↥K where
  toFun k := ⟨g * k * g⁻¹, hg k k.2⟩
  invFun k := ⟨g⁻¹ * k * g, hg' k k.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem center_le_of_equiv {L C : Type*} [Group L] [Group C] (ψ : L ≃* C) {E : Subgroup L}
    {EC : Subgroup C} (hψ : ∀ x : L, x ∈ E ↔ ψ x ∈ EC) (hZ : Subgroup.center C ≤ EC) :
    Subgroup.center L ≤ E := by
  intro z hz
  rw [hψ z]
  refine hZ ?_
  rw [Subgroup.mem_center_iff]
  intro c
  obtain ⟨l, rfl⟩ := ψ.surjective c
  simp only [← map_mul]
  congr 1
  exact (Subgroup.mem_center_iff.mp hz) l

theorem eq_refl_of_fixes_of_equiv {L C : Type*} [Group L] [Group C] (ψ : L ≃* C)
    {E B : Subgroup L} {EC : Subgroup C} (hEB : E ≤ B) (hψ : ∀ x : L, x ∈ E ↔ ψ x ∈ EC)
    (haut : ∀ σ : MulAut C, (∀ e ∈ EC, σ e = e) → ∃ x ∈ EC, σ = MulAut.conj x)
    (hcent : ∀ y ∈ E, (∀ b ∈ B, y * b = b * y) → y ∈ Subgroup.center L)
    (α : L ≃* L) (hα : ∀ b ∈ B, α b = b) : α = MulEquiv.refl L := by
  let σ : MulAut C := ψ.symm.trans (α.trans ψ)
  have hσψ : ∀ l : L, σ (ψ l) = ψ (α l) := by
    intro l
    simp [σ]
  have hσfix : ∀ e ∈ EC, σ e = e := by
    intro e he
    obtain ⟨l, rfl⟩ := ψ.surjective e
    have hlE : l ∈ E := (hψ l).mpr he
    have hlB : l ∈ B := hEB hlE
    rw [hσψ l, hα l hlB]
  obtain ⟨x, hxEC, hx⟩ := haut σ hσfix
  let y : L := ψ.symm x
  have hxy : ψ y = x := by simp [y]
  have hyE : y ∈ E := (hψ y).mpr (by rw [hxy]; exact hxEC)
  have hcomm : ∀ b ∈ B, y * b = b * y := by
    intro b hb
    have hσb : σ (ψ b) = ψ b := by
      rw [hσψ b, hα b hb]
    have hconj : x * ψ b * x⁻¹ = ψ b := by
      rw [hx] at hσb
      simpa [MulAut.conj_apply] using hσb
    have hxcomm : x * ψ b = ψ b * x := by
      have h2 : (x * ψ b) * x⁻¹ = (ψ b * x) * x⁻¹ := by
        rw [hconj, mul_assoc, mul_inv_cancel, mul_one]
      exact mul_right_cancel h2
    have h2 := congrArg ψ.symm hxcomm
    simpa [y] using h2
  have hycenter : y ∈ Subgroup.center L := hcent y hyE hcomm
  have hxcenter : x ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨l, rfl⟩ := ψ.surjective c
    rw [← hxy]
    simp only [← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp hycenter) l
  have hconj1 : MulAut.conj x = 1 := by
    ext c
    rw [MulAut.conj_apply]
    change x * c * x⁻¹ = c
    have hxc : c * x = x * c := (Subgroup.mem_center_iff.mp hxcenter) c
    rw [← hxc, mul_assoc, mul_inv_cancel, mul_one]
  have hσ1 : σ = 1 := by rw [hx, hconj1]
  apply MulEquiv.ext
  intro l
  apply ψ.injective
  have h := hσψ l
  rw [hσ1] at h
  change ψ l = ψ (α l) at h
  exact h.symm

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
