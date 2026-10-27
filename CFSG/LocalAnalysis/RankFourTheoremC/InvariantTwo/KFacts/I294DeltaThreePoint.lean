module

public import CFSG.RankThree.PartOne.KLC.ThreePoint

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open MulAction CFSG.RankThree.PartOne.KLC
open scoped commutatorElement

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem smul_eq_of_pElement {F y z : X} (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {α : A} {m : ℕ} (hα : α ^ p ^ m = 1) (a : A) :
    α • (a • F) = a • F := by
  classical
  have step : ∀ j : ℕ, (∀ a : A, α ^ p ^ (j + 1) • (a • F) = a • F) →
      ∀ a : A, α ^ p ^ j • (a • F) = a • F := by
    intro j hj a
    refine smul_eq_of_pow_fixes (α := α ^ p ^ j) (S := ({F, y, z} : Finset X))
      Finset.card_le_three hp hp5 (fun k => ?_) (fun k => ?_)
    · rw [smul_smul]
      have := hO ((α ^ p ^ j) ^ k * a)
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    · have h1 := hj ((α ^ p ^ j) ^ k * a)
      have e : (α ^ p ^ j) ^ p = α ^ p ^ (j + 1) := by rw [← pow_mul, ← pow_succ]
      rw [e]
      rw [mul_smul] at h1
      exact h1
  have hall : ∀ i : ℕ, i ≤ m → ∀ a : A, α ^ p ^ (m - i) • (a • F) = a • F := by
    intro i
    induction i with
    | zero =>
      intro _ a
      simp [hα]
    | succ i ih =>
      intro hi
      refine step (m - (i + 1)) ?_
      have e : m - (i + 1) + 1 = m - i := by omega
      rw [e]
      exact ih (by omega)
  have := hall m le_rfl a
  simpa using this

theorem commutator_mem_of_three_point_pElement (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hE : ∀ a b : A, a • F = F → b • F = F → (∃ k : ℕ, b ^ p ^ k = 1) → ⁅a, b⁆ ∈ N)
    {α : A} {m : ℕ} (hα : α ^ p ^ m = 1) (γ : A) : ⁅γ, α⁆ ∈ N := by
  classical
  have hfix : ∀ a : A, α • (a • F) = a • F := fun a =>
    smul_eq_of_pElement hO hp hp5 hα a
  have hstab : ∀ a γ : A, γ • (a • F) = a • F → ⁅γ, α⁆ ∈ N := by
    intro a γ hγ
    have h1 : (a⁻¹ * γ * a) • F = F := by
      calc (a⁻¹ * γ * a) • F = a⁻¹ • (γ • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hγ]
        _ = F := inv_smul_smul a F
    have h2 : (a⁻¹ * α * a) • F = F := by
      calc (a⁻¹ * α * a) • F = a⁻¹ • (α • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hfix a]
        _ = F := inv_smul_smul a F
    have h2' : ∃ k : ℕ, (a⁻¹ * α * a) ^ p ^ k = 1 := by
      refine ⟨m, ?_⟩
      have := conj_pow (a := a⁻¹) (b := α) (i := p ^ m)
      rw [inv_inv] at this
      rw [this, hα]
      simp
    have h3 := hE _ _ h1 h2 h2'
    have e : ⁅a⁻¹ * γ * a, a⁻¹ * α * a⁆ = a⁻¹ * ⁅γ, α⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e] at h3
    have h4 := Subgroup.Normal.conj_mem ‹N.Normal› _ h3 a
    have e2 : a * (a⁻¹ * ⁅γ, α⁆ * a) * a⁻¹ = ⁅γ, α⁆ := by group
    rwa [e2] at h4
  set S := commModSubgroup N α with hS
  have hSstab : ∀ a γ : A, γ • (a • F) = a • F → γ ∈ S := fun a γ h => hstab a γ h
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  have hz : ∀ γ₁ : A, γ₁ • F = y → ∃ s ∈ S, s • F = z := by
    intro γ₁ hγ₁
    have hκ₁ : (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • F := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • (κ • F) := by simp [mul_smul]
        _ = γ₁ • F := by rw [hκF]
    refine ⟨γ₁ * κ * γ₁⁻¹, hSstab γ₁ _ hκ₁, ?_⟩
    have hu : γ₁ • y = F ∨ γ₁ • y = y ∨ γ₁ • y = z := by
      have := hO (γ₁ * γ₁)
      rwa [mul_smul, hγ₁] at this
    have hv : γ₁ • z = F ∨ γ₁ • z = y ∨ γ₁ • z = z := by
      have := hO (γ₁ * (κ * γ₁))
      rwa [mul_smul, mul_smul, hγ₁, hκy] at this
    have hu_y : γ₁ • y ≠ y := fun h =>
      hFy (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have hv_y : γ₁ • z ≠ y := fun h =>
      hFz (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have huv : γ₁ • y ≠ γ₁ • z := fun h => hyz (smul_left_cancel γ₁ h)
    have hκu : (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • z := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • (κ • y) := by simp [mul_smul]
        _ = γ₁ • z := by rw [hκy]
    have hκv : (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • y := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • (κ • z) := by simp [mul_smul]
        _ = γ₁ • y := by rw [hκz]
    rcases hu with hu | hu | hu
    · have hvz : γ₁ • z = z := by
        rcases hv with hv | hv | hv
        · exact absurd (hu.trans hv.symm) huv
        · exact absurd hv hv_y
        · exact hv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) := by rw [hu]
        _ = γ₁ • z := hκu
        _ = z := hvz
    · exact absurd hu hu_y
    · have hvF : γ₁ • z = F := by
        rcases hv with hv | hv | hv
        · exact hv
        · exact absurd hv hv_y
        · exact absurd (hu.trans hv.symm) huv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) := by rw [hvF]
        _ = γ₁ • y := hκv
        _ = z := hu
  have hκS : κ ∈ S := hSstab 1 κ (by simpa using hκF)
  rcases hO γ with h | h | h
  · exact hSstab 1 γ (by simpa using h)
  · obtain ⟨s, hs, hsF⟩ := hz γ h
    have hksF : (κ * s) • F = y := by rw [mul_smul, hsF, hκz]
    have h1 : ((κ * s)⁻¹ * γ) • F = F := by
      calc ((κ * s)⁻¹ * γ) • F = (κ * s)⁻¹ • (γ • F) := mul_smul _ _ _
        _ = (κ * s)⁻¹ • ((κ * s) • F) := by rw [h, hksF]
        _ = F := inv_smul_smul _ _
    have h2 : (κ * s)⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem (S.mul_mem hκS hs) h2
    have e3 : κ * s * ((κ * s)⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3
  · obtain ⟨s, hs, hsF⟩ := hz (κ * γ) (by rw [mul_smul, h, hκz])
    have h1 : (s⁻¹ * γ) • F = F := by
      calc (s⁻¹ * γ) • F = s⁻¹ • (γ • F) := mul_smul _ _ _
        _ = s⁻¹ • (s • F) := by rw [h, hsF]
        _ = F := inv_smul_smul _ _
    have h2 : s⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem hs h2
    have e3 : s * (s⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3

end CFSG.LocalAnalysis.RankFourTheoremC
