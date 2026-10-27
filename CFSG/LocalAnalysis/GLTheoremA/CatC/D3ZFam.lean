module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZDiag
public import CFSG.HardMathSupport.Timmesfeld.DFour.TrialityFix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117K2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZW

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Abstract

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem orbit_three (F A B : Ω) (t : G) (ht1 : t • F ≠ F) (ht2 : (t ^ 2) • F ≠ F)
    (h12 : t • F ≠ (t ^ 2) • F) (hO : ∀ α : G, α • F = F ∨ α • F = A ∨ α • F = B) :
    ∀ α : G, α • F = F ∨ α • F = t • F ∨ α • F = (t ^ 2) • F := by
  intro α
  rcases hO α with h | h | h
  · exact Or.inl h
  · rcases hO t with h1 | h1 | h1
    · exact absurd h1 ht1
    · exact Or.inr (Or.inl (h.trans h1.symm))
    · rcases hO (t ^ 2) with h2 | h2 | h2
      · exact absurd h2 ht2
      · exact Or.inr (Or.inr (h.trans h2.symm))
      · exact absurd (h1.trans h2.symm) h12
  · rcases hO t with h1 | h1 | h1
    · exact absurd h1 ht1
    · rcases hO (t ^ 2) with h2 | h2 | h2
      · exact absurd h2 ht2
      · exact absurd (h1.trans h2.symm) h12
      · exact Or.inr (Or.inr (h.trans h2.symm))
    · exact Or.inr (Or.inl (h.trans h1.symm))

theorem fam_trivial (F : Ω) (t : G) (ht3 : t ^ 3 = 1) (ht1 : t • F ≠ F) (ht2 : (t ^ 2) • F ≠ F)
    (h12 : t • F ≠ (t ^ 2) • F)
    (hO : ∀ α : G, α • F = F ∨ α • F = t • F ∨ α • F = (t ^ 2) • F)
    (Z : Subgroup G) (hZ : ∀ γ ∈ Z, ∀ α : G, γ • (α • F) = α • F)
    (D : Set G) (hD2 : ∀ δ ∈ D, δ * δ ∈ Z) (hDm : ∀ δ ∈ D, ∀ δ' ∈ D, δ * δ' ∈ D)
    (hDt : ∀ δ ∈ D, t * δ * t⁻¹ ∈ D) : ∀ δ ∈ D, δ • F = F := by
  intro δ hδ
  by_contra hne
  have e2 : t • (t • F) = (t ^ 2) • F := by rw [← mul_smul, pow_two]
  have e3 : t • ((t ^ 2) • F) = F := by rw [← mul_smul, ← pow_succ', ht3, one_smul]
  have e1' : t⁻¹ • F = (t ^ 2) • F := by
    rw [inv_smul_eq_iff]; exact e3.symm
  have e3' : t⁻¹ • (t • F) = F := by rw [inv_smul_smul]
  have hsq : ∀ δ' ∈ D, ∀ α : G, δ' • (δ' • (α • F)) = α • F := fun δ' hδ' α => by
    rw [← mul_smul]; exact hZ _ (hD2 δ' hδ') α
  have hδ2 : δ • (δ • F) = F := by simpa using hsq δ hδ 1
  have hF3 : δ • ((t ^ 2) • F) = F ∨ δ • ((t ^ 2) • F) = t • F ∨ δ • ((t ^ 2) • F) = (t ^ 2) • F := by
    have := hO (δ * t ^ 2)
    rwa [mul_smul] at this
  have hF2 : δ • (t • F) = F ∨ δ • (t • F) = t • F ∨ δ • (t • F) = (t ^ 2) • F := by
    have := hO (δ * t)
    rwa [mul_smul] at this
  rcases hO δ with h | h | h
  · exact hne h
  ·
    have a2 : δ • (t • F) = F := by rw [← h]; exact hδ2
    have a3 : δ • ((t ^ 2) • F) = (t ^ 2) • F := by
      rcases hF3 with h3 | h3 | h3
      · exfalso
        apply h12
        apply MulAction.injective δ
        show δ • (t • F) = δ • ((t ^ 2) • F)
        rw [a2, h3]
      · exfalso
        apply ht2
        apply MulAction.injective δ
        show δ • ((t ^ 2) • F) = δ • F
        rw [h3, h]
      · exact h3
    have hδ' := hDt δ hδ
    have hprod := hDm δ hδ _ hδ'
    have p1 : (t * δ * t⁻¹) • F = F := by
      rw [mul_smul, mul_smul, e1', a3, e3]
    have p2 : (δ * (t * δ * t⁻¹)) • F = t • F := by
      rw [mul_smul, p1, h]
    have p3 : (t * δ * t⁻¹) • (t • F) = (t ^ 2) • F := by
      rw [mul_smul, mul_smul, e3', h, e2]
    have p4 : (δ * (t * δ * t⁻¹)) • (t • F) = (t ^ 2) • F := by
      rw [mul_smul, p3, a3]
    have := hZ _ (hD2 _ hprod) 1
    rw [one_smul, mul_smul, p2, p4] at this
    exact ht2 this
  ·
    have a3 : δ • ((t ^ 2) • F) = F := by rw [← h]; exact hδ2
    have a2 : δ • (t • F) = t • F := by
      rcases hF2 with h3 | h3 | h3
      · exfalso
        apply h12
        apply MulAction.injective δ
        show δ • (t • F) = δ • ((t ^ 2) • F)
        rw [h3, a3]
      · exact h3
      · exfalso
        apply ht1
        apply MulAction.injective δ
        show δ • (t • F) = δ • F
        rw [h3, h]
    have hδ' := hDt δ hδ
    have hprod := hDm δ hδ _ hδ'
    have p1 : (t * δ * t⁻¹) • F = t • F := by
      rw [mul_smul, mul_smul, e1', a3]
    have p2 : (δ * (t * δ * t⁻¹)) • F = t • F := by
      rw [mul_smul, p1, a2]
    have p3 : (t * δ * t⁻¹) • (t • F) = F := by
      rw [mul_smul, mul_smul, e3', h, e3]
    have p4 : (δ * (t * δ * t⁻¹)) • (t • F) = (t ^ 2) • F := by
      rw [mul_smul, p3, h]
    have := hZ _ (hD2 _ hprod) 1
    rw [one_smul, mul_smul, p2, p4] at this
    exact ht2 this

end Abstract

end CFSG.LocalAnalysis.GLTheoremA
