module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem conj_t_ne_z₁ (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    (g : X) : g * t * g⁻¹ ≠ z₁ := by
  intro hg
  obtain ⟨hfus, ⟨g', hg'⟩, -⟩ := hD.fd.fusion hnβ
  have hmem : (g'⁻¹ * g) * t * (g'⁻¹ * g)⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rw [show (g'⁻¹ * g) * t * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * t * g⁻¹) * g' by group, hg, ← hg',
      show g'⁻¹ * (g' * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g'⁻¹) * g' =
        t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) by group]
    exact mul_mem (subset_closure (by simp)) (Standing.Setup42.beta_mem_X i j)
  have heq : (g'⁻¹ * g) * t * (g'⁻¹ * g)⁻¹ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    rw [show (g'⁻¹ * g) * t * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * t * g⁻¹) * g' by group, hg, ← hg']
    group
  rcases hfus _ hmem with h1 | h1 <;> rw [heq] at h1
  · exact hD.hs.beta.ne_one (by simpa using h1)
  · exact hD.hs.setup.beta_ne_z hD.hs.beta (by simpa using h1)

theorem z₁_conj_t : z₁ * t * z₁⁻¹ = t * z := by
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hD.z₁_mul_z₁
  have htz : t * z = z * t :=
    hD.hs.setup.X_comm (subset_closure (by simp)) (subset_closure (by simp))
  rw [htz, hD.fd.z_eq, hz₁i]
  group

theorem exists_conj_x (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    ∃ (g : X) (i' j' : ℕ), g * t * g⁻¹ = α ∧
      g * (w ^ (orderOf w / 2) * t ^ i' * z ^ j') * g⁻¹ = z₁ ∧
      S.map (MulAut.conj g).toMonoidHom = 𝒱 ⊓ centralizer {α} ∧
      (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom =
        closure {α, z₁, t * z₁ * t⁻¹} := by
  obtain ⟨g, hgα, hgS, hgX⟩ := hD.fd.α_conj
  have hz₁X : z₁ ∈ (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom := by
    rw [hgX]
    exact subset_closure (by simp)
  obtain ⟨x, hxX, hxz⟩ := hz₁X
  have hxz' : g * x * g⁻¹ = z₁ := hxz
  have hxD : x ∉ zpowers t ⊔ (S ⊓ L) := by
    intro hxD
    obtain ⟨a, c, ha, hc, hac⟩ := hD.hs.setup.mem_X_tD hxX hxD
    rw [hac] at hxz'
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hxz'
    · apply hD.z₁_ne_one
      rw [← hxz']
      group
    · apply hD.fd.not_conj_z g⁻¹
      rw [← hxz']
      group
    · exact hD.conj_t_ne_z₁ hnβ g (by rw [← hxz', mul_one])
    · apply hD.conj_t_ne_z₁ hnβ (g * z₁)
      rw [show g * z₁ * t * (g * z₁)⁻¹ = g * (z₁ * t * z₁⁻¹) * g⁻¹ by group,
        hD.z₁_conj_t, hxz']
  obtain ⟨i', j', rfl⟩ := hD.hs.setup.mem_X_not_tD hxX hxD
  exact ⟨g, i', j', hgα, hxz', hgS, hgX⟩

end Data415B

end CFSG.ComponentClassification.HarrisLit
