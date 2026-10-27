module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2LaProj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2LaEigen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2LaFrame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_psl_la {K : Type} [Field K] (hK : (2 : K) ≠ 0) {n : ℕ} (hn : 4 < n)
    (a₁ b₁ a₂ b₂ : Matrix (Fin n) (Fin n) K) (ha₁ : a₁ * a₁ = 1) (hb₁ : b₁ * b₁ = 1)
    (ha₂ : a₂ * a₂ = 1) (hb₂ : b₂ * b₂ = 1) (h₁ : a₁ * b₁ = -(b₁ * a₁))
    (h₂ : a₂ * b₂ = -(b₂ * a₂)) (h₁₂ : a₁ * a₂ = a₂ * a₁) (h₁₂' : a₁ * b₂ = b₂ * a₁)
    (h₂₁ : b₁ * a₂ = a₂ * b₁) (hbb : b₁ * b₂ = b₂ * b₁) :
    ∃ g : Matrix (Fin n) (Fin n) K, g * g = 1 ∧ g.det = 1 ∧
      (∀ c : K, g ≠ c • (1 : Matrix (Fin n) (Fin n) K)) ∧ g * a₁ = a₁ * g ∧ g * b₁ = b₁ * g ∧
      g * a₂ = a₂ * g ∧ g * b₂ = b₂ * g := by
  obtain ⟨e₁, e₂, w, ψ, he₁, he₂, hw₁, hw₂, hψ₁, hψ₂, hψw⟩ :=
    l2_la_eigen hK (by omega) a₁ a₂ ha₁ ha₂ h₁₂
  obtain ⟨U, Φ, hΦU, hUa₁, hUb₁, hUa₂, hUb₂, -⟩ :=
    l2_la_frame hK a₁ b₁ a₂ b₂ hb₁ hb₂ h₁ h₂ h₁₂ h₁₂' h₂₁ hbb he₁ he₂ hw₁ hw₂ hψ₁ hψ₂ hψw
  obtain ⟨hg2, hdet, hns⟩ := l2_la_proj hK hn U Φ hΦU
  have hcomm : ∀ a : Matrix (Fin n) (Fin n) K, U * Φ * a = a * (U * Φ) →
      (1 - (2 : K) • (U * Φ)) * a = a * (1 - (2 : K) • (U * Φ)) := by
    intro a ha
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, ha]
  exact ⟨1 - (2 : K) • (U * Φ), hg2, hdet, hns, hcomm a₁ hUa₁, hcomm b₁ hUb₁, hcomm a₂ hUa₂,
    hcomm b₂ hUb₂⟩

end CFSG.OddStandard.HigherRank.YamadaG23
