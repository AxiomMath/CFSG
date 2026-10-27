module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2LaProj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2LaFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2UniEigen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2UniHerm

public section

open scoped Matrix

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_psu_la {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (hK : (2 : K) ≠ 0)
    {n : ℕ} (hn : 4 < n) (a₁ b₁ a₂ b₂ : Matrix (Fin n) (Fin n) K) (ha₁ : a₁ * a₁ = 1)
    (hb₁ : b₁ * b₁ = 1) (ha₂ : a₂ * a₂ = 1) (hb₂ : b₂ * b₂ = 1)
    (hu₁ : (a₁.map σ)ᵀ * a₁ = 1) (hv₁ : (b₁.map σ)ᵀ * b₁ = 1)
    (hu₂ : (a₂.map σ)ᵀ * a₂ = 1) (hv₂ : (b₂.map σ)ᵀ * b₂ = 1)
    (h₁ : a₁ * b₁ = -(b₁ * a₁)) (h₂ : a₂ * b₂ = -(b₂ * a₂)) (h₁₂ : a₁ * a₂ = a₂ * a₁)
    (h₁₂' : a₁ * b₂ = b₂ * a₁) (h₂₁ : b₁ * a₂ = a₂ * b₁) (hbb : b₁ * b₂ = b₂ * b₁) :
    ∃ g : Matrix (Fin n) (Fin n) K, g * g = 1 ∧ g.det = 1 ∧ (g.map σ)ᵀ * g = 1 ∧
      (∀ c : K, g ≠ c • (1 : Matrix (Fin n) (Fin n) K)) ∧ g * a₁ = a₁ * g ∧ g * b₁ = b₁ * g ∧
      g * a₂ = a₂ * g ∧ g * b₂ = b₂ * g := by
  have hh : ∀ a : Matrix (Fin n) (Fin n) K, a * a = 1 → (a.map σ)ᵀ * a = 1 →
      (a.map σ)ᵀ = a := by
    intro a ha hu
    calc (a.map σ)ᵀ = (a.map σ)ᵀ * (a * a) := by rw [ha, Matrix.mul_one]
      _ = ((a.map σ)ᵀ * a) * a := by rw [Matrix.mul_assoc]
      _ = a := by rw [hu, Matrix.one_mul]
  obtain ⟨e₁, e₂, c, w, he₁, he₂, hc, hw₁, hw₂, hψ₁, hψ₂, hψw⟩ :=
    l2_uni_eigen σ hσ hK (by omega) a₁ a₂ ha₁ ha₂ (hh a₁ ha₁ hu₁) (hh a₂ ha₂ hu₂) h₁₂
  obtain ⟨U, Φ, hΦU, hUa₁, hUb₁, hUa₂, hUb₂, hP⟩ :=
    l2_la_frame hK a₁ b₁ a₂ b₂ hb₁ hb₂ h₁ h₂ h₁₂ h₁₂' h₂₁ hbb he₁ he₂ hw₁ hw₂ hψ₁ hψ₂ hψw
  obtain ⟨hg2, hdet, hns⟩ := l2_la_proj hK hn U Φ hΦU
  have hH : ((U * Φ).map σ)ᵀ = U * Φ := by
    rw [hP]
    exact l2_uni_herm σ hσ b₁ b₂ (hh b₁ hb₁ hv₁) (hh b₂ hb₂ hv₂) hbb w c hc
  have hgH : ((1 - (2 : K) • (U * Φ)).map σ)ᵀ = 1 - (2 : K) • (U * Φ) := by
    have h2 : σ (2 : K) = 2 := map_ofNat σ 2
    rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_sub,
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one,
      Matrix.map_smulₛₗ σ σ (2 : K) (fun a => map_mul σ 2 a), Matrix.transpose_smul, h2, hH]
  have hcomm : ∀ a : Matrix (Fin n) (Fin n) K, U * Φ * a = a * (U * Φ) →
      (1 - (2 : K) • (U * Φ)) * a = a * (1 - (2 : K) • (U * Φ)) := by
    intro a ha
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, ha]
  exact ⟨1 - (2 : K) • (U * Φ), hg2, hdet, by rw [hgH]; exact hg2, hns, hcomm a₁ hUa₁,
    hcomm b₁ hUb₁, hcomm a₂ hUa₂, hcomm b₂ hUb₂⟩

end CFSG.OddStandard.HigherRank.YamadaG23
