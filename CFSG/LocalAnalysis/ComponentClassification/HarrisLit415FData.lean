module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415FusC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2L
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma415Inputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Fusion
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Centralizer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Alpha
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem exists_fData
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput) (hD : AutPSL2RDerivedInput)
    (hI : AutPSL2InvolutionCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    ∃ (τ α : X) (K₂ 𝒱 : Subgroup X),
      Harris415FData t L S (w ^ (orderOf w / 2)) z (w ^ (orderOf w / 2) * t ^ i * z ^ j)
        z₁ τ α K₂ W 𝒱 := by
  obtain ⟨K₂, hK₂, hbar, hz₂, hmap⟩ := hc.exists_K₂
  obtain ⟨𝒱, τ, h𝒱, hW𝒱, hτ𝒱, -, hτz₁, hτz, hτβ⟩ := hc.exists_V hnab hKC hA h412
  have hstar := hc.conj_mem_of_V hnab hKC hA hD h412 h𝒱 hW𝒱 hτ𝒱 hτz hτβ
  obtain ⟨hcen, hz𝒱⟩ := hc.center_V hKC h𝒱 hW𝒱 hτ𝒱 hτz hτβ
  have hτ : τ ∈ 𝒱 ⊓ centralizer {z₁} :=
    mem_inf.mpr ⟨hτ𝒱, mem_centralizer_singleton_iff.mpr hτz₁⟩
  obtain ⟨α, g₀, hα, hg₀t, hg₀S, hg₀X⟩ := hc.exists_alpha hnab h𝒱 hW𝒱 hstar hz𝒱
  have hW₀ : 𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} =
      W ⊓ centralizer {z₁} := by
    rw [inf_right_comm, hc.inf_V_beta h𝒱 hW𝒱]
  have hV₀card : Nat.card 𝒱 = 2 * Nat.card ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) := by
    have h1 := Subgroup.relIndex_mul_card (𝒱 ⊓ centralizer ({z₁} : Set X)) 𝒱
    rw [inf_of_le_left inf_le_left, hc.relIndex_V₀ hW𝒱 hstar hz𝒱] at h1
    exact h1.symm
  have hV₀le : Nat.card ↥(𝒱 ⊓ centralizer {z₁}) ≤
      4 * Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) := by
    rw [hW₀]
    have h1 := hc.card_V_le h𝒱
    have h2 := hc.card_W₀
    omega
  refine ⟨τ, α, K₂, 𝒱, ?_⟩
  exact
    { sq_z₁ := hc.sq_z₁
      z₁_ne := hc.z₁_ne
      z_eq := hc.z_eq
      isTwoComponentIn_K₂ := hK₂
      bar_K₂ := hbar
      z₂_mem := hz₂
      layerIn_K₂ := hc.layerIn_eq_K₂ hnab hK hSch hI h412 hK₂
      isPGroup_centralizer_K₂ := hc.isPGroup_centralizer_K₂ hI h412 hmap
      isSylowOf_W := hc.isSylowOf_W
      isSylowOf_𝒱 := h𝒱
      W_le := hW𝒱
      t_mem := hW𝒱 hc.t_mem_W
      card_𝒱_le := hc.card_V_le h𝒱
      isSylowOf_𝒱₀ := hc.isSylowOf_V₀ hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hg₀X hstar
      isSylowOf_W₀ := by
        rw [hW₀]
        exact hc.isSylowOf_W₀
      card_W₀ := by
        rw [hW₀]
        exact hc.card_W₀
      card_𝒱₀_le := hV₀le
      center_𝒱₀ := hc.center_V₀ hKC h𝒱 hW𝒱 hstar hz𝒱 hτ hτβ
      τ_mem := hτ
      τ_conj := hτβ
      not_conj_z := hc.not_conj_z_of hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hg₀X
      fusion := hc.fusion_415 hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hg₀X hstar
      α_mem := hα
      α_conj := ⟨g₀, hg₀t, hg₀S, hg₀X⟩ }

end Config415

theorem harris415TwoLocalStep_of_aut
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hA : AutPSL2RCentralizerInput) (hD : AutPSL2RDerivedInput)
    (hI : AutPSL2InvolutionCentralizerInput) : Harris415TwoLocalStep := by
  intro X _ _ _ hnab hK _ t L p f S w z V i j hhyp
  obtain ⟨hs, h412, -, hnq⟩ := hhyp
  obtain ⟨Kb₁, Kb₂, W, z₁, hc⟩ := hs.exists_config415 h412 hnq
  obtain ⟨τ, α, K₂, 𝒱, hF⟩ := hc.exists_fData hnab hK hSch AutL2Facts.cfAutPSL2Fusion
    AutL2Facts.cfAutPSL2Centralizer hA hD hI h412
  exact ⟨z₁, τ, α, K₂, W, 𝒱, hF⟩

end CFSG.ComponentClassification.HarrisLit
