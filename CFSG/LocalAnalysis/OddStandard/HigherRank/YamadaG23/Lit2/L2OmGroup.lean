module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmImages
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmPigeon
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Sylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2_om_group {E H S Ω : Type} [Group E] [Finite E] [Group H] [Group S] [Finite S]
    [Group Ω] [Finite Ω]
    (α : E →* H) (hα : Function.Surjective α) (ρ : H →* S) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = center H) (hH2 : IsPGroup 2 ↥(center H)) {A : Subgroup S}
    (hE : IsE 4 ↥A) (hP : L2Pauli ρ A) {ζ : E} (hζk : ζ ∈ (ρ.comp α).ker)
    (hζ4 : orderOf ζ = 4) (hζg : ∀ u ∈ (ρ.comp α).ker, ∃ k : ℕ, u = ζ ^ k)
    (hcen : ∀ u ∈ (ρ.comp α).ker, ∀ x : E, u * x = x * u)
    (π : Ω →* S) (hπ2 : ∀ u ∈ π.ker, u * u = 1) (hπcen : ∀ u ∈ π.ker, ∀ w : Ω, u * w = w * u)
    (hπk : Nat.card π.ker ≤ 2) (θ : E →* Ω) (hθ : π.comp θ = ρ.comp α)
    (hsyl : IsSylowIn 2 (centIn ⊤ A) A)
    (hKL : ∀ y : Fin 4 → Ω, (∀ i, y i * y i = 1) → (∀ i j, y i * y j = y j * y i) →
      ∃ D : Finset Ω, 33 ≤ D.card ∧ ∀ d ∈ D, d * d = 1 ∧ ∀ i, y i * d = d * y i) :
    False := by
  obtain ⟨y, hy2, hyc, hyd⟩ :=
    l2_om_images α hα ρ hρs hρk hH2 hE hP hζk hζ4 hζg hcen π hπ2 hπcen θ hθ
  obtain ⟨D, hD, hDp⟩ := hKL y hy2 hyc
  obtain ⟨d, hdD, hdA⟩ := l2_om_pigeon π hπk (A := A) (by rw [hE.2]; norm_num) D hD
  have hg2 : π d * π d = 1 := by
    rw [← map_mul, (hDp d hdD).1, map_one]
  have hgc : ∀ a ∈ A, a * π d = π d * a :=
    fun a ha => hyd d (fun i => (hDp d hdD).2 i) a ha
  exact l2_not_sylow_of_extra hgc hdA hg2 hsyl

end CFSG.OddStandard.HigherRank.YamadaG23
