module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Model
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdMain

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.Timmesfeld (edgeE)
open CFSG.LieType CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable (p f : ℕ) [Fact p.Prime]

noncomputable abbrev Rθ : Subgroup (K7 p f) :=
  (D7 p f).rootGroup CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7 ⊔
    (D7 p f).rootGroup (-CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7)

noncomputable abbrev T7 (j : Fin 7) : Subgroup (K7 p f) :=
  Steinberg.Minuscule.e7Data_valid.torus (GaloisField p f) j

@[expose] def E7A1A4Frame : Prop :=
  ∀ (C : Fin 4 → Subgroup (K7 p f)) (RM : Subgroup (K7 p f)), (∀ i, C i ∈ F7 p f) → RM ∈ F7 p f →
    (∀ i j : Fin 4, i.val + 1 = j.val →
      Gaps.ModelAdj (Subgroup.center (K7 p f)) (C i) (C j) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (C i) (C j)) →
    (∀ i j : Fin 4, i.val + 2 ≤ j.val → Commutes (C i) (C j)) → (∀ i, Commutes RM (C i)) →
    ∃ g : K7 p f, RM = conjSub g (Rθ p f) ∧
      ∀ i, C i = conjSub g (rankOne (D7 p f).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) i))

@[expose] def E7A1A4Toral : Prop :=
  ∀ (Y : Type) [Group Y] (ψ : K7 p f →* Y), ψ.ker ≤ Subgroup.center (K7 p f) →
    ∀ σ : Y ≃* Y, (∀ y, σ (σ y) = y) → (∀ k, σ (ψ k) ∈ ψ.range) → ∀ k₀ : K7 p f,
      (∀ y ∈ Rθ p f, σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) →
      (∀ i : Fin 4, ∀ y ∈ rankOne (D7 p f).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) i),
        σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) →
      ∀ j : Fin 7, j ≠ 0 → ∀ h ∈ T7 p f j,
        σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹)

@[expose] def E7TorusFixedModel : Prop :=
  ∀ (Y : Type) [Group Y] (ψ : K7 p f →* Y), ψ.ker ≤ Subgroup.center (K7 p f) →
    ∀ σ : Y ≃* Y, (∀ y, σ (σ y) = y) → (∀ k, σ (ψ k) ∈ ψ.range) →
    ∀ (C : Fin 4 → Subgroup (K7 p f)) (RM : Subgroup (K7 p f)), (∀ i, C i ∈ F7 p f) → RM ∈ F7 p f →
      (∀ i j : Fin 4, i.val + 1 = j.val →
        Gaps.ModelAdj (Subgroup.center (K7 p f)) (C i) (C j) ∧
          ∃ W, LinearBlockStandardPair (GaloisField p f) W (C i) (C j)) →
      (∀ i j : Fin 4, i.val + 2 ≤ j.val → Commutes (C i) (C j)) → (∀ i, Commutes RM (C i)) →
      (∀ i, ∀ y ∈ C i, σ (ψ y) = ψ y) → (∀ y ∈ RM, σ (ψ y) = ψ y) →
      ∃ k₀ : K7 p f, RM = conjSub k₀ (Rθ p f) ∧
        ∀ j : Fin 7, j ≠ 0 → ∀ h ∈ T7 p f j,
          σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹)

theorem e7TorusFixedModel_of_frame_toral (hF : E7A1A4Frame p f) (hT : E7A1A4Toral p f) :
    E7TorusFixedModel p f := by
  unfold E7TorusFixedModel
  intro Y _ ψ hψ σ hσ2 hσr C RM hC hRM hadj hcomm hRMC hfixC hfixM
  obtain ⟨g, hg, hCg⟩ := hF C RM hC hRM hadj hcomm hRMC
  refine ⟨g, hg, hT Y ψ hψ σ hσ2 hσr g (fun y hy => ?_) (fun i y hy => ?_)⟩
  · exact hfixM _ (hg ▸ conj_mem_conjSub hy)
  · exact hfixC i _ (hCg i ▸ conj_mem_conjSub hy)

end CFSG.ClassicalInvolution.RouteD.TypeE8
