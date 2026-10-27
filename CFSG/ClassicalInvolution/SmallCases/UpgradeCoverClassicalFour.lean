module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_statedScalars statedProjCongr glCongr_statedSL glCongr_statedSp glCongr_statedSU)

theorem statedClassicalModel_unique_four {X Y : Type} [Group X] [Group Y]
    {t : CFSG.Open.StatedLieTag} {n r e : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus)
    (hX : CFSG.Open.StatedClassicalModel X t n r e)
    (hY : CFSG.Open.StatedClassicalModel Y t n r e) :
    Nonempty (X ≃* Y) := by
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSL φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSU φ n (r ^ e))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSp φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (map_statedOmega φ (statedQuadPlus_comp φ))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩

end CFSG.ClassicalInvolution.Upgrade
