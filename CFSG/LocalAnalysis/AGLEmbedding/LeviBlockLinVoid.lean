module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem u38_not_mem_linBlockOrders {f : ℕ} (hf : 1 ≤ f) :
    5515776 ∉ linBlockOrders (GaloisField 2 f) := by
  rintro ⟨m, -, hm⟩
  rw [GaloisField.card 2 f (by omega)] at hm
  exact ordA_ne_u38 rfl hm.symm

theorem u42_not_mem_linBlockOrders {f : ℕ} (hf : 1 ≤ f) :
    25920 ∉ linBlockOrders (GaloisField 2 f) := by
  rintro ⟨m, -, hm⟩
  rw [GaloisField.card 2 f (by omega)] at hm
  exact ordA_ne_u42 rfl hm.symm

theorem kFactCompParabSU38On_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabSU38On (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, -, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  exact su38At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, _, hρs, hQ,
    u38_not_mem_linBlockOrders hf⟩

theorem kFactCompParabLeviU42On_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabLeviU42On (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, -, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  exact leviU42At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, _, hρs, hQ,
    u42_not_mem_linBlockOrders hf⟩

end CFSG.AGLEmbedding
