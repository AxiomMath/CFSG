module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinTorus
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LeviBlock

theorem range_comp_flagStabilizer {Y : Type} [Group Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Field K] {n : ℕ} {I : Set ℕ}
    (ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L) (hρ : Function.Surjective ρ)
    (hcomap : (P.subgroupOf L).comap ρ = LinearFlag.flagStabilizer n K I) :
    (L.subtype.comp (ρ.comp (LinearFlag.flagStabilizer n K I).subtype)).range = P := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    have hq : (q : Matrix.SpecialLinearGroup (Fin n) K) ∈ (P.subgroupOf L).comap ρ := by
      rw [hcomap]
      exact q.2
    exact Subgroup.mem_subgroupOf.mp hq
  · intro p hp
    obtain ⟨k, hk⟩ := hρ ⟨p, hPL hp⟩
    have hkQ : k ∈ LinearFlag.flagStabilizer n K I := by
      rw [← hcomap, Subgroup.mem_comap, hk]
      exact Subgroup.mem_subgroupOf.mpr hp
    exact ⟨⟨k, hkQ⟩, by simp [hk]⟩

theorem kFactCompParabThreeFivesOn_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabThreeFivesOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA O J _ hPO _ hsec hJ hJc
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, hker, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 := three_le_card_fiveBlocks _ (range_comp_flagStabilizer hCP.parab.1 ρ hρs hcomap)
    (linLeviHom (GaloisField 2 f) n I) (isPGroup_ker_linLeviHom (by omega))
    pi_le_range_linLeviHom commutator_range_linLeviHom_le
    (isQuasisimple_or_isSolvable_linBlockSL I)
    (fun a hq h60 => card_linBlockSL_of_sixty hK hq h60) hPO hsec hJ hJc
  exact four_le_pRank_of_three_sixty_blocks hK ρ hker hcomap h3

end CFSG.AGLEmbedding
