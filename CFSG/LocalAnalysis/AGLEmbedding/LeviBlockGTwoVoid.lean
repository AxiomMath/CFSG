module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFivesAt
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock

public section

namespace CFSG.AGLEmbedding

open CFSG.Open


theorem hasLeviBlocks_g2 (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (f : ℕ), Function.Surjective ρ ∧
      HasLeviBlocks ↥((P.subgroupOf L).comap ρ) {ordA 1 (2 ^ f)} := by
  obtain ⟨K, _, _, ρ, G, _, _, S, β, f, hρ, hker, hpi, hcomm, hqs, hZ, hcard⟩ :=
    LeviBlock.exists_leviData_g2 hGA hCP hG
  exact ⟨K, inferInstance, inferInstance, ρ, f, hρ, 1, fun _ => G, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => S, β, hker, hpi, hcomm, fun _ => Or.inl hqs,
    fun _ _ => Set.mem_singleton_iff.2 ((LeviBlock.card_quotient_center_of_eq_bot hZ).trans hcard)⟩

theorem kFactCompParabSU38On_g2 (hGA : GriessAllModelsStatement) :
    KFactCompParabSU38On (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := hasLeviBlocks_g2 hGA hCP hG
  exact su38At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ, _, hρ, hQ,
    fun h => ordA_ne_u38 rfl (Set.mem_singleton_iff.1 h).symm⟩

theorem kFactCompParabLeviU42On_g2 (hGA : GriessAllModelsStatement) :
    KFactCompParabLeviU42On (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := hasLeviBlocks_g2 hGA hCP hG
  exact leviU42At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ, _, hρ, hQ,
    fun h => ordA_ne_u42 rfl (Set.mem_singleton_iff.1 h).symm⟩

theorem kFactCompParabThreeFivesOn_g2 (hGA : GriessAllModelsStatement) :
    KFactCompParabThreeFivesOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, G, _, _, S, β, f, hρ, hker, hpi, hcomm, hqs, hZ, -⟩ :=
    LeviBlock.exists_leviData_g2 hGA hCP hG
  exact fivesAt_of_levi hCP.parab.1 ρ hρ (G := fun _ : Fin 1 => G) (S := fun _ => S) β hker hpi
    hcomm (fun _ => Or.inl hqs)
    (fun _ _ h60 => (LeviBlock.card_quotient_center_of_eq_bot hZ).symm.trans h60)
    ((Finite.card_subtype_le _).trans (by simp))

end CFSG.AGLEmbedding
