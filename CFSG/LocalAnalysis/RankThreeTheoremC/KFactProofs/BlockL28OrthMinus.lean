module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28NormalSection
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinusBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinusTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem kFactCompParabL28RankOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabL28RankOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD N hNP hPN d ψ hd hψ
  obtain ⟨dI, hdI, ⟨e⟩⟩ := id hD
  obtain ⟨K, _, _, _, b, c, r, s, dc, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  obtain ⟨f, hK⟩ := orthMinus_card_eq_two_pow (K := K)
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ.toMonoidHom)
      (orthMinusBlockOrders (2 ^ f)) := by
    rw [hρ, ← hK]
    exact hasLeviBlocks_orthParab hcuts hr hirr
  have h504 := card_mem_of_l28Section hCP.parab.1 ρ.toMonoidHom ρ.surjective hQ hNP hPN ψ hd hψ
  have hunits : Nat.card Kˣ = 7 := by
    rw [Nat.card_units, hK, minusTwoPow_eq_eight_of_mem h504]
  have hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L) :=
    not_dvd_card_center_rest hZ hCP.comp hCP.odd (Or.inr (Or.inr (Or.inl hD)))
      (by norm_num) (by norm_num)
  set φ : (Fin 2 → Kˣ) →* Y := L.subtype.comp (ρ.toMonoidHom.comp
    ((orthParab r (minusTailForm K b c) dc).subtype.comp
      (minusParabTorus b c 2 (by omega) (by omega)))) with hφ
  refine l28_E_of_torus_of_not_dvd hunits hZ7 φ ?_ ?_
  · exact (L.subtype_injective.comp (ρ.injective.comp Subtype.val_injective)).comp
      (minusParabTorus_injective b c 2 (by omega) (by omega))
  · rintro _ ⟨t, rfl⟩
    exact (ρ _).2

theorem kFactCompParabL28TwoRankOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabL28TwoRankOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  obtain ⟨dI, hdI, ⟨e⟩⟩ := id hD
  obtain ⟨K, _, _, _, b, c, r, s, dc, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  obtain ⟨β, hker, hpi, hcomm⟩ := minus_exists_levi_data ρ hρ hcuts hr hirr
  obtain ⟨j₁, j₂, hne, hq₁, hq₂, hc₁, hc₂⟩ := two_blocks_of_l28Section hCP.parab.1
    ρ.toMonoidHom ρ.surjective β hker hpi hcomm (isQuasisimple_or_isSolvable_orthLeviBlock hirr)
    hNP hPN ψ hd₁ hd₂ hψ
  obtain ⟨h8, h4⟩ := minus_card_eq_eight_and_four_le hcuts hirr hne ⟨hq₁, hc₁⟩ ⟨hq₂, hc₂⟩
  exact minus_three_le_pRank ρ h8 h4

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
