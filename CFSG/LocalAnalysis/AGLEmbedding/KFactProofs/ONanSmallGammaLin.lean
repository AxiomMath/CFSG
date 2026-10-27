module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallGamma

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34 (card_projectiveSL eZero exists_eq_map_conj_eZero)

theorem smallGammaData_of_isLinThreeFour {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K)
    (T : Sylow 3 K) : SmallGammaData K (T : Subgroup K) := by
  obtain ⟨ε₀⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK20 : Nat.card K = 20160 := by
    rw [Nat.card_congr ε₀.toEquiv]
    exact card_projectiveSL hk
  have hTcard : Nat.card (T : Subgroup K) = 9 := KFactProofs.L34Local.card_sylow_three hK20 T
  have hP₁ : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← hTcard]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hP₁
  let ε : projectiveSL 3 (GaloisField 2 2) ≃* K := (MulAut.conj g).trans ε₀.symm
  have hεT : ∀ y, y ∈ eZero (GaloisField 2 2) ↔ ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g * y * g⁻¹ ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  exact SmallGammaData.of_localData ((KFactProofs.L34Local.localData_eZero hk).map ε hεT)

end CFSG.AGLEmbedding.KFactProofs.SmallGamma
