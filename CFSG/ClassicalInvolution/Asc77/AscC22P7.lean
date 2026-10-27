module

public import CFSG.ClassicalInvolution.Asc77.AscC22P6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace C22P

set_option linter.unusedSectionVars false

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem chain_of_alpha (hodd : T7Z.OddCenterClassical) (hq1 : p ^ f % 4 = 1)
    (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W)
    (hL : LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f))
    (hG : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) :
    ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤ := by
  classical
  have hπ : piSign p f = true := by simp [piSign, hq1]
  rw [hπ] at hL
  have hp2 : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨K₄, hK₄, h41, h42, h43, hV⟩ := fourTwins_S hs hW
  obtain ⟨R, R', b, b', y, hFd⟩ := (frame_at hs hK₄ h41 h42 h43 hW).exists_data
  obtain ⟨hex, hP1, hK₄le, hgen1⟩ := layer1 hodd hs hα hL hK₄ h41 h42 h43 hFd
  obtain ⟨hPK, hPK', hJ'le, hgen2⟩ := layer2 hodd hs hex hπ hα hK₄ h41 h42 h43 hV hFd hP1
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  have cKK' : Commutes K K' := commutes_of_twins hs.stand hz hKV hs.hK' hs.hne.symm hex
  have cKK₃ : Commutes K K₃ := commutes_of_twins hs.stand hz hKV hs.hK₃ hs.hK₃K.symm hex
  have cK'K₃ : Commutes K' K₃ := commutes_of_twins hs.stand hz hs.hK' hs.hK₃ hs.hK₃K'.symm hex
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hs.hK₃.1
  refine ⟨![K, conjSub y K₃, K', K₃], ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact hKΩ
    · exact hJΩ
    · exact hs.hK'.1
    · exact hs.hK₃.1
  · intro i j hij hn1 hn2
    fin_cases i <;> fin_cases j <;> simp [edgeD] at hij hn1 hn2 ⊢
    · exact cKK'
    · exact cKK₃
    · exact cKK'.symm
    · exact cK'K₃
    · exact cKK₃.symm
    · exact cK'K₃.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeD] at hij ⊢
    · exact hPK
    · obtain ⟨W, hW⟩ := hPK'
      exact ⟨W, linearBlockStandardPair_symm hW⟩
    · obtain ⟨W, hW⟩ := hP1
      exact ⟨W, linearBlockStandardPair_symm hW⟩
  · have hH : ∀ k : Fin 4, ![K, conjSub y K₃, K', K₃] k ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k :=
      fun k => le_iSup (fun k => ![K, conjSub y K₃, K', K₃] k) k
    have hKH : K ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 0
    have hJH : conjSub y K₃ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 1
    have hK'H : K' ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 2
    have hK₃H : K₃ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 3
    have hY' : exactLayer Ω (b * b') ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := by
      rw [hgen2]
      exact sup_le (sup_le hK'H hJH) hKH
    have hJ'H : conjSub y K₄ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hJ'le.trans hY'
    have hY : exactLayer Ω (u₁ * u₂) ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := by
      rw [hgen1]
      exact sup_le (sup_le hJ'H hK₃H) hJH
    have hK₄H : K₄ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hK₄le.trans hY
    refine top_le_iff.mp ?_
    rw [← hG]
    refine sup_le (iSup₂_le fun M hM => ?_) ?_
    · rcases hV M hM with h | h | h | h <;> rw [h]
      · exact hKH
      · exact hK'H
      · exact hK₃H
      · exact hK₄H
    · rw [rLayer_eq_exactLayer hp2 hq hΩ hs.sq_12]
      exact hY

end Chain

end C22P

end CFSG.ClassicalInvolution.Asc77
