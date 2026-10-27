module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517I
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O82

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem row1520_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hOne : Row1520One G M T T₁ T₂) (hK7145 : K7145) (hKOut : KOut)
    (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMAlt : KSMAlt)
    (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) (h12 : Row1512 G M T T₁ T₂)
    (h15 : Row1515 G M T T₁ T₂) (h19 : Row1519 G M T T₁ T₂) : Row1520 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL
  have hp5 : 5 ≤ p := five_le_of_mem_sigmaM h11 hp
  have hpp : p.Prime := sigmaA_prime p hp.1
  obtain ⟨hlist, hU5⟩ := h12 Ls L hLs hL
  have hU5' : IsUFiveFour ↥Ls → p ≠ 5 := fun h hp5' => hU5 h (hp5' ▸ hp)
  have hZ := not_dvd_centre_barO2_of_row1512 hKSMOdd hKSMU4 hKSML3 hKSMAlt ctx.gn hLs.1 hL hpp hp5
    hlist hU5'
  have hMtop : M ≠ ⊤ := (ctx.strong p hp).1
  have hXK : CFSG.Open.IsKGroup ↥M := ctx.cstar.kProper.isKGroup M hMtop
  have hno : ∀ N : Subgroup ↥M, N.Normal → N.index ≠ p := fun N hN => by
    haveI := hN
    exact no_normal_index_p_of_ctx_gen ctx hp N
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11
  have h15' := h15 Ls L hLs hL _ rfl
  have hone := hOne p hp hp5 Ls L hLs hL
  have h3 : CFSG.Open.pRank 3 L < 3 := by
    obtain ⟨I, hI, -, -, h3I⟩ := hone
    exact pRank_three_lt_of_exists hL.1
      (fun h3' => centre_barO2_eq_bot_of_pRank_three hT hKSMOdd hKSMU4 hKSMAlt ctx.gn ctx.shape hLs hL
        hlist h3') hX3 hI h3I
  have hex : (IsSpSix (fun _ => True) ↥Ls ∨ IsOmegaEightMinus (fun _ => True) ↥Ls ∨
      IsLinTwo 6 ↥Ls ∨ IsLinTwo 7 ↥Ls ∨ Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) ∨
      IsLFour (fun Q => ¬ 3 ∣ Q + 1) ↥Ls ∨ IsUFour (fun Q => ¬ 3 ∣ Q - 1) ↥Ls) → False := by
    intro h
    have := pRank_lift_eq_three_of_excluded hT.chev hT.alt ctx.gn hLs.1 hL h
    omega
  refine ⟨hone, ?_, h3, ?_, ?_, ?_⟩
  · exact two_le_pRank_cMBar_gen hK7145 hKOut hXK hpp hp5 hL.1 (ctx.three_le p hp)
      (h19 p hp Ls L hLs hL) hZ hno h15'
  · rintro (h | h | h | h | h)
    · exact hex (Or.inl h)
    · exact hex (Or.inr (Or.inl h))
    · exact hex (Or.inr (Or.inr (Or.inl h)))
    · exact hex (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact fun h => hex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact fun h => hex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem row1520 {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hOne : Row1520One G M T T₁ T₂) (hK7145 : K7145) (hKOut : KOut)
    (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMAlt : KSMAlt)
    (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) (h12 : Row1512 G M T T₁ T₂)
    (h15 : Row1515 G M T T₁ T₂) (h19 : Row1519 G M T T₁ T₂) : Row1520 G M T T₁ T₂ :=
  row1520_gen hOne hK7145 hKOut hT hKSMOdd hKSMU4 hKSML3 hKSMAlt (S15CtxGen.of_ctx2 ctx) h11 h12
    h15 h19

end CFSG.LocalAnalysis.RankThreeUC.S15
