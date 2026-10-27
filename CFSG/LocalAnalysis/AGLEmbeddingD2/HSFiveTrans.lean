module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransCase

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem d2IndexCaseAt_hs_five' (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts) (hMS : D2HeisMSide)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5) (hU : D2HSFiveNonBorel)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hMcL : D2HeisBorelAt (.sporadic .McL) fun p => p = 5)
    (hSpor : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt (.sporadic s) fun p => p = 5) :
    D2IndexCaseAt (.sporadic .HS) fun p => p = 5 := by
  intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  subst hp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBfor := d2HeisBorelFor_hs_five (A := A) hloc hU hglob hD1 hmax hβ
  have hB := hBfor H hesc Rbar K hRbar hK he
  have hRQ := hMS G hglob hD1 5 le_rfl P M A H R hesc hmax hβ Rbar K hRbar hK hB
  have hcard : Nat.card R = 5 ^ 3 := by
    rw [← hesc.card_map_eq le_rfl, ← hRbar]
    exact hB.card
  have hRexp : ∀ r ∈ R, r ^ 5 = 1 := fun r hr => by
    by_contra hr5
    exact hesc.false_of_pow_eq_one hRbar ⟨r, hr, hr5⟩ hB.pow_eq_one
  refine hesc.false_of_heisBorelFor' hrank hL3 hS hKU (fun d hd => ?_) (fun s => ?_) hCGT
    hglob.toAGLGlobal (hD1.at hβ) (hD2.noXBlockFor hglob.toD1Global) hmax le_rfl hRbar hB hRQ
  · intro H' h' Rbar' K' hRbar' hK' he'
    exfalso
    rcases hd with ⟨h53, -⟩ | ⟨-, hdt | hdz⟩
    · norm_num at h53
    · have hT := hTits d hdt _ 5 rfl Rbar' _ _ K' hK' he'
      have hcA := h'.card_A
      rw [h'.A_eq_of_map_eq (hRbar'.symm.trans hT.eq_A), hcard] at hcA
      norm_num at hcA
    · obtain ⟨zb, hB'⟩ := hSzB d hdz _ 5 rfl Rbar' _ _ K' hK' he'
      obtain ⟨b, hbR, hb⟩ := exists_pow_ne_one_of_map hRbar' hB'.exp
      exact hb (hRexp b hbR)
  · by_cases h1 : s = .HS
    · subst h1
      exact hBfor
    by_cases h2 : s = .McL
    · subst h2
      exact hMcL.for rfl
    · exact ((hSpor s h1 h2).for hglob hD1 rfl hmax hβ).heisBorelFor

end CFSG.AGLEmbeddingD2
