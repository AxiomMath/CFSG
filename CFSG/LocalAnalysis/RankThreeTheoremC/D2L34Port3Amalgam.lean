module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaCoreFree
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaConf3_false
    (hglob : AGLGlobal G) (hD1 : D1At G 3) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hAll : D2L34AllResidue3 P M) (hstr : GLBStronglyEmbedded 3 M)
    (hMS : ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧ Nat.card Q = 3 ∧
      IsS3Parabolic U (U ⊔ Q) ∧ ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H) : False := by
  obtain ⟨U, Q, hU, hQM, hQ3, hQpar, hQconj⟩ := hMS
  obtain ⟨Y, hYH, hYM, hY3, hYpar⟩ := d2L34BetaHPara3 hc hU
  have hcore := d2L34BetaCoreFree3 (U := U) hglob hD1 hc hstr hAll.onlyL34At hYH hYM hY3 hQM hQ3
    hQconj
  have hWM : (primeComplementCore (G := H) 3).map H.subtype ≤ M := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hc.esc.primeComplementCore_le_inf hw)).2
  have hT₀M : pCoreOf 2 (H ⊓ M) ≤ M :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right
  have hUM : U ≤ M := hU.2.2.1.trans (sup_le hWM hT₀M)
  have hmeet : (U ⊔ Y) ⊓ (U ⊔ Q) = U := by
    rcases hYpar.eq_or_eq (le_inf le_sup_left le_sup_left) inf_le_left with h | h
    · exact h
    · exfalso
      apply hYM
      have hle : U ⊔ Y ≤ U ⊔ Q := h ▸ inf_le_right
      exact le_sup_right.trans (hle.trans (sup_le hUM hQM))
  have hpair : F6.IsGoldschmidtVPair (U ⊔ Y) (U ⊔ Q) :=
    ⟨hYpar.2, hQpar.2, by rw [hmeet]; exact hYpar.1, by rw [hmeet]; exact hQpar.1, hcore⟩
  have hgold := card_inf_le_two_pow_seven_of_vPair hpair
  rw [hmeet] at hgold
  have hS := hc.esc.two_pow_eight_le_card_twoCore_of_l34 hglob hc.l34 hc.iso hc.le_K
  have hSU : Nat.card (pCoreOf 2 H) ≤ Nat.card U := Subgroup.card_le_of_le hU.2.1
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
