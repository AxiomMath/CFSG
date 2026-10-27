module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)

theorem prop95_of (h96 : Lemma96) (h97 : Lemma97) (hi : Prop95i) (hii : Prop95ii)
    (hiii : Prop95iii) (hC : Prop95IvChev) (hA : Prop95IvAlt) : Prop95 := by
  intro G _ _ m p hS M D hD
  refine ⟨hi G m p hS M D hD, hii G m p hS M D hD, fun L hL => ?_⟩
  have hn := hiii G m p hS M D hD L hL
  refine ⟨hn, ?_⟩
  by_cases hc : barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
  · exact Or.inl hc
  · right
    have hp : p.Prime := prime_of_standing hS
    have hp2 : p ≠ 2 := ne_two_of_standing hS
    have hQ : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M := h97 G m p hS M D hD
    have hcomp : IsComponentOf (tl M L) ⊤ := isComponentOf_tl hp hp2 hD hL hn hc hQ
    have hcomm : ⁅tl M (gammaD D), tl M L⁆ = tl M L := tl_commutator_gammaD hp hD hL hn hc
    have hFF : FFChevConclusion (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) :=
      (h96 G m p hS M D hD (tl M L) hcomp hcomm).2
    by_cases hAlt : ∃ n : ℕ, 5 ≤ n ∧
        Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))
    · obtain ⟨hb, hag⟩ := hA G m p hS M D hD hQ L hL hn hc hAlt
      rcases hag with h | h
      · exact ⟨hb, Or.inl h⟩
      · exact ⟨hb, Or.inr (Or.inr h)⟩
    · obtain ⟨hb, hbeta⟩ := hC G m p hS M D hD hQ L hL hn hc hFF hAlt
      exact ⟨hb, Or.inr (Or.inl hbeta)⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
