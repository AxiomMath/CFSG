module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MSmall
public import CFSG.HardMathSupport.Dickson.BMRows.KFormBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def T158L34NoFG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (X L : Subgroup G) (y : G),
    GLAPComponent p X L → catalogIs (PSimple p L) chev2L34 → y ^ p = 1 → ¬ FGOn p y L

section Spor


theorem t158m_spor_false (hTab : CFSG.HardMathSupport.Dickson.BMRows.I1416Chev2SporListK)
    (hL34 : T158L34NoFG) {X : Type} [Group X] [Finite X]
    {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X} {L₁ L₂ : Subgroup X} (h : T158Hyp p K B x₁ x₂ L₁ L₂)
    (hc : ¬ IsChevSimple 2 (PSimple p K)) (hQ : catalogIs (PSimple p K) t158FamSpor) : False := by
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ := t158m_unpack h
  have hp := h.prime
  have hp2 := h.odd
  obtain ⟨hxN, -⟩ := t158m_normalizer h
  obtain ⟨hx1p, hx2p⟩ := t158m_pow h
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | sporadic s =>
    obtain ⟨hB, hM⟩ := CFSG.HardMathSupport.Dickson.BMRows.kRows_of_isKGroup
      (CFSG.HardMathSupport.Dickson.BMRows.isKGroup_pSimple h.hyp.1.1 hK) e
    have hxp' : IsPGroup p (Subgroup.zpowers x₁) :=
      isPGroup_of_isElemAbelian (t158m_elemAbelian_zpowers hx1p)
    have hα : chevAut p K ⟨x₁, hxN⟩ ^ p = 1 := chevAut_pow_eq_one p K hxN hx1p
    have hJ' := glaPComponent_chevTransfer hp hxN hxp' hL1
    obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hxp' hL1
    by_cases hα1 : chevAut p K ⟨x₁, hxN⟩ = 1
    · rw [hα1, t158m_fixSubgroup_one] at hJ'
      obtain ⟨eT⟩ := chevQ_pSimple_top_equiv hp hna hJ'
      exact hc (chev_isChevSimple_of_mulEquiv (eJ.trans eT).symm hc1)
    · have hLch : IsChevSimple 2 (PSimple p (chevTransfer p K L₁)) :=
        chev_isChevSimple_of_mulEquiv eJ.symm hc1
      obtain ⟨j, hj, ⟨f⟩⟩ := hTab (PSimple p K) s ⟨e⟩ hB hM p hp hp2 (chevAut p K ⟨x₁, hxN⟩) hα hα1
        (chevTransfer p K L₁) hJ' hLch
      rcases hj with hj | hj
      · exact t158m_false_of_chev2Small hp hp2 hL1 hc1 ⟨j, hj, ⟨eJ.trans f⟩⟩ hx2p hn21 h.layer
      · exact hL34 X p hp hp2 _ L₁ x₂ hL1 ⟨j, hj, ⟨eJ.trans f⟩⟩ hx2p hn21
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | lie _ => exact hi.elim

theorem t158m_noOn_spor (hTab : CFSG.HardMathSupport.Dickson.BMRows.I1416Chev2SporListK)
    (hL34 : T158L34NoFG) : T158NoOn t158FamSpor := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hc hh
  exact t158m_spor_false hTab hL34 hh hc hQ

end Spor

end CFSG.LocalAnalysis.GLTheoremA.T158

end
