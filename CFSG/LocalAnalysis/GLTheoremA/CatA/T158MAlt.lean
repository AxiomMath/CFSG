module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTriv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Odd


theorem t158m_fgOn_false_of_oddInner {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X L : Subgroup G} {y : G} (hL : GLAPComponent p X L) (hchev : IsChevSimple 2 (PSimple p L))
    (hyp : y ^ p = 1) (hFG : FGOn p y L)
    (hodd : ∀ φ : MulAut (PSimple p L), Odd (orderOf φ) → ∃ g : PSimple p L, φ = MulAut.conj g) :
    False := by
  have hyN := t158m_fgOn_normalizer hFG
  have hα : MI.indAut p L y hyN ^ p = 1 := l154_indAut_pow_eq_one hyN hyp
  have hodd' : Odd (orderOf (MI.indAut p L y hyN)) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨g, hg⟩ := hodd _ hodd'
  have hin : InducesInnerMod p L y := (MI.indAut_mem_inner_iff hp hL hyN).1 ⟨g, hg.symm⟩
  have hInn : InnDiagOn p (Subgroup.zpowers y) L := MI.inner_innDiag_any hL hchev hyN hin
  rcases hFG with hF | ⟨hNI, -, -⟩
  · exact (MI.field_nonInnDiag_any hL hF).2 hInn
  · exact hNI.2 hInn

end Odd

section Alt


theorem t158m_alt_false {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X}
    {L₁ L₂ : Subgroup X} (h : T158Hyp p K B x₁ x₂ L₁ L₂) (hQ : catalogIs (PSimple p K) t158FamAlt) :
    False := by
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ := t158m_unpack h
  have hp := h.prime
  have hp2 := h.odd
  obtain ⟨hxN, -⟩ := t158m_normalizer h
  obtain ⟨hx1p, hx2p⟩ := t158m_pow h
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | alternating n hn =>
    have hxp' : IsPGroup p (Subgroup.zpowers x₁) :=
      isPGroup_of_isElemAbelian (t158m_elemAbelian_zpowers hx1p)
    have hα : chevAut p K ⟨x₁, hxN⟩ ^ p = 1 := chevAut_pow_eq_one p K hxN hx1p
    have hJ' := glaPComponent_chevTransfer hp hxN hxp' hL1
    obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hxp' hL1
    obtain ⟨m, hm5, ⟨eA⟩⟩ : ∃ m : ℕ, 5 ≤ m ∧ Nonempty (PSimple p L₁ ≃* alternatingGroup (Fin m)) := by
      by_cases hα1 : chevAut p K ⟨x₁, hxN⟩ = 1
      · rw [hα1, t158m_fixSubgroup_one] at hJ'
        obtain ⟨eT⟩ := chevQ_pSimple_top_equiv hp hna hJ'
        exact ⟨n, hn, ⟨eJ.trans (eT.trans e)⟩⟩
      · have hβ : (MulAut.congr e) (chevAut p K ⟨x₁, hxN⟩) ^ p = 1 := by
          rw [← map_pow, hα, map_one]
        have hβ1 : (MulAut.congr e) (chevAut p K ⟨x₁, hxN⟩) ≠ 1 := fun h' =>
          hα1 ((MulAut.congr e).injective (h'.trans (map_one _).symm))
        obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport hp e hJ'
        obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n p hn hp hp2 _ hβ hβ1 _ hLe
        exact ⟨m, (le_max_left 5 p).trans hm, ⟨eJ.trans (eLe.trans f)⟩⟩
    have hm : m = 5 ∨ m = 6 ∨ m = 8 := by
      by_contra hne
      exact not_chev2_alt hm5 (by omega) eA hc1
    have hamb : catalogIs (PSimple p L₁) l154AmbAlt :=
      ⟨TauCeti.CFSGIndex.alternating m hm5,
        ⟨by rcases hm with rfl | rfl | rfl <;> simp [ambiguousChev], by simp [l154AmbU33, onLie]⟩, ⟨eA⟩⟩
    exact t158m_fgOn_false_of_oddInner hp hp2 hL1 hc1 hx2p hn21 (l154_oddInner_of_ambAlt hamb)
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

theorem t158m_falseOn_alt : T158FalseOn t158FamAlt := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh
  exact t158m_alt_false hh hQ

end Alt

end CFSG.LocalAnalysis.GLTheoremA.T158

end
