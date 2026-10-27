module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416ROdd
public import CFSG.LocalAnalysis.GLTheoremA.S8.Prop81

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

section Odd


theorem t158m_odd_false {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X}
    {L₁ L₂ : Subgroup X} (h : T158Hyp p K B x₁ x₂ L₁ L₂) (hQ : catalogIs (PSimple p K) t158FamOdd) :
    False := by
  obtain ⟨⟨hKG, hK, -⟩, -⟩ := h.hyp
  obtain ⟨-, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ := t158m_unpack h
  have hp := h.prime
  have hp2 := h.odd
  obtain ⟨hx1N, -⟩ := t158m_normalizer h
  obtain ⟨hx1p, hx2p⟩ := t158m_pow h
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d =>
    have hchar : d.1.characteristic ≠ 2 := hi
    have hr : d.1.characteristic.Prime := S8.lie_characteristic_prime d.1
    have hKr : IsChevSimple d.1.characteristic (PSimple p K) := Or.inl ⟨.lie d, rfl, ⟨e⟩⟩
    have hclo : ChevClosureQAt X p :=
      chevClosureQAt_of_lieComp_lieComps (G := X) lieComp_holds
        (fun _ hq h5 => lieCompsOn_holds hq h5) hp hp2
    have hL1r : IsChevSimple d.1.characteristic (PSimple p L₁) :=
      hclo hp hp2 d.1.characteristic hr ⊤ K (Subgroup.zpowers x₁) hKG hK hKr
        (t158m_elemAbelian_zpowers hx1p) (Subgroup.zpowers_le.2 hx1N) L₁
        (by rw [t158m_centralizer_zpowers]; exact hL1)
    have hsmall := chev2OddAmb_holds d.1.characteristic (PSimple p L₁) hr hchar hc1 hL1r
    exact t158m_false_of_chev2Small hp hp2 hL1 hc1 hsmall hx2p hn21 h.layer
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

theorem t158m_falseOn_odd : T158FalseOn t158FamOdd := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh
  exact t158m_odd_false hh hQ

end Odd

end CFSG.LocalAnalysis.GLTheoremA.T158

end
