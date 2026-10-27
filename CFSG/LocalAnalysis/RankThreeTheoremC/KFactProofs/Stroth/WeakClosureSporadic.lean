module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic

@[expose] def WCSporadicAt (s : TauCeti.SporadicName) [Finite (Carrier s)] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → WCOn p (Carrier s)

theorem wcSporadic_of_forall
    (h : ∀ (s : TauCeti.SporadicName) [Finite (Carrier s)], WCSporadicAt s) : WCSporadic := by
  intro K _ _ _ _ hK p hp hp2
  obtain ⟨s, ⟨e⟩⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Carrier s) := Finite.of_equiv K e.toEquiv
  exact WCOn.of_mulEquiv e (h s p hp hp2)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
