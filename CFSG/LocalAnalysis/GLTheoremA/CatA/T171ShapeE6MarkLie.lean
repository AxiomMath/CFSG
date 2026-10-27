module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.RankThree.PartOne.S11c.Sec66TModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def isE6n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => q.p = 2 ∧ q.exponent = n | _ => False

theorem lieModel_E6_of_catalogIs
    {Y : Type} [Group Y] {m : ℕ} (hcat : catalogIs Y (isE6n m)) :
    CFSG.Blueprint.LieModel Y .E6 0 2 m := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | E6 q =>
    have hq : q.p = 2 := hP.1
    have hn : q.exponent = m := hP.2
    have hm : CFSG.Blueprint.UntwistedChevalleyModel Y .E6 (q.p ^ q.exponent) :=
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq e
    rw [hq, hn] at hm
    refine (CFSG.RankThree.PartOne.Sec66T.lieModel_untwisted_iff (t := .E6) (τ := .E6)
      (n := 0) (f := m) (by decide)).2 ⟨rfl, ?_, hm⟩
    exact ⟨Nat.prime_two, by rw [← hn]; exact q.exponent_pos, rfl⟩
  | _ => exact hP.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
