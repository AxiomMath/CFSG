module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUCl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Cfg

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem QPUJ6Cl.barConfig6_of_config3 {M : Type} [Group M] [Finite M] {p f : ℕ}
    (hc : QPUJ6Config3 M p f) : QPUJ6Cl.BarConfig6 (M ⧸ center M) p f :=
  QPUJ6Cl.barConfig6_of_data hc.1 hc.2.1 hc.2.2.2.2.2.2

theorem cfQPUJ6ThreeClassical_holds : CFQPUJ6ThreeClassical := by
  intro M _ _ p f hc ⟨τ, n, f'', hmod⟩
  have hbar := QPUJ6Cl.barConfig6_of_config3 hc
  obtain ⟨-, -, hp, hp2, hf, -, -⟩ := hc
  exact QPUJ6Cl.false_of_barConfig6_classical hp hp2 hf hmod hbar

end CFSG.ComponentClassification.GSThmB
