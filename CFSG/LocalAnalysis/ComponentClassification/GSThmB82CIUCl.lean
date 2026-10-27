module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClSp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClO

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank

namespace QPUJ6Cl

theorem false_of_barConfig6_classical {P : Type} [Group P] [Finite P] {τ : StatedLieTag}
    {n p f f'' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hmod : StatedClassicalModel P τ n p f'') (h : BarConfig6 P p f) : False := by
  cases τ with
  | PSL => exact false_of_barConfig6_psl hp hp2 hf hmod h
  | PSU => exact false_of_barConfig6_psu hp hp2 hf hmod h
  | PSp => exact false_of_barConfig6_psp hp hp2 hf hmod h
  | POmegaOdd => exact false_of_barConfig6_pomegaOdd hp hp2 hmod h
  | POmegaPlus => exact false_of_barConfig6_pomegaPlus hp hp2 hmod h
  | POmegaMinus => exact false_of_barConfig6_pomegaMinus hp hp2 hmod h
  | _ => exact hmod.2.elim

end QPUJ6Cl

theorem cfQPUJ6Classical_holds : CFQPUJ6Classical := by
  intro M _ _ p f hc ⟨τ, n, f'', hmod⟩
  have hbar := QPUJ6Cl.barConfig6_of_config hc
  obtain ⟨-, -, hp, hp2, hf, -, -⟩ := hc
  exact QPUJ6Cl.false_of_barConfig6_classical hp hp2 hf hmod hbar

end CFSG.ComponentClassification.GSThmB
