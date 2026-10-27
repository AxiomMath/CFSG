module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClU
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClSp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOModel

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem cfQPUJClassical_of_core (hcore : OCore) : CFQPUJClassical := by
  intro M _ _ p' f' p f hc ⟨τ, n, f'', hmod⟩
  obtain ⟨hM, hZ, -, -, -, -, hp, hp2, hf, h5, rfl, rfl, E, L, t, J, J₀, hE, hLE, hLc, hLtop, hLm,
    htL, ht2, htZ, hJt, hJc, hJm, hJ₀L, hJ₀J, hJ₀⟩ := hc
  have hbar : BarConfig (M ⧸ center M) p f p f :=
    barConfig_of_central hM hZ hE hLE hLc hLtop hLm htL ht2 htZ hJt hJc hJm hJ₀L hJ₀J hJ₀
  cases τ with
  | PSL => exact false_of_barConfig_psl hp hp2 hf h5 hmod hbar
  | PSU => exact false_of_barConfig_psu hp hp2 hf h5 hmod hbar
  | PSp => exact false_of_barConfig_psp hp hp2 hf h5 hmod hbar
  | POmegaOdd => exact false_of_barConfig_pomegaOdd_of_core hcore hp hp2 hf h5 hmod hbar
  | POmegaPlus => exact false_of_barConfig_pomegaPlus_of_core hcore hp hp2 hf h5 hmod hbar
  | POmegaMinus => exact false_of_barConfig_pomegaMinus_of_core hcore hp hp2 hf h5 hmod hbar
  | _ => exact hmod.2.elim

end CFSG.ComponentClassification.GSThmB.QPUCl
