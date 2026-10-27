module

public import CFSG.GF2Type.SmithTypeE.Parts
public import CFSG.LargeExtraspecial.S14C12Lit
import CFSG.GF2Type.Entry
public import CFSG.LargeExtraspecial.BridgeSetting

public section

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Bridge

theorem partA_of_reifartSmithU62Input (hRS : S14.ReifartSmithU62Input) : PartA := by
  intro G _ _ _ _ z hz hext hcard Mbar _ hMbar hU
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 10 := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  obtain ⟨g⟩ := hU
  have g' : timmesfeldFStar Mbar ≃* timmesfeldPSU 6 :=
    (MulEquiv.subgroupCongr (generalizedFitting_eq_timmesfeldFStar Mbar).symm).trans g
  have hE := hRS G (Setting.ofFStar z hz hext') hw
    ⟨(equivOfMapEq e (timmesfeldFStar_map e)).trans g'⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, hE⟩)

end CFSG.GF2Type.SmithTypeE
