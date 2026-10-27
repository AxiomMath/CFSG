module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cls3
public import Certificates.Certificate5247

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem not_sylCfgOf_L34
    {Y : Type} [Group Y] (hY : LieModel Y .PSL 3 2 2) : ¬ SylCfgOf Y := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hI : ((CFSG.ComponentClassification.PSL3Four.S).subgroupOf
      CFSG.ComponentClassification.PSL3Four.R).map
        ((Cls3.conjIso.trans (MulAut.congr e.symm)).toMonoidHom) = innSub Y := by
    have h1 : ((Cls3.conjIso.trans (MulAut.congr e.symm)).toMonoidHom) =
        (MulAut.congr e.symm).toMonoidHom.comp Cls3.conjIso.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, Cls3.map_SR_eq_innSub, map_innSub e.symm]
  intro hcfg
  exact not_threeCfg_sub_of_noThree _ _ CFSG.ComponentClassification.PSL3Four.S_le_R
    (m := 315) (by rw [CFSG.ComponentClassification.PSL3Four.card_S]; norm_num) (by decide)
    Certificates.certificate5247.2.2
    (threeCfg_of_sylCfgOf_aut (Cls3.conjIso.trans (MulAut.congr e.symm)) hI hcfg)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
