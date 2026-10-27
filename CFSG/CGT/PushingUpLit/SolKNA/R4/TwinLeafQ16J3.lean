module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J3Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafModels
public import Certificates.Certificate320304

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

theorem j3Q16_pg_mem :
    ∀ l < Check.j3Q16.pg.size,
      CFSG.Monster.B.Co2.permOfArr 6156 Check.j3Q16.pg[l]! ∈ CFSG.Sporadic.SmallOddCore.j3R := by
  intro l hl
  have hsub : CFSG.Sporadic.SmallOddCore.j3S ≤ CFSG.Sporadic.SmallOddCore.j3R :=
    (CFSG.Sporadic.SmallOddCore.ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial).1
  have hmem : Check.j3Q16.pg[l]! ∈ Check.j3Q16.pg := by
    rw [getElem!_pos Check.j3Q16.pg l hl]
    exact Array.getElem_mem hl
  have hx : Check.j3Q16.pg[l]! ∈ CFSG.Sporadic.SmallOddCore.j3SylowGenTbls.map
      CFSG.Sporadic.SmallOddCore.Native.natArr := by
    simpa [Check.j3Q16] using hmem
  obtain ⟨T, hT, hTx⟩ := List.mem_map.1 hx
  refine hsub ?_
  rw [← hTx]
  exact Subgroup.subset_closure ⟨T, List.mem_toArray.2 hT, rfl⟩

theorem noQ16Q16_j3R :
    NoQ16Q16 ↥CFSG.Sporadic.SmallOddCore.j3R := by
  obtain ⟨hle, hc, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  exact noQ16Q16_of_sylow_card hle (k := 8) (m := 392445) (hc.trans (by norm_num)) (by decide)
    (by rw [CFSG.ComponentClassification.RankTwoSporadic.J3.card_j3R]; norm_num)
    Certificates.certificate320304

theorem autJ3NoQ16Q16_holds :
    AutJ3NoQ16Q16 :=
  autJ3NoQ16Q16_of_model noQ16Q16_j3R

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
