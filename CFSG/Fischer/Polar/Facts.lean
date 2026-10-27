module

public import CFSG.Fischer.Polar.Xi22
public import CFSG.Fischer.Uniq.PolarFacts
public import CFSG.Fischer.Uniq.HyperovalFacts
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import CFSG.Fischer.Uniq.Hyperoval

public section

namespace CFSG.Fischer

theorem polarFacts :
    PolarFacts where
  perp_comm _ _ h := perp_comm.1 h
  perp_self := perp_self
  line_perp _ hL _ hx _ hy := hL.perp_of_mem hx hy
  isLine_lineThru _ _ hxy h := isLine_lineThru hxy h
  left_mem_lineThru := left_mem_lineThru
  right_mem_lineThru := right_mem_lineThru
  eq_lineThru _ hL _ hx _ hy hxy := hL.eq_lineThru hx hy hxy
  ncard_lines_through := ncard_lines_through
  twins_of_line _ _ _ hpx hpy hxp hyp hxy h := twins_of_line hpx hpy hxp hyp hxy h
  ncard_perp_perp _ _ h := ncard_perp_perp h
  twinFree _ _ h _ _ hx hy hxy hp := twinFree_perp_perp h hx hy hxy hp
  eq_of_perp_perp _ _ _ h h' hN := eq_of_perp_perp h h' hN
  ncard_perp_ne := ncard_perp_ne
  exists_mem_hypOrbit _ hO hne := hO.exists_mem_hypOrbit hne
  ncard_of_mem_hypOrbit _ _ hO := ncard_of_mem_hypOrbit hO
  tvP_image_mem_hypOrbit _ _ hO p := tvP_image_mem_hypOrbit hO p
  hypOrbit_subset_of_invariant _ h𝒮 _ _ hO hOi := hypOrbit_subset_of_invariant h𝒮 hO hOi
  ncard_hypOrbit := ncard_hypOrbit
  hypOrbit_disjoint _ _ h := hypOrbit_disjoint h
  perp_delta := perp_delta
  delta_tvP := delta_tvP
  image_delta_hypOrbit := image_delta_hypOrbit
  injOn_tvP_image _ hO := injOn_tvP_image hO
  tvP_image_ne _ hO _ hf := tvP_image_ne hO hf
  exists_not_perp _ hO hne _ hf := hO.exists_not_perp hne hf
  xi_D2 := xi22_D2
  xi_MU := xi22_MU
  xi_ED := xi22_ED

theorem hyperovalFacts :
    HyperovalFacts where
  linesByPerp _ _ hxy h := lineThru_eq_perp hxy h
  isClosedHyperoval_of_mem _ _ hO := isClosedHyperoval_of_mem_hypOrbit hO
  eq_of_inter_perp _ _ hO hO' _ hp hp' h := hO.eq_of_inter_perp hO' hp hp' h
  not_linear _ hO _ hp _ hq := hO.not_linear hp hq

end CFSG.Fischer
