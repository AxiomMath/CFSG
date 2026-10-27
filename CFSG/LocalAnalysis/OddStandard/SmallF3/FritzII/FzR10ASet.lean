module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G]

structure FzR10ASet (t tau lam rho : G) (Z E W Q R T P : Subgroup G) (a b : G) : Prop where
  str : FzStr t tau lam rho Z E W Q R T
  pf : FzPFacts t tau rho E W Q T P
  h8 : FzZ8 Z E P
  basis : FzR10ABasis P a b
  rho_act : FzR10AAct a b rho rho0

structure FzR10AMats (t tau lam a b : G) (Mt Ms Ml : Mat) : Prop where
  lt_t : FzR10AMatLt Mt
  lt_s : FzR10AMatLt Ms
  lt_l : FzR10AMatLt Ml
  act_t : FzR10AAct a b t Mt
  act_s : FzR10AAct a b tau Ms
  act_l : FzR10AAct a b lam Ml

end CFSG.OddStandard.SmallF3.FritzII
