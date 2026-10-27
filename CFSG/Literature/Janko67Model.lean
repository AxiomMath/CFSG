module

public import CFSG.RankThree.GF2n.Parrott.PSp43Model

public section

namespace CFSG.Literature.Janko67

open CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43


abbrev C0 : Subgroup QP45.originalSubgroup :=
  Subgroup.centralizer ({⟨t, t_mem_Q⟩} : Set QP45.originalSubgroup)

@[expose] def tC : C0 := ⟨⟨t, t_mem_Q⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩


@[expose] def uC : C0 :=
  ⟨⟨u, u_mem_Q⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_u.symm)⟩

@[expose] def a1C : C0 :=
  ⟨⟨alpha1, alpha1_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_alpha1.symm)⟩

@[expose] def b1C : C0 :=
  ⟨⟨beta1, beta1_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_beta1.symm)⟩

@[expose] def a2C : C0 :=
  ⟨⟨alpha2, alpha2_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_alpha2.symm)⟩

@[expose] def b2C : C0 :=
  ⟨⟨beta2, beta2_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_beta2.symm)⟩

@[expose] def s1C : C0 :=
  ⟨⟨sigma1, sigma1_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_sigma1.symm)⟩

@[expose] def s2C : C0 :=
  ⟨⟨sigma2, sigma2_mem_Q⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_sigma2.symm)⟩

@[expose] def P0 : Subgroup C0 := Subgroup.closure {uC, a1C, b1C, a2C, b2C}

@[expose] def S0 : Subgroup C0 := Subgroup.closure {tC, uC, a1C * a2C, b1C * b2C}

end CFSG.Literature.Janko67
