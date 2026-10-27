module

public import CFSG.CGT.PushingUpLit.J42.S5ExtChain
public import CFSG.CGT.PushingUpLit.J42.S5ExtRho
public import CFSG.CGT.PushingUpLit.J42.S5ExtWlog
public import Certificates.Certificate271071

public section

namespace CFSG.CGT.PushingUpLit.SolK

theorem gen4_of_extraData {K : Type*} [Group K] [Finite K]
    (D : ExtraData K) : CFSG.GH74.SectionalTwoRankLE K 4 := by
  have I : S5Iface := Classical.choice Certificates.certificate271071
  exact s5ext_sectionalTwoRankLE_of_central (D.nf 4) (s5Rho I D).z_central (s5Rho I D).z_sq
    (fun H hH hz => s5ext_gen4_core I D (s5Rho I D) H hH hz)

end CFSG.CGT.PushingUpLit.SolK
