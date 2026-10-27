module

public import CFSG.GH74.GLS.LU.Local.A3ReduceGH
public import CFSG.GH74.GLS.LU.Local.Torus8
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a

public section

namespace CFSG.GH74.GLS.LU.Local

open CFSG.GH74.GLS.IVK

theorem luA3Lin_of_inputs_gh
    (h95 : CFSG.GH74.GLS.IVK.Proofs2.IVK_9_5At_gh_all) (hCov : L3Cover) : LUA3Lin_gh :=
  luA3Lin_of_leaf₁_gh h95 CFSG.GH74.GLS.IVK.Proofs2.ivk_4_4a l3InvTorus hCov luKStepLeaf₁

theorem luA3UniFive_of_inputs_gh
    (h95five : IVK_9_5At_gh 5) (hCov : L3Cover) : LUA3UniFive_gh :=
  luA3UniFive_of_leaf₁_gh h95five CFSG.GH74.GLS.IVK.Proofs2.ivk_4_4a l3InvTorus hCov luKStepLeaf₁

theorem luA3Uni_of_inputs_gh
    (h95 : CFSG.GH74.GLS.IVK.Proofs2.IVK_9_5At_gh_all) (hCov : L3Cover) : LUA3Uni_gh :=
  luA3Uni_of_leaf₁_gh h95 CFSG.GH74.GLS.IVK.Proofs2.ivk_4_4a l3InvTorus hCov luKStepLeaf₁
    (luA3UniFive_of_inputs_gh (CFSG.GH74.GLS.IVK.Proofs2.ivk_9_5At_gh_five_of_all h95) hCov)

end CFSG.GH74.GLS.LU.Local
