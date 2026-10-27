module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3.TA3

theorem embedsAut_of_autModel {K G : Type} [Group K] [Group G] (M : GH74.KGroups.AutModel K G) :
    EmbedsAut K ↥M.A := by
  intro Y _ N _ ⟨eK⟩ hC
  have hinj := realize_injective N eK M hC
  refine ⟨(realize N eK M).codRestrict M.A (fun y => realize_range_le N eK M ⟨y, rfl⟩), ?_⟩
  intro a b hab
  exact hinj (congrArg Subtype.val hab)

theorem embedsAut_of_exactModel {M : Type} [Group M] {P R : Subgroup M}
    (hA : Sporadic.SmallOddCore.AutModel P R) {K : Type} [Group K] (θ₀ : K ≃* P) :
    EmbedsAut K ↥R := by
  intro Y _ N _ ⟨eK⟩ hC
  have hinj := hA.embed_injective N (eK.trans θ₀) hC
  refine ⟨(hA.embed N (eK.trans θ₀)).codRestrict R (fun y => hA.embed_mem N _ y), ?_⟩
  intro a b hab
  exact hinj (congrArg Subtype.val hab)

end CFSG.CGT.PushingUpLit.SolKNA.R4
