module

public import CFSG.GH74.GLS.LU.Local.KStep

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local

@[expose] def IVK_9_5At_all : Prop :=
  ∀ q : ℕ, 5 ≤ q → IVK_9_5At q

theorem ivk_9_5At_five_of_all (h : IVK_9_5At_all) : IVK_9_5At 5 :=
  h 5 le_rfl

theorem ivk_9_5_of_all (h : IVK_9_5At_all) : IVK_9_5 :=
  fun J _ _ hJ hK z hz q hodd hq hsl hcyc => h q hq.le J hJ hK z hz hodd hsl hcyc

theorem ivk_9_5At_all_of (h : IVK_9_5) (h5 : IVK_9_5At 5) : IVK_9_5At_all := by
  intro q hq
  rcases hq.eq_or_lt with rfl | hlt
  · exact h5
  · exact IVK_9_5At_of h hlt

end CFSG.GH74.GLS.IVK.Proofs2
