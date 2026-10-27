module

public import CFSG.GH74.GLS.IVK.Lifted.CentSylow

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers CFSG.Assembly.LowTwoRank

section Quat

variable {G : Type} [Group G] [Finite G]

theorem ii4_4_quat : II4_4_quat := by
  intro G _ _ hG z hz S K hS hKC hrk
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 hS
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS' hKC.1 hsub
  have hsyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg hsyl
  have hq : CFSG.IsQuasisimple (Hat K) := TwoThin.isQuasisimple_hat hKC
  have hncyc := sylow_two_not_cyclic_of_quasisimple hq Pbar
  have hSK₂ : IsPGroup 2 ↥S := hS.isPGroup
  have hP2 : IsPGroup 2 ↥(S ⊓ K) := hSK₂.to_inf_left
  have hrankP : NoCommutingDistinctInvolutions ↥(S ⊓ K) := by
    intro u v huv
    have hu : orderOf (((u.1 : ↥(S ⊓ K)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf (((v.1 : ↥(S ⊓ K)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    have hcomm : ((u.1 : ↥(S ⊓ K)) : G) * ((v.1 : ↥(S ⊓ K)) : G) =
        ((v.1 : ↥(S ⊓ K)) : G) * ((u.1 : ↥(S ⊓ K)) : G) := by
      have := congrArg (fun x : ↥(S ⊓ K) => (x : G)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (eq_of_pRank_one hrk (u.1).2.2 (v.1).2.2 hu hv hcomm))
  rcases rank_one_two_cyclic_or_quaternion hP2 hrankP with hc | ⟨e, he1, ⟨ε⟩⟩
  · exfalso
    have hSKK : S ⊓ K ≤ K := inf_le_right
    let ψ : ↥(S ⊓ K) →* ↥(Pbar : Subgroup (Hat K)) :=
      ((hatMk K).comp (Subgroup.inclusion hSKK)).codRestrict (Pbar : Subgroup (Hat K)) (fun x => by
        rw [hPbar]
        exact mem_hatImg.2 ⟨Subgroup.inclusion hSKK x, x.2, rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      rw [hPbar] at hy
      obtain ⟨a, haS, rfl⟩ := mem_hatImg.1 hy
      exact ⟨⟨(a : G), haS⟩, Subtype.ext rfl⟩
    exact hncyc (isCyclic_of_surjective ψ hψ)
  · refine ⟨e + 2, by omega, ?_⟩
    rw [Nat.add_sub_cancel]
    exact ⟨ε.symm⟩

end Quat

end CFSG.GH74.GLS.IVK.Lifted
