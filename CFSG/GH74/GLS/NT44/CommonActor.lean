module

public import CFSG.GH74.GLS.NT44.LowRankAssembly
public import CFSG.GH74.GLS.NT44.NoncentralInvolution
import CFSG.GH74.GLS.NT44.HighRankAssembly
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
public import CFSG.GH74.GLS.TwoThin.ClassCongr

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem exists_balanced_actor_of_conjugate_closure_le_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {T W J : Subgroup G} {x : G}
    (hnonab : ∃ b c : G, b * c ≠ c * b)
    (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ z).ncard ≤
        (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x).ncard)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hcenter : Nat.card (Subgroup.center fullQ) = 16)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hxT : x ∈ T)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W
      (CFSG.GH74.GLS.zStar (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)))
    (hWT : W ≤ T)
    (hZW : Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ W) :
    ∃ A : Subgroup G,
      Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ A ∧
      A ≤ T ⊓ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x ∧
        CFSG.GH74.GLS.IsE 3 ⊤ A ∧
        CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A := by
  classical
  by_cases hhigh : 3 ≤ CFSG.pRank 2 ↥W
  · let A : Subgroup G := (CFSG.omega₁ W (p := 2)).map W.subtype
    have hA := CFSG.GH74.GLS.NT44.high_rank_omega_balance_of_rigid_center_sylow
      (G := G) (fullQ := fullQ) (x := x) (W := W) hnonab hx2 hmax hW hhigh
    change A ≤ W ∧ CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A at hA
    have hWP : W ≤ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x :=
      hW.le.trans inf_le_left
    have hZA : Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ A := by
      refine (Subgroup.closure_le _).2 ?_
      intro z hz
      have hzW : z ∈ W := hZW (Subgroup.subset_closure hz)
      have hzorder : orderOf z = 2 := hz.2.orderOf_eq.symm.trans hx2
      refine Subgroup.mem_map.mpr ⟨⟨z, hzW⟩, ?_, rfl⟩
      change (⟨z, hzW⟩ : W) ∈ Subgroup.closure {w : W | w ^ (2 ^ 1) = 1}
      apply Subgroup.subset_closure
      apply Subtype.ext
      change z ^ (2 ^ 1) = 1
      simpa only [pow_one, ← hzorder] using pow_orderOf_eq_one z
    exact ⟨A, hZA, le_inf (hA.1.trans hWT) (hA.1.trans hWP), hA.2⟩
  · have hWrank : CFSG.pRank 2 ↥W ≤ 2 := by omega
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTCs : CFSG.ABGLocalTools.IsSylowOf 2 T
        (Subgroup.centralizer ({x} : Set G)) := hT.of_le hTC le_top
    have hTJ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ J) J :=
      CFSG.GH74.GLS.Stage1.Thm4.P92.sylow_inf hJ hTCs
    let e : CFSG.GH74.GLS.kBar J ≃* fullQ := hJ.2.some
    have hL34J : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar J) :=
      CFSG.GH74.GLS.TwoThin.isL34Quotient_of_mulEquiv e.symm hL34
    obtain ⟨u, huTJ, hu2, huZ⟩ :=
      CFSG.GH74.GLS.NT44.exists_involution_mem_sylow_not_mem_zStar_of_isL34Quotient
        J (T ⊓ J) hTJ hL34J
    have huT : u ∈ T := (Subgroup.mem_inf.mp huTJ).1
    have huJ : u ∈ J := (Subgroup.mem_inf.mp huTJ).2
    let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
    let A : Subgroup G := Z ⊔ Subgroup.zpowers u
    refine ⟨A, le_sup_left, ?_⟩
    exact CFSG.GH74.GLS.NT44.low_rank_conjugate_closure_balance_of_noncentral_involution
      (G := G) (fullQ := fullQ) (T := T) (W := W) (J := J) (x := x) (u := u)
      hnonab hx2 hmax hJ hcenter hT hxT hTC hW hWT hZW hWrank huT huJ hu2 huZ

end CFSG.GH74.GLS.NT44
