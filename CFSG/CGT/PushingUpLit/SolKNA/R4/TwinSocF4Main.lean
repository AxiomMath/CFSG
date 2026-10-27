module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Prop
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Red
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)

theorem conjNormal_z_mem_autCentOf {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    {R : Subgroup A} {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) :
    (MulAut.conjNormal (H := T) z) ∈ autCentOf T (sylowSet S) := by
  refine conjNormal_mem_autCentOf fun s hs => ?_
  have h : s ∈ Subgroup.centralizer ({z} : Set A) := hd.cent (mem_sylowSet_le S hs)
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm


theorem autCentInv_of_socF4 {r : ℕ} (h3 : SocF4L3 r) (hU : SocF4U3 r) : AutCentInvR r := by
  intro hr A _ _ T _ hT hab hC hE R S z hd hc hnO hed ψ hψ hS
  have hψC : ψ ∈ autCentOf T (sylowSet S) := mem_autCentOf_iff.mpr hS
  have hz2 : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by
    have := hd.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hcY := conjNormal_z_mem_autCentOf T hd
  have hc2 : (MulAut.conjNormal (H := T) z) * MulAut.conjNormal z = 1 := by
    rw [← map_mul, hz2, map_one]
  have hc1 : (MulAut.conjNormal (H := T) z) ≠ 1 := fun h => hz1 (conjNormal_eq_one hC h)
  rcases hE with hL2 | hL3 | hU3
  · exact autCentInv_of_smallL2 hr T hC hL2 hd hc hψ hψC
  · obtain ⟨hle, hnorm, hodd, K, _, _, hKodd, -, ⟨e⟩⟩ :=
      h3 hr A T hT hab hC (Or.inr (Or.inl hL3)) R S z hd hc hnO hed hL3
    exact eq_of_sl2_odd_index hle hnorm hodd hKodd e hψC hψ hcY hc2 hc1
  · obtain ⟨hle, hnorm, hodd, K, _, _, hKodd, -, ⟨e⟩⟩ :=
      hU hr A T hT hab hC (Or.inr (Or.inr hU3)) R S z hd hc hnO hed hU3
    exact eq_of_sl2_odd_index hle hnorm hodd hKodd e hψC hψ hcY hc2 hc1

theorem model163R_of_socF4 {r : ℕ} (h3 : SocF4L3 r) (hU : SocF4U3 r) : Perp22Rest.Model163R r :=
  model163R_of_autCentInvR (autCentInv_of_socF4 h3 hU)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
