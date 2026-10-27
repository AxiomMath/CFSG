module

public import CFSG.LargeExtraspecial.S7One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

structure Data (S : Setting G) (g : G) (t : S.O) : Prop where
  H : Hyp4 S g
  hNo : NoA2 S g
  C : Cons311 S g
  ht : t ∈ S.Lbar g
  ht1 : t ≠ 1
  hL : LinCase S g ht
  h3 : finrank (ZMod 2) (Vt S g t) = 3
  hw : S.width = 6

namespace Data

variable (D : Data S g t)
include D

theorem htt : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
  coe_mul_self (mul_self_of_mem_Lbar S D.H.conj_mem D.ht)

theorem finrank_commSpace :
    finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 6 := by
  have hT := Submodule.finrank_mono (Vt_le_Tt D.H D.hNo D.ht1 D.hL)
  have hU := S7.finrank_commSpace_eq D.H D.ht D.ht1
  have h2 := two_mul_finrank_commSpace_le D.htt
  have hQ := S.finrank_Qt_eq_two_mul_width
  have := D.h3
  have := D.hw
  omega

theorem Tt_eq_Vt : Tt S g t = Vt S g t := by
  have hU := S7.finrank_commSpace_eq D.H D.ht D.ht1
  have h6 := D.finrank_commSpace
  have := D.h3
  exact (Submodule.eq_of_le_of_finrank_le (Vt_le_Tt D.H D.hNo D.ht1 D.hL) (by omega)).symm

theorem commSpace_eq_fixSpace :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  refine Submodule.eq_of_le_of_finrank_le (commSpace_le_fixSpace D.htt) ?_
  have h1 := finrank_commSpace_add_finrank_fixSpace ((t : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have h6 := D.finrank_commSpace
  have hQ := S.finrank_Qt_eq_two_mul_width
  have := D.hw
  omega

theorem q_eq_zero {u : S.Qt} (hu : u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.q u = 0 :=
  (isTypeA_of_linCase D.H D.ht1 D.hL).2.2.2.2 u hu

end Data

end CFSG.GF2Type.Smith1979.Case2
