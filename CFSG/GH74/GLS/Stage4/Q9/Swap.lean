module

public import CFSG.GH74.GLS.Stage4.Q9.Setting

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

@[expose] def Q9Setting.swap {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) : Q9Setting G z K₂ K₁ F₂ F₁ where
  z_ord := S.z_ord
  one_class := S.one_class
  card₁ := S.card₂
  card₂ := S.card₁
  φ₁ := S.φ₂
  φ₂ := S.φ₁
  le_centralizer₁ := S.le_centralizer₂
  le_centralizer₂ := S.le_centralizer₁
  normal₁ := S.normal₂
  normal₂ := S.normal₁
  comm := fun x hx y hy => (S.comm y hy x hx).symm
  inter_eq := by rw [inf_comm]; exact S.inter_eq
  index_two := by rw [sup_comm]; exact S.index_two
  card3 := S.card3
  card2 := S.card2
  t := S.t
  t_ord := S.t_ord
  t_mem := S.t_mem
  t_notin := by rw [sup_comm]; exact S.t_notin
  A := S.B
  B := S.A
  A_act := S.B_act
  B_act := S.A_act
  A_det := S.B_det
  B_det := S.A_det
  Hs := S.Hs
  Hs_iso := S.Hs_iso
  Hs_le := S.Hs_le
  Hs_ge₁ := S.Hs_ge₂
  Hs_ge₂ := S.Hs_ge₁
  normalizer_eq := S.normalizer_eq
  tns := S.tns
  as := S.as
  as_ord := S.as_ord
  as_mem := S.as_mem
  as_moves := S.as_moves
  u := S.u
  u_mem := by rw [sup_comm]; exact S.u_mem
  u_ord := S.u_ord
  u_ne := S.u_ne
  w₁ := S.w₂
  w₂ := S.w₁
  w₁_mem := S.w₂_mem
  w₂_mem := S.w₁_mem
  w₁_sq := S.w₂_sq
  w₂_sq := S.w₁_sq
  w₁_act := S.w₂_act
  w₂_act := S.w₁_act
  a := S.a
  a_norm_z := S.a_norm_z
  a_norm_u := S.a_norm_u
  a_moves := S.a_moves
  a_cent := by
    have h := S.a_cent
    have hcomm : S.w₁ * S.w₂ = S.w₂ * S.w₁ := S.comm _ S.w₁_mem _ S.w₂_mem
    rw [hcomm] at h
    exact h

end CFSG.GH74.GLS.Stage4.Q9
