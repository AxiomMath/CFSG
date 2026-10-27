module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

structure Ctx49 (G : Type) [Group G] [Finite G] (z : G) (S K F U : Subgroup G) (x y : G) : Prop where
  std : Std4r1 G z S K F
  hQF : Qz S z = F
  quatF : ∃ n, IVK.IsQuaternionTwoGroup ↥F n
  U_le : U ≤ Rz S z
  U_four : IVK.IsFourSubgroup U
  U_norm : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U
  x3 : IsPGroup 3 ↥(zpowers x)
  x_W : x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G)
  x_U : x ∈ normalizer (U : Set G)
  x_z : x * z * x⁻¹ ≠ z
  card_eq : Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z)
  idx : (Rz S z).relIndex S = 2
  y_S : y ∈ S
  y_two : orderOf y = 2
  y_R : y ∉ Rz S z
  y_sd : ∃ n, IVK.IsSemidihedralTwoGroup ↥(Qz S z ⊔ zpowers y) n

structure Closed49 : Prop where
  hII : II4_4_4_center
  hq : II4_4_quat
  hdiag : IVK_diag_unique
  h19 : IVK_1_9_outer
  hsd : SD_facts
  hsdq : SD_sq_not_z
  hqc : Quat_centr
  hrn : Rnormal4

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
