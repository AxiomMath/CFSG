module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22C
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerDich

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance

section Member

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z : G}

theorem isSubnormal_centralizer_member (hs : Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  have h := (Hat2A7S8.Asc77.T8.isClassical2A7_of_isUniqueInvolution hs.classical hK hz).subnormal
  rwa [top_inf_eq] at h

theorem oddCoreOf_le_centralizer_member (hs : Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) :
    oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
  Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_centralizer_member hs hK hz)

theorem mem_centralizer_closure_pair {c i : G} (hz : z * i = i * z) (hc : c * i = i * c) :
    i ∈ Subgroup.centralizer ((Subgroup.closure ({z, c} : Set G) : Subgroup G) : Set G) := by
  have hle : Subgroup.closure ({z, c} : Set G) ≤ Subgroup.centralizer ({i} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hz
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hc
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem member_le_normalizer_alpha (hs : Pre2A7 Ω K₀) {c : G} {K : Subgroup G}
    (hK : T8.XMem Ω c K) (hz : IsUniqueInvolution K z) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    {α : Subgroup G} (hα : alphaOf (Subgroup.closure ({z, c} : Set G)) = α)
    (hO : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.normalizer (α : Set G)) :
    K ≤ Subgroup.normalizer (α : Set G) := by
  have hL : Hat2A7S8.Asc77.T8.LayerHyp Ω c := Hat2A7S8.layerHyp_of_pre hs hc2 hc1
  intro y hy
  obtain ⟨i, hi, n, hn, rfl⟩ := Hat2A7S8.Asc77.T8.XMem.layerRes_cover hL hK y hy
  have hiK : i ∈ K := T8.layerRes_le c K hi
  have hic : i ∈ T8.cenZ c := T8.layerRes_le_cenZ c K hi
  have hiN : i ∈ Subgroup.normalizer (α : Set G) := by
    refine T8T.centralizer_le_normalizer_of_alphaOf_eq hα ?_
    refine mem_centralizer_closure_pair ?_ ?_
    · exact (Hat2A7S8.comm_of_mem_isUniqueInvolution hz hiK).symm
    · exact (T8.mem_cenZ_iff.mp hic).symm
  have hnN : n ∈ Subgroup.normalizer (α : Set G) :=
    hO (oddCoreOf_le_centralizer_member hs hK.1 hz hn)
  exact (Subgroup.normalizer (α : Set G)).mul_mem hiN hnN

end Member

section FrameAlpha

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z : G} {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}

namespace Frame3

section Alg

variable (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃)
include F

theorem w_sq : (u₁ * u₃) * (u₁ * u₃) = 1 := by
  calc (u₁ * u₃) * (u₁ * u₃) = u₁ * (u₃ * u₁) * u₃ := by group
    _ = u₁ * (u₁ * u₃) * u₃ := by rw [← F.comm₁₃']
    _ = (u₁ * u₁) * (u₃ * u₃) := by group
    _ = 1 := by rw [F.sq₁, F.sq₃]; exact F.z_sq

theorem z_comm_w : z * (u₁ * u₃) = (u₁ * u₃) * z :=
  ((show Commute z u₁ from F.z_comm₁).mul_right (show Commute z u₃ from F.z_comm₃)).eq

end Alg

section WithHyp

variable (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) (hΩ : HypOmegaGen Ω)
include F hΩ

theorem w_ne_one : u₁ * u₃ ≠ 1 := fun h =>
  F.u₁_not_mem₃ hΩ (by rw [eq_inv_of_mul_eq_one_left h]; exact K₃.inv_mem F.mem_K₃)

theorem w_ne_z : u₁ * u₃ ≠ z := fun h =>
  F.u₁_not_mem₃ hΩ (by
    have : u₁ = u₃ := mul_right_cancel (h.trans F.sq₃.symm)
    rw [this]
    exact F.mem_K₃)

theorem x_mem_B : u₁ * u₂ ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem y_mem_B : u₂ * u₃ ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem w_mem_B : u₁ * u₃ ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) := by
  rw [← F.x_mul_z_mul_y]
  exact (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)).mul_mem
    ((Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)).mul_mem (x_mem_B F hΩ) (z_mem_B F hΩ))
    (y_mem_B F hΩ)

theorem isElemAbelian2_pair₁₂ :
    IsElemAbelian2 (Subgroup.closure ({z, u₁ * u₂} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair F.z_sq F.x_sq F.z_ne_one (F.x_ne_one hΩ)
    (fun h => F.x_ne_z hΩ h.symm) F.z_comm_x

theorem isElemAbelian2_pair₂₃ :
    IsElemAbelian2 (Subgroup.closure ({z, u₂ * u₃} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair F.z_sq F.y_sq F.z_ne_one (F.y_ne_one hΩ)
    (fun h => F.y_ne_z hΩ h.symm) F.z_comm_y

theorem isElemAbelian2_pair₁₃ :
    IsElemAbelian2 (Subgroup.closure ({z, u₁ * u₃} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair F.z_sq F.w_sq F.z_ne_one (F.w_ne_one hΩ)
    (fun h => F.w_ne_z hΩ h.symm) F.z_comm_w

theorem closure_pair_le_B {c : G}
    (hc : c ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) :
    Subgroup.closure ({z, c} : Set G) ≤ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  intro w hw
  rcases hw with rfl | rfl
  · exact z_mem_B F hΩ
  · exact hc

variable (hH : Hyp51 (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)))
include hH

theorem alphaOf_eq_of_le {A : Subgroup G}
    (hAB : A ≤ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) (hA : IsElemAbelian2 A 2) :
    alphaOf A = alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) :=
  (lemma54_odd_and_eq hH (closure_pair_le_B F hΩ (x_mem_B F hΩ)) (isElemAbelian2_pair₁₂ F hΩ)).2
    A hAB hA

theorem alphaOf_pair₂₃ :
    alphaOf (Subgroup.closure ({z, u₂ * u₃} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) :=
  alphaOf_eq_of_le F hΩ hH (closure_pair_le_B F hΩ (y_mem_B F hΩ)) (isElemAbelian2_pair₂₃ F hΩ)

theorem alphaOf_pair₁₃ :
    alphaOf (Subgroup.closure ({z, u₁ * u₃} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) :=
  alphaOf_eq_of_le F hΩ hH (closure_pair_le_B F hΩ (w_mem_B F hΩ)) (isElemAbelian2_pair₁₃ F hΩ)

theorem odd_alpha : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)))) :=
  (lemma54_odd_and_eq hH (closure_pair_le_B F hΩ (x_mem_B F hΩ))
    (isElemAbelian2_pair₁₂ F hΩ)).1

theorem oddCore_le_normalizer {b : G}
    (hb : b ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) :
    oddCoreOf (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) :=
  T8T.oddCoreOf_centralizer_le_normalizer hH.1 hH.2.1 hb (fun _ hAB hA =>
    alphaOf_eq_of_le F hΩ hH hAB hA)

end WithHyp

section Members

variable (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) (hs : Pre2A7 Ω K₀)
  (hH : Hyp51 (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)))
include F hs hH

theorem le_normalizer_alpha₁ :
    K₁ ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) :=
  member_le_normalizer_alpha hs (F.xMem₁ hs.hyp ⟨u₂, F.mem_u₂, u₃, F.mem_u₃, rfl⟩) F.hz₁ F.y_sq
    (F.y_ne_one hs.hyp) (F.alphaOf_pair₂₃ hs.hyp hH)
    (F.oddCore_le_normalizer hs.hyp hH (F.z_mem_B hs.hyp))

theorem le_normalizer_alpha₂ :
    K₂ ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) :=
  member_le_normalizer_alpha hs (F.xMem₂ hs.hyp ⟨u₁, F.mem_u₁, u₃, F.mem_u₃, rfl⟩) F.hz₂ F.w_sq
    (F.w_ne_one hs.hyp) (F.alphaOf_pair₁₃ hs.hyp hH)
    (F.oddCore_le_normalizer hs.hyp hH (F.z_mem_B hs.hyp))

end Members

end Frame3

end FrameAlpha

end CFSG.ClassicalInvolution.Hat2A7S
