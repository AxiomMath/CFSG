module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7b
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7B

variable {G : Type} [Group G]

theorem comm_of_mul_self_eq_one {a b z : G} (ha : a * a = z) (hb : b * b = z) (hz : z * z = 1)
    (hza : z * a = a * z) (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have hai : a⁻¹ = a * z := by
    rw [inv_eq_iff_mul_eq_one]
    calc a * (a * z) = (a * a) * z := by group
      _ = z * z := by rw [ha]
      _ = 1 := hz
  have hbi : b⁻¹ = b * z := by
    rw [inv_eq_iff_mul_eq_one]
    calc b * (b * z) = (b * b) * z := by group
      _ = z * z := by rw [hb]
      _ = 1 := hz
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  calc a * b = (a * b)⁻¹ := h1
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = (b * z) * (a * z) := by rw [hai, hbi]
    _ = b * (z * a) * z := by group
    _ = b * (a * z) * z := by rw [hza]
    _ = b * a * (z * z) := by group
    _ = b * a := by rw [hz]; group

theorem mem_closure_fst {x y w : G} : x ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mem_closure_snd {x y w : G} : y ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mem_closure_thd {x y w : G} : w ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

end T7B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

namespace Hyp22

theorem hzK' (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K' z :=
  isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK'

theorem hzK₃ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K₃ z :=
  isUniqueInvolution_of_mem_twinSet h.std.hz h.hK₃

theorem sq₁ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.std.hz h.hu₁.1 h.hu₁.2

theorem sq₂ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK' h.hu₂.1 h.hu₂.2

theorem sq₃ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK₃ h.hu₃.1 h.hu₃.2

theorem comm_z₁ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₁ = u₁ * z :=
  e189_commute_of_mem h.std.hz h.hu₁.1

theorem comm_z₂ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₂ = u₂ * z :=
  e189_commute_of_mem h.hzK' h.hu₂.1

theorem comm_z₃ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₃ = u₃ * z :=
  e189_commute_of_mem h.hzK₃ h.hu₃.1

theorem sq_12 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₂) * (u₁ * u₂) = 1 :=
  h.hB.2 _ T7B.mem_closure_fst

theorem sq_23 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : (u₂ * u₃) * (u₂ * u₃) = 1 :=
  h.hB.2 _ T7B.mem_closure_thd

theorem comm₁₂ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ = u₂ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₂ h.std.hz.sq h.comm_z₁ h.sq_12

theorem comm₂₃ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ = u₃ * u₂ :=
  T7B.comm_of_mul_self_eq_one h.sq₂ h.sq₃ h.std.hz.sq h.comm_z₂ h.sq_23

theorem eq_13 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ = z * ((u₁ * u₂) * (u₂ * u₃)) := by
  have h1 : (u₁ * u₂) * (u₂ * u₃) = u₁ * z * u₃ := by
    calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  calc u₁ * u₃ = (z * z) * (u₁ * u₃) := by rw [h.std.hz.sq, one_mul]
    _ = z * (z * u₁) * u₃ := by group
    _ = z * (u₁ * z) * u₃ := by rw [h.comm_z₁]
    _ = z * ((u₁ * u₂) * (u₂ * u₃)) := by rw [h1]; group

theorem mem_B_13 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [h.eq_13]
  exact Subgroup.mul_mem _ T7B.mem_closure_snd
    (Subgroup.mul_mem _ T7B.mem_closure_fst T7B.mem_closure_thd)

theorem sq_13 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₃) * (u₁ * u₃) = 1 :=
  h.hB.2 _ h.mem_B_13

theorem comm₁₃ (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ = u₃ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₃ h.std.hz.sq h.comm_z₁ h.sq_13

theorem closure_rotate (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z, u₃ * u₁} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact T7B.mem_closure_thd
    · exact T7B.mem_closure_snd
    · rw [← h.comm₁₃]
      exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · have e : u₁ * u₂ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
        calc u₁ * u₂ = (z * z) * (u₁ * u₂) := by rw [h.std.hz.sq, one_mul]
          _ = z * (z * u₁ * u₂) := by group
          _ = z * (u₁ * z * u₂) := by rw [h.comm_z₁]
          _ = z * (u₂ * z * u₁) := by
              rw [show u₁ * z * u₂ = u₁ * (z * u₂) by group, h.comm_z₂,
                show u₂ * z * u₁ = u₂ * (z * u₁) by group, h.comm_z₁,
                show u₁ * (u₂ * z) = (u₁ * u₂) * z by group,
                show u₂ * (u₁ * z) = (u₂ * u₁) * z by group, h.comm₁₂]
          _ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
              rw [show (u₂ * u₃) * (u₃ * u₁) = u₂ * (u₃ * u₃) * u₁ by group, h.sq₃]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem closure_swap (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₁, z, u₁ * u₃} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [← h.comm₁₂]
      exact T7B.mem_closure_fst
    · exact T7B.mem_closure_snd
    · exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [h.comm₁₂]
      exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have e : u₂ * u₃ = z * ((u₂ * u₁) * (u₁ * u₃)) := by
        calc u₂ * u₃ = (z * z) * (u₂ * u₃) := by rw [h.std.hz.sq, one_mul]
          _ = z * (z * u₂ * u₃) := by group
          _ = z * (u₂ * z * u₃) := by rw [h.comm_z₂]
          _ = z * ((u₂ * u₁) * (u₁ * u₃)) := by
              rw [show (u₂ * u₁) * (u₁ * u₃) = u₂ * (u₁ * u₁) * u₃ by group, h.sq₁]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))

theorem rotate (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : Hyp22 p f Ω K' K₃ K z u₂ u₃ u₁ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hKK' : K ∈ twinSet Ω K' := by
    rw [twinSet_eq_of_mem_twinSet h.std.hz h.std.hK']
    exact mem_twinSet_self hK h.std.hz
  have hperp : KPerp Ω K' = KPerp Ω K := ((l6_3 p f hp hq G Ω hΩ K hK K' h.std.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz h.std.hK'
  refine
    { std := Std7.of_twin h.std h.std.hK' h.hK₃ h.hK₃K'
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := hKK'
      hK₃K := h.std.hne.symm
      hK₃K' := h.hK₃K.symm
      hu₁ := h.hu₂
      hu₂ := h.hu₃
      hu₃ := h.hu₁
      hB := ?_ }
  rw [h.closure_rotate]
  exact h.hB

theorem swap (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) : Hyp22 p f Ω K' K K₃ z u₂ u₁ u₃ := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hperp : KPerp Ω K' = KPerp Ω K := ((l6_3 p f hp hq G Ω hΩ K hK K' h.std.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz h.std.hK'
  refine
    { std := Std7.of_twin h.std h.std.hK' (mem_twinSet_self hK h.std.hz) h.std.hne.symm
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := by rw [htw]; exact h.hK₃
      hK₃K := h.hK₃K'
      hK₃K' := h.hK₃K
      hu₁ := h.hu₂
      hu₂ := h.hu₁
      hu₃ := h.hu₃
      hB := ?_ }
  rw [h.closure_swap]
  exact h.hB

theorem isElemAbelian2_closure (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z} : Set G)) 2 := by
  have hne : u₁ * u₂ ≠ z := by
    intro he
    have hK' : K' ∈ Ω := h.std.hK'.1
    have hK : K ∈ Ω := h.std.stand.mem
    refine T7A.not_mem_inf_of_orderOf_four h.std.stand.hyp hK hK' h.std.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h.hu₁.1) h.std.hz.mem
  have h1 : u₁ * u₂ ≠ 1 := by
    intro he
    have hK' : K' ∈ Ω := h.std.hK'.1
    have hK : K ∈ Ω := h.std.stand.mem
    refine T7A.not_mem_inf_of_orderOf_four h.std.stand.hyp hK hK' h.std.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h.hu₁.1
  have hcomm : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [h.comm_z₂]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [h.comm_z₁]
      _ = z * (u₁ * u₂) := by group
  exact T7A.isElemAbelian2_closure_pair h.sq_12 h.std.hz.sq h1 h.std.hz.ne_one hne hcomm

end Hyp22

end CFSG.ClassicalInvolution.Asc77
