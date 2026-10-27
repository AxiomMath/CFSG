module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Setup
public import CFSG.ClassicalInvolution.Asc77.AscT7BSylow

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

structure Hyp22G (Ω : Set (Subgroup G)) (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G) : Prop where
  hyp : HypOmegaGen Ω
  mem : K ∈ Ω
  hz : IsUniqueInvolution K z
  subn : ∀ L ∈ twinSet Ω K, IsSubnormal L (Subgroup.centralizer ({z} : Set G))
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  hK₃ : K₃ ∈ twinSet Ω K
  hK₃K : K₃ ≠ K
  hK₃K' : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  hB : IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3

namespace Hyp22G

theorem hzK' (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K' z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK'

theorem hzK₃ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K₃ z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK₃

theorem sq₁ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.hz h.hu₁.1 h.hu₁.2

theorem sq₂ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK' h.hu₂.1 h.hu₂.2

theorem sq₃ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK₃ h.hu₃.1 h.hu₃.2

theorem comm_z₁ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : z * u₁ = u₁ * z :=
  e189_commute_of_mem h.hz h.hu₁.1

theorem comm_z₂ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : z * u₂ = u₂ * z :=
  e189_commute_of_mem h.hzK' h.hu₂.1

theorem comm_z₃ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : z * u₃ = u₃ * z :=
  e189_commute_of_mem h.hzK₃ h.hu₃.1

theorem sq_12 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₂) * (u₁ * u₂) = 1 :=
  h.hB.2 _ T7B.mem_closure_fst

theorem sq_23 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : (u₂ * u₃) * (u₂ * u₃) = 1 :=
  h.hB.2 _ T7B.mem_closure_thd

theorem comm₁₂ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ = u₂ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₂ h.hz.sq h.comm_z₁ h.sq_12

theorem comm₂₃ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ = u₃ * u₂ :=
  T7B.comm_of_mul_self_eq_one h.sq₂ h.sq₃ h.hz.sq h.comm_z₂ h.sq_23

theorem eq_13 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ = z * ((u₁ * u₂) * (u₂ * u₃)) := by
  have h1 : (u₁ * u₂) * (u₂ * u₃) = u₁ * z * u₃ := by
    calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  calc u₁ * u₃ = (z * z) * (u₁ * u₃) := by rw [h.hz.sq, one_mul]
    _ = z * (z * u₁) * u₃ := by group
    _ = z * (u₁ * z) * u₃ := by rw [h.comm_z₁]
    _ = z * ((u₁ * u₂) * (u₂ * u₃)) := by rw [h1]; group

theorem mem_B_13 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [h.eq_13]
  exact Subgroup.mul_mem _ T7B.mem_closure_snd
    (Subgroup.mul_mem _ T7B.mem_closure_fst T7B.mem_closure_thd)

theorem sq_13 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₃) * (u₁ * u₃) = 1 :=
  h.hB.2 _ h.mem_B_13

theorem comm₁₃ (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ = u₃ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₃ h.hz.sq h.comm_z₁ h.sq_13

theorem closure_rotate (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
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
        calc u₁ * u₂ = (z * z) * (u₁ * u₂) := by rw [h.hz.sq, one_mul]
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

theorem rotate (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : Hyp22G Ω K' K₃ K z u₂ u₃ u₁ := by
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz h.hK'
  refine
    { hyp := h.hyp
      mem := h.hK'.1
      hz := h.hzK'
      subn := by rw [htw]; exact h.subn
      hK' := by rw [htw]; exact h.hK₃
      hne := h.hK₃K'
      hK₃ := by rw [htw]; exact mem_twinSet_self h.mem h.hz
      hK₃K := h.hne.symm
      hK₃K' := h.hK₃K.symm
      hu₁ := h.hu₂
      hu₂ := h.hu₃
      hu₃ := h.hu₁
      hB := ?_ }
  rw [h.closure_rotate]
  exact h.hB

theorem conj (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {g : G} (hg : g * z * g⁻¹ = z) :
    Hyp22G Ω (conjSub g K) (conjSub g K') (conjSub g K₃) z (g * u₁ * g⁻¹) (g * u₂ * g⁻¹)
      (g * u₃ * g⁻¹) := by
  have hcK : conjSub g K ∈ Ω := h.hyp.conjInvariant g K h.mem
  have hzc : IsUniqueInvolution (conjSub g K) z := by
    have := h.hz.conj g
    rwa [hg] at this
  have hmem : conjSub g K ∈ twinSet Ω K := ⟨hcK, z, h.hz, hzc⟩
  have htw : twinSet Ω (conjSub g K) = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz hmem
  have hB : Subgroup.closure ({(g * u₁ * g⁻¹) * (g * u₂ * g⁻¹), z,
        (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹)} : Set G) =
      conjSub g (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    rw [T7B.conjSub_closure_three, hg]
    have e1 : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    have e2 : (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹) = g * (u₂ * u₃) * g⁻¹ := by group
    rw [e1, e2]
  refine
    { hyp := h.hyp
      mem := hcK
      hz := hzc
      subn := by rw [htw]; exact h.subn
      hK' := twinSet_conj h.hyp.conjInvariant h.hK' g
      hne := fun e => h.hne (conjSub_injective g e)
      hK₃ := twinSet_conj h.hyp.conjInvariant h.hK₃ g
      hK₃K := fun e => h.hK₃K (conjSub_injective g e)
      hK₃K' := fun e => h.hK₃K' (conjSub_injective g e)
      hu₁ := ⟨conj_mem_conjSub h.hu₁.1, by rw [T7B.orderOf_conj']; exact h.hu₁.2⟩
      hu₂ := ⟨conj_mem_conjSub h.hu₂.1, by rw [T7B.orderOf_conj']; exact h.hu₂.2⟩
      hu₃ := ⟨conj_mem_conjSub h.hu₃.1, by rw [T7B.orderOf_conj']; exact h.hu₃.2⟩
      hB := ?_ }
  rw [hB]
  refine ⟨by rw [natCard_conjSub]; exact h.hB.1, fun x hx => ?_⟩
  have hx' := mem_conjSub_iff.mp hx
  have := h.hB.2 _ hx'
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem isElemAbelian2_closure [Finite G] (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z} : Set G)) 2 := by
  have hne : u₁ * u₂ ≠ z := by
    intro he
    refine Hyp22Core.not_mem_of_orderOf_four h.hyp h.mem h.hK'.1 h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h.hu₁.1) h.hz.mem
  have h1 : u₁ * u₂ ≠ 1 := by
    intro he
    refine Hyp22Core.not_mem_of_orderOf_four h.hyp h.mem h.hK'.1 h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h.hu₁.1
  have hcomm : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [h.comm_z₂]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [h.comm_z₁]
      _ = z * (u₁ * u₂) := by group
  exact T7A.isElemAbelian2_closure_pair h.sq_12 h.hz.sq h1 h.hz.ne_one hne hcomm

theorem of_core [Finite G] (h : Hyp22Core Ω K K' K₃ z u₁ u₂ u₃)
    (hsub : ∀ L ∈ twinSet Ω K, IsSubnormal L (Subgroup.centralizer ({z} : Set G))) :
    Hyp22G Ω K K' K₃ z u₁ u₂ u₃ where
  hyp := h.hyp
  mem := h.memK
  hz := h.hz
  subn := hsub
  hK' := ⟨h.memK', z, h.hz, h.hz'⟩
  hne := h.ne₁₂
  hK₃ := ⟨h.memK₃, z, h.hz, h.hz₃⟩
  hK₃K := h.ne₁₃
  hK₃K' := h.ne₂₃
  hu₁ := h.hu₁
  hu₂ := h.hu₂
  hu₃ := h.hu₃
  hB := h.isElemAbelian2_B

end Hyp22G

end CFSG.ClassicalInvolution.A7T22
