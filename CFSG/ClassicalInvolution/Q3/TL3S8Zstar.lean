module

public import CFSG.ClassicalInvolution.Q3.TL3S8Std

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

theorem classicalInvolutionOddCore_eq_bot_of_fstar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) : classicalInvolutionOddCore G = ⊥ := by
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hFc : IsComponentOf (genFittingFStar G) ⊤ :=
    isComponentOf_top_of_normal_simple _ hnab
  have hC : Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  have : Group.IsSolvable (classicalInvolutionOddCore G) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card G)
  have hsub : IsSubnormal (classicalInvolutionOddCore G) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (genFittingFStar G) (classicalInvolutionOddCore G) hFc hsub
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at hcomm
  exact le_bot_iff.mp hcomm

theorem not_mem_center_of_fstar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) {z : G} (hz : z ≠ 1) :
    z ∉ Subgroup.center G := by
  intro hzc
  have hC : Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  have hzC : z ∈ Subgroup.centralizer (genFittingFStar G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hzc) g
  rw [hC, Subgroup.mem_bot] at hzC
  exact hz hzC

theorem genFittingFStar_le_of_normal [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) {N : Subgroup G} (hN : N.Normal) {x : G}
    (hxN : x ∈ N) (hx1 : x ≠ 1) : genFittingFStar G ≤ N := by
  have hFn : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hC : Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  have hNF : ((N ⊓ genFittingFStar G).subgroupOf (genFittingFStar G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hN.conj_mem _ hn.1 g, hFn.conj_mem _ hn.2 g⟩
  have := hNF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N ⊓ genFittingFStar G).subgroupOf (genFittingFStar G)) with h0 | h0
  · exfalso
    have hxC : x ∈ Subgroup.centralizer (genFittingFStar G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ genFittingFStar G := by
        refine ⟨?_, ?_⟩
        · have := hN.conj_mem x⁻¹ (N.inv_mem hxN) y
          have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [e]
          exact N.mul_mem hxN this
        · exact (genFittingFStar G).mul_mem (hFn.conj_mem y hy x)
            ((genFittingFStar G).inv_mem hy)
      have h2 : (⟨x * y * x⁻¹ * y⁻¹, h1.2⟩ : genFittingFStar G) ∈
          (N ⊓ genFittingFStar G).subgroupOf (genFittingFStar G) := Subgroup.mem_subgroupOf.mpr h1
      rw [h0, Subgroup.mem_bot] at h2
      have h3 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h2
      calc y * x = (x * y * x⁻¹ * y⁻¹) * (y * x) := by rw [h3, one_mul]
        _ = x * y := by group
        _ = x * y := rfl
    rw [hC, Subgroup.mem_bot] at hxC
    exact hx1 hxC
  · intro y hy
    have : (⟨y, hy⟩ : genFittingFStar G) ∈ (N ⊓ genFittingFStar G).subgroupOf (genFittingFStar G) :=
      h0 ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

namespace TightSylowStd

variable {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}

theorem exists_conj_mem_sylow_ne [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (h : TightSylowStd R S t T) :
    ∃ g : G, g * t * g⁻¹ ∈ (T : Subgroup G) ∧ g * t * g⁻¹ ≠ t := by
  have hodd : CFSG.oddCore G = ⊥ := classicalInvolutionOddCore_eq_bot_of_fstar hnab
  have hord : orderOf t = 2 := h.datum.order
  have hzS : t ∈ (T : Subgroup G) := h.mem_T
  have hzZ : (⟨t, hzS⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hTt s.2)
  have hne : t ≠ 1 := fun h1 => by
    have := hord
    rw [h1, orderOf_one] at this
    omega
  exact CFSG.ClassicalInvolution.exists_conj_mem_sylow_ne hodd T ⟨t, hzS⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact hord) (not_mem_center_of_fstar hnab hne)

end TightSylowStd

end CFSG.ClassicalInvolution.Q3
