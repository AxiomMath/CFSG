module

public import CFSG.ClassicalInvolution.Q3.TwinLemma
public import CFSG.ClassicalInvolution.Generic.StepOdd
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem image_oddQuotient_isSubnormal {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsSubnormal K ⊤) :
    IsSubnormal (K.map (QuotientGroup.mk' (classicalInvolutionOddCore X))) ⊤ := by
  have h := Components.chain_map (QuotientGroup.mk' (classicalInvolutionOddCore X)) hK
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem oddCoreIn_top_quotient {X : Type} [Group X] [Finite X] :
    Balance.oddCoreIn (⊤ : Subgroup (X ⧸ classicalInvolutionOddCore X)) = ⊥ := by
  have h1 := OddCore.normal_intersection (X ⧸ classicalInvolutionOddCore X)
    (⊤ : Subgroup (X ⧸ classicalInvolutionOddCore X))
  have h2 : componentClassificationOddCore (X ⧸ classicalInvolutionOddCore X) = ⊥ :=
    OddCore.quotient_corefree X
  rw [Balance.oddCoreIn, h1, h2, inf_bot_eq]

theorem twin_modOdd3_images {X : Type} [Group X] [Finite X] {K J : Subgroup X} {z : X}
    (hK : IsSubnormal K ⊤) (hJ : IsSubnormal J ⊤) (hz : orderOf z = 2) (hzK : z ∈ K)
    (hzJ : z ∈ J) (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3))) :
    K.map (QuotientGroup.mk' (classicalInvolutionOddCore X)) =
        J.map (QuotientGroup.mk' (classicalInvolutionOddCore X)) ∨
      ⁅K, J⁆ ≤ classicalInvolutionOddCore X := by
  obtain ⟨e₁⟩ := eK
  obtain ⟨e₂⟩ := eJ
  set π := QuotientGroup.mk' (classicalInvolutionOddCore X) with hπ
  have eK' : ↥(K.map π) ≃* SL(2, ZMod 3) := (Components.oddCore_image_equiv K hK).symm.trans e₁
  have eJ' : ↥(J.map π) ≃* SL(2, ZMod 3) := (Components.oddCore_image_equiv J hJ).symm.trans e₂
  rcases Q3.twinLemma3 (C := ⊤) (J₁ := K.map π) (J₂ := J.map π) (z := π z)
      oddCoreIn_top_quotient (image_oddQuotient_isSubnormal hK) (image_oddQuotient_isSubnormal hJ)
      ⟨eK'⟩ ⟨eJ'⟩ (orderOf_mk_oddCore_eq_two hz) (Subgroup.mem_map_of_mem _ hzK)
      (Subgroup.mem_map_of_mem _ hzJ) with h | h
  · exact Or.inl h
  · right
    have h1 : (⁅K, J⁆).map π = ⊥ := by rw [Subgroup.map_commutator]; exact h
    have h2 : ⁅K, J⁆ ≤ π.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : π x ∈ (⁅K, J⁆).map π := Subgroup.mem_map_of_mem π hx
      rw [h1] at this
      exact Subgroup.mem_bot.mp this
    rwa [hπ, QuotientGroup.ker_mk'] at h2

theorem twin_modOdd3_core {X : Type} [Group X] [Finite X] {K J : Subgroup X} {z : X}
    (hK : IsSubnormal K ⊤) (hJ : IsSubnormal J ⊤) (hz : orderOf z = 2) (hzK : z ∈ K)
    (hzJ : z ∈ J) (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3)))
    (hNK : classicalInvolutionOddCore X ≤ K) (hNJ : classicalInvolutionOddCore X ≤ J) :
    K = J ∨ ⁅K, J⁆ ≤ classicalInvolutionOddCore X := by
  rcases twin_modOdd3_images hK hJ hz hzK hzJ eK eJ with h | h
  · left
    set π := QuotientGroup.mk' (classicalInvolutionOddCore X) with hπ
    have hker : π.ker ≤ K ⊓ J := fun x hx => by
      rw [hπ, QuotientGroup.ker_mk'] at hx
      exact ⟨hNK hx, hNJ hx⟩
    have key : ∀ {A B : Subgroup X}, π.ker ≤ B → A.map π = B.map π → A ≤ B := by
      intro A B hB hAB x hx
      have : π x ∈ B.map π := hAB ▸ Subgroup.mem_map_of_mem π hx
      obtain ⟨y, hy, hyx⟩ := this
      have hxy : y⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have := B.mul_mem hy (hB hxy)
      simpa using this
    exact le_antisymm (key (hker.trans inf_le_right) h) (key (hker.trans inf_le_left) h.symm)
  · exact Or.inr h

section InAmbient

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_top {C K : Subgroup G} (h : IsSubnormal K C) :
    IsSubnormal (K.subgroupOf C) ⊤ := by
  have := isSubnormal_subgroupOf h C
  rwa [Subgroup.subgroupOf_self] at this

noncomputable def quotEquivSubgroupOf {C K : Subgroup G} (hKC : K ≤ C) :
    (K.subgroupOf C ⧸ classicalInvolutionOddCore (K.subgroupOf C)) ≃*
      (K ⧸ classicalInvolutionOddCore K) :=
  let e' : K.subgroupOf C ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  QuotientGroup.congr _ _ e' (OddCore.equiv_invariant e')

theorem nonempty_quotEquiv_subgroupOf {C K : Subgroup G} (hKC : K ≤ C) {A : Type*} [Group A]
    (e : K ⧸ classicalInvolutionOddCore K ≃* A) :
    Nonempty (K.subgroupOf C ⧸ classicalInvolutionOddCore (K.subgroupOf C) ≃* A) :=
  ⟨(quotEquivSubgroupOf hKC).trans e⟩

variable [Finite G]

theorem twin_modOdd3 {C K J : Subgroup G} {z : G} (hKC : IsSubnormal K C)
    (hJC : IsSubnormal J C) (hz : orderOf z = 2) (hzK : z ∈ K) (hzJ : z ∈ J)
    (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3)))
    (hNK : Balance.oddCoreIn C ≤ K) (hNJ : Balance.oddCoreIn C ≤ J) :
    K = J ∨ ⁅K, J⁆ ≤ Balance.oddCoreIn C := by
  have hKle : K ≤ C := isSubnormal_le hKC
  have hJle : J ≤ C := isSubnormal_le hJC
  obtain ⟨e₁⟩ := eK
  obtain ⟨e₂⟩ := eJ
  have hz' : orderOf (⟨z, hKle hzK⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hN : ∀ {M : Subgroup G}, Balance.oddCoreIn C ≤ M →
      classicalInvolutionOddCore C ≤ M.subgroupOf C := fun {M} hM x hx =>
    Subgroup.mem_subgroupOf.mpr (hM ⟨x, hx, rfl⟩)
  rcases twin_modOdd3_core (K := K.subgroupOf C) (J := J.subgroupOf C)
      (z := (⟨z, hKle hzK⟩ : C)) (isSubnormal_subgroupOf_top hKC) (isSubnormal_subgroupOf_top hJC)
      hz' (Subgroup.mem_subgroupOf.mpr hzK) (Subgroup.mem_subgroupOf.mpr hzJ)
      (nonempty_quotEquiv_subgroupOf hKle e₁) (nonempty_quotEquiv_subgroupOf hJle e₂)
      (hN hNK) (hN hNJ) with h | h
  · left
    have := congrArg (Subgroup.map C.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hKle, Subgroup.map_subgroupOf_eq_of_le hJle] at this
  · right
    have hmap : ⁅K, J⁆ = (⁅K.subgroupOf C, J.subgroupOf C⁆).map C.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKle,
        Subgroup.map_subgroupOf_eq_of_le hJle]
    rw [hmap]
    exact Subgroup.map_mono h

theorem twin_modOdd3_weak {C K J : Subgroup G} {z : G} (hKC : IsSubnormal K C)
    (hJC : IsSubnormal J C) (hz : orderOf z = 2) (hzK : z ∈ K) (hzJ : z ∈ J)
    (eK : Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)))
    (eJ : Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3))) :
    K ⊔ Balance.oddCoreIn C = J ⊔ Balance.oddCoreIn C ∨ ⁅K, J⁆ ≤ Balance.oddCoreIn C := by
  have hKle : K ≤ C := isSubnormal_le hKC
  have hJle : J ≤ C := isSubnormal_le hJC
  obtain ⟨e₁⟩ := eK
  obtain ⟨e₂⟩ := eJ
  have hz' : orderOf (⟨z, hKle hzK⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hNC : Balance.oddCoreIn C ≤ C := Balance.oddCoreIn_le C
  rcases twin_modOdd3_images (K := K.subgroupOf C) (J := J.subgroupOf C)
      (z := (⟨z, hKle hzK⟩ : C)) (isSubnormal_subgroupOf_top hKC) (isSubnormal_subgroupOf_top hJC)
      hz' (Subgroup.mem_subgroupOf.mpr hzK) (Subgroup.mem_subgroupOf.mpr hzJ)
      (nonempty_quotEquiv_subgroupOf hKle e₁) (nonempty_quotEquiv_subgroupOf hJle e₂) with h | h
  · left
    set π := QuotientGroup.mk' (classicalInvolutionOddCore C) with hπ
    have key : ∀ {A B : Subgroup G}, A ≤ C →
        (A.subgroupOf C).map π = (B.subgroupOf C).map π → A ≤ B ⊔ Balance.oddCoreIn C := by
      intro A B hAC hAB x hx
      have hxC : x ∈ C := hAC hx
      have h1 : π ⟨x, hxC⟩ ∈ (B.subgroupOf C).map π :=
        hAB ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
      obtain ⟨y, hy, hyx⟩ := h1
      have hker : y⁻¹ * ⟨x, hxC⟩ ∈ classicalInvolutionOddCore C := by
        have : π (y⁻¹ * ⟨x, hxC⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      have hmem : ((y⁻¹ * ⟨x, hxC⟩ : ↥C) : G) ∈ Balance.oddCoreIn C := ⟨_, hker, rfl⟩
      have hyB : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
      have hxy : (y : G) * ((y⁻¹ * ⟨x, hxC⟩ : ↥C) : G) = x := by simp
      rw [← hxy]
      exact Subgroup.mul_mem_sup hyB hmem
    exact le_antisymm (sup_le (key hKle h) le_sup_right) (sup_le (key hJle h.symm) le_sup_right)
  · right
    have hmap : ⁅K, J⁆ = (⁅K.subgroupOf C, J.subgroupOf C⁆).map C.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKle,
        Subgroup.map_subgroupOf_eq_of_le hJle]
    rw [hmap]
    exact Subgroup.map_mono h

end InAmbient

end CFSG.ClassicalInvolution.Uniform
