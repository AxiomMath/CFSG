module

public import CFSG.ClassicalInvolution.Asc77.AscS16I

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.S22
open scoped commutatorElement

section Alpha

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem alpha_23V (h2 : C22_2V p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : V3Ab Ω K) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (closure_23_le h) (isElemAbelian2_closure_23 h)

theorem alpha_13V (h2 : C22_2V p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : V3Ab Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (closure_13_le h) (isElemAbelian2_closure_13 h)

theorem oddCore_le_normalizer_alphaV (h2 : C22_2V p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : V3Ab Ω K) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha (Hyp22Setting.isElemAbelian_B h) (natCard_B h)
    (B_le_centralizer h) (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2

theorem third_le_normalizer_alphaV (h2 : C22_2V p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : V3Ab Ω K) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := T7A.isSubnormal_centralizer hΩ hK₃Ω h.hzK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK hK₃Ω h.hK₃K.symm h.hz h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₁.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hc₂ : ⁅u₂, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK' hK₃Ω h.hK₃K'.symm h.hzK' h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₂.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hu₁C
  have hcomm : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have e : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ = (u₁ * ⁅u₂, ℓ⁆ * u₁⁻¹) * ⁅u₁, ℓ⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN _).mp hc₂) hc₁
  exact T7B.mem_normalizer_alphaOf_of_commutator h.sq_12 hzt hℓC hcomm
    (oddCore_le_normalizer_alphaV h2 h hb)

theorem le_normalizer_alphaV (h2 : C22_2V p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hb : V3Ab Ω K) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, third_le_normalizer_alphaV h2 h hb⟩
  · have := third_le_normalizer_alphaV h2 (rotate h) (V3Ab.of_twin h.hz h.hK' hb)
    rwa [alpha_23V h2 h hb] at this
  · have := third_le_normalizer_alphaV h2 (rotate (rotate h)) (V3Ab.of_twin h.hz h.hK₃ hb)
    rwa [← T7J.comm₁₃ h, alpha_13V h2 h hb] at this

theorem twin_le_normalizer_alphaV (h2 : C22_2V p f) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hb : V3Ab Ω K) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (le_normalizer_alphaV h2 h hb).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (le_normalizer_alphaV h2 h hb).2.1
  obtain ⟨w, hw⟩ := exists_replace_third h hL hLK hLK'
  exact third_le_normalizer_alphaV h2 hw hb

end Alpha

end S16

end CFSG.ClassicalInvolution.Asc77
