module

public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscT7BBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T7B

variable {G : Type} [Group G]

theorem centralizer_le_normalizer_alphaOf (E : Subgroup G) :
    Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (alphaOf E : Set G) := by
  intro c hc
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub c E = E := T7A.conjSub_eq_self_of_mem_centralizer hc
  have h2 := alphaOf_conjSub c E
  rw [h1] at h2
  exact h2.symm

variable [Finite G]

theorem mem_normalizer_alphaOf_of_commutator {t z ℓ : G} (ht2 : t * t = 1) (hzt : z * t = t * z)
    (hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G))
    (hcomm : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)))
    (hO : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G)) :
    ℓ ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    ht2 (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hcomm
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hoO
  have hcz : ℓ * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hℓC hoC
  have hct : (ℓ * o) * t = t * (ℓ * o) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hcE : ℓ * o ∈ Subgroup.centralizer
      ((Subgroup.closure ({t, z} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.centralizer ({ℓ * o} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hcz).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hcN := centralizer_le_normalizer_alphaOf _ hcE
  have h2 : (ℓ * o) * o⁻¹ ∈
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ (hO hoO))
  rwa [mul_inv_cancel_right] at h2

end T7B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

namespace Hyp22

theorem comm_gen (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
  have hc12 : Commute u₁ u₂ := h.comm₁₂
  have hc13 : Commute u₁ u₃ := h.comm₁₃
  have hc23 : Commute u₂ u₃ := h.comm₂₃
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)
  have hmix : Commute (u₁ * u₂) (u₂ * u₃) :=
    Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hcu₁₂.eq
  · exact hmix.eq
  · exact hcu₁₂.symm.eq
  · rfl
  · exact hcu₂₃.symm.eq
  · exact hmix.symm.eq
  · exact hcu₂₃.eq
  · rfl

theorem isElemAbelian_B (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian 2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  have hcomm := T7A.commutes_closure h.comm_gen
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact h.hB.2 x hx

theorem B_le_centralizer (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq

theorem isElemAbelian2_closure_23 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₂ * u₃, z} : Set G)) 2 :=
  h.rotate.isElemAbelian2_closure

theorem closure_23_le (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_thd
  · exact T7B.mem_closure_snd

theorem closure_12_le (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_fst
  · exact T7B.mem_closure_snd

theorem closure_13_le (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h.mem_B_13
  · exact T7B.mem_closure_snd

theorem isElemAbelian2_closure_13 (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₃, z} : Set G)) 2 := by
  have h' := h.rotate.rotate.isElemAbelian2_closure
  rwa [← h.comm₁₃] at h'

theorem natCard_B (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Nat.card ↥(Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) = 8 := by
  have := h.hB.1
  norm_num at this
  exact this

section Alpha22

variable [IsSimpleGroup G]

theorem alpha_23 (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2 _ h.closure_23_le h.isElemAbelian2_closure_23

theorem alpha_13 (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2 _ h.closure_13_le h.isElemAbelian2_closure_13

theorem oddCore_le_normalizer_alpha (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha h.isElemAbelian_B h.natCard_B h.B_le_centralizer
    (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2

theorem third_le_normalizer_alpha (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK' : K' ∈ Ω := h.std.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := T7A.isSubnormal_centralizer hΩ hK₃Ω h.hzK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK hK₃Ω h.hK₃K.symm h.std.hz h.hzK₃
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
    (h.oddCore_le_normalizer_alpha h2)

theorem le_normalizer_alpha (h2 : C22_2 p f) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, h.third_le_normalizer_alpha h2⟩
  · have := h.rotate.third_le_normalizer_alpha h2
    rwa [h.alpha_23 h2] at this
  · have := h.rotate.rotate.third_le_normalizer_alpha h2
    rwa [← h.comm₁₃, h.alpha_13 h2] at this

end Alpha22

end Hyp22

end CFSG.ClassicalInvolution.Asc77
