module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiBasic
public import CFSG.Goldschmidt.Steps.G37Proj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma commutatorElement_mul_of_commute {x y k l : G}
    (hky : k * y = y * k) (hkl : k * l = l * k) (hlx : l * x = x * l) :
    ⁅x * k, y * l⁆ = ⁅x, y⁆ := by
  have hkyl : ⁅k, y * l⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr hky,
      commutatorElement_eq_one_iff_mul_comm.mpr hkl]
    group
  have hxyl : ⁅x, y * l⁆ = ⁅x, y⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr hlx.symm]
    group
  rw [commutatorElement_mul_left_eq_conj_mul, hkyl, hxyl]
  group

private lemma sq_mul_of_commute {x k : G} (hkx : k * x = x * k) :
    (x * k) ^ 2 = x ^ 2 * k ^ 2 :=
  ((commute_iff_eq x k).mpr hkx.symm).mul_pow 2

namespace Gomi6Data

variable {A V C₀ C₁ : Subgroup G} {t u : G} (h : Gomi6Data A V C₀ C₁ t u)

include h

theorem hyp_Z4 : Nonempty (↥V ≃* Multiplicative (ZMod 4)) := by
  haveI : IsCyclic ↥V := by rw [h.V_eq]; infer_instance
  refine ⟨?_⟩
  have e : ↥V ≃* Multiplicative (ZMod (Nat.card ↥V)) :=
    (zmodCyclicMulEquiv (G := ↥V) inferInstance).symm
  rw [h.card_V] at e
  exact e

theorem hyp_relIndex : V.relIndex (A ⊔ V) = 16 := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := (⊥ : Subgroup G)) (K := V) (L := A ⊔ V)
    bot_le le_sup_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h.card_V, h.card_AV] at h1
  omega

theorem hyp_comm : ∀ a ∈ A ⊔ V, ∀ b ∈ A ⊔ V, ⁅a, b⁆ ∈ V := by
  intro a ha b hb
  obtain ⟨a1, ha1, v1, hv1, rfl⟩ := mem_sup_of_commute h.V_cent_A ha
  obtain ⟨a2, ha2, v2, hv2, rfl⟩ := mem_sup_of_commute h.V_cent_A hb
  have hu : u ∈ V := by rw [h.V_eq]; exact Subgroup.mem_zpowers u
  have hzV : zpowers (u ^ 2) ≤ V := Subgroup.zpowers_le.mpr (V.pow_mem hu 2)
  have hcomm : ⁅a1 * v1, a2 * v2⁆ = ⁅a1, a2⁆ :=
    commutatorElement_mul_of_commute (h.V_cent_A a2 ha2 v1 hv1).symm
      (h.V_comm v1 hv1 v2 hv2) (h.V_cent_A a1 ha1 v2 hv2).symm
  rw [hcomm]
  exact hzV (h.A_comm a1 ha1 a2 ha2)

theorem hyp_sq : ∀ a ∈ A ⊔ V, a ^ 2 ∈ V := by
  intro a ha
  obtain ⟨a1, ha1, v1, hv1, rfl⟩ := mem_sup_of_commute h.V_cent_A ha
  have hu : u ∈ V := by rw [h.V_eq]; exact Subgroup.mem_zpowers u
  have hzV : zpowers (u ^ 2) ≤ V := Subgroup.zpowers_le.mpr (V.pow_mem hu 2)
  rw [sq_mul_of_commute (h.V_cent_A a1 ha1 v1 hv1).symm]
  exact V.mul_mem (hzV (h.A_sq a1 ha1)) (V.pow_mem hv1 2)

theorem hyp_nonab : ¬ ∀ a ∈ A ⊔ V, ∀ b ∈ A ⊔ V, a * b = b * a := by
  rintro hc
  obtain ⟨a, ha, b, hb, hab⟩ := h.A_nonab
  exact hab (hc a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_left hb))

theorem hyp_t_norm_Gh : t ∈ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) :=
  CFSG.Goldschmidt.G37.normalizer_le_normalizer_centralizer' V h.t_mem_normalizer_V

theorem hyp_AV_le :
    A ⊔ V ≤ centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V := by
  rw [h.cent_inf_cs_eq]
  refine le_inf h.AV_le_cent (sup_le ?_ ?_)
  · refine (Subgroup.le_centralizer_iff.mpr ?_).trans
      (Subgroup.centralizer_le_normalizer (C₀ : Set G))
    rw [h.C0_eq]
    refine sup_le ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact h.V_cent_A a ha v hv
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a ha
      exact h.t_cent_A a ha
  · exact h.V_le_C0.trans (Subgroup.le_normalizer (H := C₀))

theorem hyp_cs_le :
    centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V ≤
      normalizer ((A ⊔ V : Subgroup G) : Set G) := by
  rw [h.cent_inf_cs_eq]
  exact inf_le_right.trans (h.N_C0_le.trans h.N_C1_le)

theorem hyp_comm_t : ∃ z ∈ V, ⁅z, t⁆ ≠ 1 := by
  have hu : u ∈ V := by rw [h.V_eq]; exact Subgroup.mem_zpowers u
  refine ⟨u, hu, ?_⟩
  have h' : t * u⁻¹ * t⁻¹ = u := by
    have h2 := congrArg Inv.inv h.t_inv
    simpa [mul_assoc] using h2
  have hcomm : ⁅u, t⁆ = u ^ 2 := by
    calc ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
      _ = u * u := by rw [h']
      _ = u ^ 2 := (pow_two u).symm
  rw [hcomm]
  exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h.u_order]; norm_num)

end Gomi6Data

end CFSG.OddStandard.HigherRank.YamadaG23
