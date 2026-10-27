module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Lift4Group
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem Hyp.exists_equiv_unip_V {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : Hyp G A) (d : Datum A) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      Nonempty (↥(d.P ⊓ A) ≃* ↥(unipAll k)) := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  exact exists_equiv_unip_of_isSylowOf h.odd e d.V_isSylow

theorem Hyp.card_V {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : Hyp G A) (d : Datum A) : Nat.card ↥(d.P ⊓ A) = 64 := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := h.exists_equiv_unip_V d
  rw [Nat.card_congr e.toEquiv, card_unipAll, hk]
  norm_num

section Lift

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

omit [Finite G] in
theorem exists_conj_of_mul_self {g : G} (hg : g ∈ S₀) (hgt : (g * d.t) * (g * d.t) = 1) :
    ∃ f ∈ S₀, f⁻¹ * d.t * f = g * d.t :=
  S.free.exists_conj d.t_mul_self hg hgt

theorem card_inf_centralizer_t : Nat.card ↥(S₀ ⊓ centralizer ({d.t} : Set G)) = 64 := by
  have h := S.free.card_centralizer_sq d.t_mul_self
  have h2 : Nat.card ↥(S₀ ⊓ centralizer ({d.t} : Set G)) ^ 2 = 64 ^ 2 := by
    rw [h, S.card_S₀]
    norm_num
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2

theorem inf_centralizer_t_eq_V (h : Hyp G A) :
    S₀ ⊓ centralizer ({d.t} : Set G) = d.P ⊓ A := by
  have hle : d.P ⊓ A ≤ S₀ ⊓ centralizer ({d.t} : Set G) :=
    le_inf S.V_le_S₀ fun v hv => mem_centralizer_singleton_iff.mpr (d.V_comm_t hv)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [S.card_inf_centralizer_t, h.card_V d]


theorem exists_involution_sq (h : Hyp G A) {x₀ : G}
    (hnorm : ∀ s, s ∈ S₀ ↔ x₀ * s * x₀⁻¹ ∈ S₀) (hcomm : x₀ * d.t * x₀⁻¹ * d.t⁻¹ ∈ S₀)
    (hsq : d.t⁻¹ * (x₀ * x₀) ∈ S₀) :
    ∃ x₁ : G, x₀⁻¹ * x₁ ∈ S₀ ∧ (x₁ * x₁) * (x₁ * x₁) = 1 ∧ IsConj d.t (x₁ * x₁) := by
  have ht2 := d.t_mul_self
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨k, _, _, hk4, ⟨e⟩⟩ := h.exists_equiv_unip_V d
  have hV := S.inf_centralizer_t_eq_V h
  have htS₁ := S.t_mem_S₁
  rw [htinv] at hcomm hsq
  have hgt : (x₀ * d.t * x₀⁻¹ * d.t) * d.t = x₀ * d.t * x₀⁻¹ := by
    rw [mul_assoc _ d.t d.t, ht2, mul_one]
  have h1 : ((x₀ * d.t * x₀⁻¹ * d.t) * d.t) * ((x₀ * d.t * x₀⁻¹ * d.t) * d.t) = 1 := by
    rw [hgt]
    calc x₀ * d.t * x₀⁻¹ * (x₀ * d.t * x₀⁻¹) = x₀ * (d.t * d.t) * x₀⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨f, hfS, hf⟩ := S.exists_conj_of_mul_self hcomm h1
  rw [hgt] at hf
  obtain ⟨x, hx⟩ : ∃ x, x = f * x₀ := ⟨_, rfl⟩
  have hxt : x * d.t = d.t * x := by
    calc x * d.t = f * (x₀ * d.t * x₀⁻¹) * x₀ := by rw [hx]; group
      _ = f * (f⁻¹ * d.t * f) * x₀ := by rw [hf]
      _ = d.t * x := by rw [hx]; group
  have hxt' : x⁻¹ * d.t = d.t * x⁻¹ := by
    calc x⁻¹ * d.t = x⁻¹ * (d.t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * d.t) * x⁻¹ := by rw [hxt]
      _ = d.t * x⁻¹ := by group
  have hnormx : ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀ := by
    intro s
    have e1 : x * s * x⁻¹ = f * (x₀ * s * x₀⁻¹) * f⁻¹ := by rw [hx]; group
    rw [e1]
    constructor
    · intro hs
      exact S₀.mul_mem (S₀.mul_mem hfS ((hnorm s).1 hs)) (S₀.inv_mem hfS)
    · intro hs
      have : x₀ * s * x₀⁻¹ ∈ S₀ := by
        have := S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hfS) hs) hfS
        simpa [mul_assoc] using this
      exact (hnorm s).2 this
  have hcomm_iff : ∀ y, (x * y * x⁻¹ * d.t = d.t * (x * y * x⁻¹)) ↔ y * d.t = d.t * y := by
    intro y
    have e1 : x * y * x⁻¹ * d.t = x * (y * d.t) * x⁻¹ := by
      calc x * y * x⁻¹ * d.t = x * y * (x⁻¹ * d.t) := by rw [mul_assoc]
        _ = x * y * (d.t * x⁻¹) := by rw [hxt']
        _ = x * (y * d.t) * x⁻¹ := by group
    have e2 : d.t * (x * y * x⁻¹) = x * (d.t * y) * x⁻¹ := by
      calc d.t * (x * y * x⁻¹) = (d.t * x) * y * x⁻¹ := by group
        _ = (x * d.t) * y * x⁻¹ := by rw [hxt]
        _ = x * (d.t * y) * x⁻¹ := by group
    rw [e1, e2]
    exact ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => by rw [h]⟩
  have hnormV : ∀ y, y ∈ d.P ⊓ A ↔ x * y * x⁻¹ ∈ d.P ⊓ A := by
    intro y
    rw [← hV, mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← hnormx y]
    exact and_congr_right fun _ => (hcomm_iff y).symm
  have hVt : ∀ y ∈ d.P ⊓ A, d.t * y = y * d.t := fun y hy => (d.V_comm_t hy).symm
  have hvS : d.t * (x * x) ∈ S₀ := by
    have e1 : d.t * (x * x) = (d.t * (f * (x₀ * f * x₀⁻¹)) * d.t⁻¹) * (d.t * (x₀ * x₀)) := by
      rw [htinv, hx]
      calc d.t * (f * x₀ * (f * x₀)) = d.t * (f * (x₀ * f * x₀⁻¹)) * (x₀ * x₀) := by group
        _ = (d.t * (f * (x₀ * f * x₀⁻¹)) * d.t) * (d.t * (x₀ * x₀)) := by
          rw [mul_assoc _ d.t (d.t * _), ← mul_assoc d.t d.t, ht2, one_mul]
    rw [e1]
    have hf₂ : f * (x₀ * f * x₀⁻¹) ∈ S₀ := S₀.mul_mem hfS ((hnorm f).1 hfS)
    have hS₀t : ∀ s ∈ S₀, d.t * s * d.t⁻¹ ∈ S₀ := fun s hs => S.S₀_normal d.t htS₁ s hs
    exact S₀.mul_mem (hS₀t _ hf₂) hsq
  have hvC : d.t * (x * x) ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc d.t * (x * x) * d.t = d.t * (x * (x * d.t)) := by group
      _ = d.t * (x * (d.t * x)) := by rw [hxt]
      _ = d.t * ((x * d.t) * x) := by group
      _ = d.t * ((d.t * x) * x) := by rw [hxt]
      _ = d.t * (d.t * (x * x)) := by group
  have hv : d.t * (x * x) ∈ d.P ⊓ A := by
    rw [← hV]
    exact ⟨hvS, hvC⟩
  have hxv : x * x = d.t * (d.t * (x * x)) := by rw [← mul_assoc d.t d.t, ht2, one_mul]
  obtain ⟨s, hsV, v', hv'V, hs, hv'⟩ := exists_order_four_lift hk4 e hnormV ht2 hxt.symm hVt hv hxv
  have hsS : s ∈ S₀ := S.V_le_S₀ hsV
  have hv'S : v' ∈ S₀ := S.V_le_S₀ hv'V
  have hv't : v' * d.t = d.t * v' := d.V_comm_t hv'V
  have hsq' : (x * s * (x * s)) * (x * s * (x * s)) = 1 := by
    rw [hs]
    calc d.t * v' * (d.t * v') = d.t * (v' * d.t) * v' := by group
      _ = d.t * (d.t * v') * v' := by rw [hv't]
      _ = (d.t * d.t) * (v' * v') := by group
      _ = 1 := by rw [ht2, hv', one_mul]
  refine ⟨x * s, ?_, hsq', ?_⟩
  · have e1 : x₀⁻¹ * (x * s) = (x₀⁻¹ * f * x₀) * s := by rw [hx]; group
    rw [e1]
    refine S₀.mul_mem ?_ hsS
    have e2 : x₀ * (x₀⁻¹ * f * x₀) * x₀⁻¹ = f := by group
    exact (hnorm (x₀⁻¹ * f * x₀)).2 (by rw [e2]; exact hfS)
  · have h2 : (v' * d.t) * (v' * d.t) = 1 := by
      rw [hv't]
      calc d.t * v' * (d.t * v') = d.t * (v' * d.t) * v' := by group
        _ = d.t * (d.t * v') * v' := by rw [hv't]
        _ = (d.t * d.t) * (v' * v') := by group
        _ = 1 := by rw [ht2, hv', one_mul]
    obtain ⟨f', -, hf'⟩ := S.exists_conj_of_mul_self hv'S h2
    refine isConj_iff.mpr ⟨f'⁻¹, ?_⟩
    rw [inv_inv, hf', hs, hv't]

end SylowA

end Lift

end CFSG.OddStandard.Seitz77
