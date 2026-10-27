module

public import CFSG.LargeExtraspecial.S9RBPCaseC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem index_Abar : ((S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g)).index = 4 := by
  have h1 := Subgroup.card_mul_index ((S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g))
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, C.card_Lbar] at h1
  have h2 := T.data.card_Abar
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
  have h3 : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      ((S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g)).index =
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 := by rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem exists_sub_mem (hNo : NoA2 S g)
    (hKN : ∀ k ∈ Rbar S g t, (∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) → k ∈ Nbar S g t)
    {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {w₂ : S.Qt} (hw₂ : w₂ ∈ Wt S g t)
    (h0 : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ≠ 0)
    (hf : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈ fixMod S (S.Lbar ((h : G) * g)) (Vt S g t))
    {z : S.Qt} (hz : z ∈ (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
      fixMod S (S.Lbar g) (Vt S g t)) :
    ∃ l ∈ S.Lbar g, ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) -
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂)) - z ∈ Vt S g t := by
  classical
  have haQ := H.conj_mem
  set U := Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  set Ta := U ⊓ fixMod S (S.Lbar g) (Vt S g t) with hTa
  set u' := (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ with hu'
  have hu'U : u' ∈ U := Submodule.mem_sup_right (sub_mem_commSpace _ _)
  have hu'W : u' ∈ Wt S g t := T.U_le_Wt hu'U
  have hmemT : ∀ l : S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ Ta := fun l =>
    T.sub_mem_Fix H C (cl_a_mem_Vt ht) (Lbar_le_Rbar ht) hu'U l.2
  let F : S.Lbar g → ↥(Ta.map (Vt S g t).mkQ) := fun l =>
    ⟨(Vt S g t).mkQ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u'), Submodule.mem_map_of_mem (hmemT l)⟩
  have hFeq : ∀ a b : S.Lbar g, F a = F b ↔
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - (b : S.Qt ≃ₗ[ZMod 2] S.Qt) u' ∈ Vt S g t := by
    intro a b
    simp only [F, Subtype.mk.injEq, Submodule.mkQ_apply, Submodule.Quotient.eq]
    rw [show (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' - ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u') =
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - (b : S.Qt ≃ₗ[ZMod 2] S.Qt) u' by abel]
  have hdiff' : ∀ (a b : S.Lbar g) (y : S.Qt),
      ((((a⁻¹ * b : S.Lbar g) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y =
        (((a : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) y - (a : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
    intro a b y
    rw [map_sub, inv_apply_apply_O]
    rfl
  have hdiff := fun a b => hdiff' a b u'
  have hconst : ∀ a b : S.Lbar g, a⁻¹ * b ∈ (S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g) →
      F a = F b := by
    intro a b hab
    rw [hFeq]
    have h1 := T.data.N0bar_apply (Lbar_inf_Nbar_le_N0bar (mem_subgroupOf.mp hab)) hu'W
    rw [hdiff] at h1
    have h2 := apply_mem_Vt_of_mem_Rbar haQ (Lbar_le_Rbar ht a.2) h1
    rw [apply_inv_apply_O] at h2
    have := neg_mem h2
    rwa [neg_sub] at this
  have hinj : ∀ a b : S.Lbar g, F a = F b →
      a⁻¹ * b ∈ (S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g) := by
    intro a b hab
    rw [hFeq] at hab
    have hm : ((a⁻¹ * b : S.Lbar g) : S.O) ∈ Rbar S g t := Lbar_le_Rbar ht (a⁻¹ * b).2
    have hmu : ((((a⁻¹ * b : S.Lbar g) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ Vt S g t := by
      rw [hdiff]
      have := apply_mem_Vt_of_mem_Rbar haQ (inv_mem (Lbar_le_Rbar ht a.2)) (neg_mem hab)
      rwa [neg_sub] at this
    have hmT : ∀ x ∈ Ta, ((((a⁻¹ * b : S.Lbar g) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈
        Vt S g t := fun x hx => hx.2 _ (a⁻¹ * b).2
    have hN := hKN _ hm (T.gen hNo hh hb hw₂ h0 hf hm hmT hmu)
    exact mem_subgroupOf.mpr ⟨(a⁻¹ * b).2, hN⟩
  set Ab := (S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g) with hAb
  let Fq : S.Lbar g ⧸ Ab → ↥(Ta.map (Vt S g t).mkQ) := fun q => Quotient.liftOn' q F
    fun a b hab => hconst a b (QuotientGroup.leftRel_apply.mp hab)
  have hFq : Function.Injective Fq := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr (hinj a b h)
  have hVT : Vt S g t ≤ Ta := le_inf le_sup_left fun v hv l hl =>
    sub_mem (apply_mem_Vt_of_mem_Rbar haQ (Lbar_le_Rbar ht hl) hv) hv
  have hdT := finrank_map_mkQ_add hVT
  have dTa : finrank (ZMod 2) Ta = finrank (ZMod 2) (Vt S g t) + 2 := T.finrank_Fix hNo
  have hcardT : Nat.card ↥(Ta.map (Vt S g t).mkQ) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have : finrank (ZMod 2) ↥(Ta.map (Vt S g t).mkQ) = 2 := by omega
    rw [this]; norm_num
  have hcardQ : Nat.card (S.Lbar g ⧸ Ab) = 4 := T.index_Abar
  have : Finite ↥(Ta.map (Vt S g t).mkQ) := Module.finite_of_finite (ZMod 2)
  have hbij := hFq.bijective_of_nat_card_le (by rw [hcardT, hcardQ])
  obtain ⟨q, hq⟩ := hbij.2 ⟨(Vt S g t).mkQ z, Submodule.mem_map_of_mem hz⟩
  induction q using QuotientGroup.induction_on with | H l => ?_
  refine ⟨l, l.2, ?_⟩
  have h1 := congrArg Subtype.val hq
  change (Vt S g t).mkQ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u') = (Vt S g t).mkQ z at h1
  exact (Submodule.Quotient.eq _).mp h1

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
