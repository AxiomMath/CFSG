module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwoTuple
public import CFSG.LocalAnalysis.EvenBN.U4.RootF2Two

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem F2_le_RG (_hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ≤ miyamotoRG h L η t Q :=
  inf_le_right

theorem F2_sup_V2 (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ⊔ (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) =
      miyamotoRG h L η t Q := by
  set V := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) with hV
  have hVN : V ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    inf_le_left.trans hS.RG_le_normalizer_F2
  have h1 := card_sup_mul_card_inf_eq hVN
  have hinf : miyamotoF2G h L η t Q ⊓ V = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← hS.F2_inf_centralizer_I2]
    exact mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (mem_inf.1 hx).2).2⟩
  rw [hinf, card_bot, mul_one, hS.card_F2, hS.card_V2] at h1
  refine Subgroup.eq_of_le_of_card_ge (sup_le hS.F2_le_RG inf_le_left) ?_
  rw [h1, hS.card_miyamotoRG]
  ring_nf
  exact le_rfl

theorem N2G_le_centralizer_E (hS : Setting h L η t Q T) :
    miyamotoN2G h L η ≤ centralizer (miyamotoEG h L η Q : Set G) :=
  hS.N2G_le_centralizer_Y.trans (centralizer_le (SetLike.coe_subset_coe.2 hS.E_le_Y))

theorem normalizer_F2_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer (miyamotoF2G h L η t Q : Set G) ≤
      normalizer (miyamotoEG h L η Q : Set G) := by
  have key : ∀ x ∈ normalizer (miyamotoF2G h L η t Q : Set G), ∀ e ∈ miyamotoEG h L η Q,
      x * e * x⁻¹ ∈ miyamotoEG h L η Q := by
    intro x hx e he
    rw [← hS.centerIn_F2] at he ⊢
    obtain ⟨heF, heC⟩ := mem_inf.1 he
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hx e).1 heF, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : x⁻¹ * y * x ∈ miyamotoF2G h L η t Q := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 heC _ hy'
    calc y * (x * e * x⁻¹) = x * ((x⁻¹ * y * x) * e) * x⁻¹ := by group
      _ = x * (e * (x⁻¹ * y * x)) * x⁻¹ := by rw [hc]
      _ = x * e * x⁻¹ * y := by group
  intro x hx
  rw [mem_normalizer_iff]
  intro e
  refine ⟨key x hx e, fun he => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ he
  rwa [inv_inv, show x⁻¹ * (x * e * x⁻¹) * x = e by group] at this

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
