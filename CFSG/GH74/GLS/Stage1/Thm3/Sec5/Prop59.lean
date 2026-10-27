module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem prop59_aux (hII : II4_4_4_center) (hF : FStar_C) (h95 : III2_9_5_r2)
    (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) {a : G} (ha : a ∈ Qof S K₁)
    (ha2 : orderOf a = 2) (haz : a ≠ z) : a ∉ commBar z := by
  intro hcomm
  have hM := m4_of_std hII h
  have haS : a ∈ S := ha.1
  have hc1 : a ∈ cSec K₁ := ha.2
  have hn1 : a ∈ normalizer (K₁ : Set G) := hc1.1
  have haC : a ∈ Cz z := S_le_Cz hM haS
  have hn2 : a ∈ normalizer (K₂ : Set G) := normalizer_other hM h.ne haC hn1
  have hin1 : InducesInner a K₁ := ⟨1, K₁.one_mem, by simpa using hc1⟩
  have hin2 : InducesInner a K₂ := h95 G z S K₁ K₂ h hQ a haS ha2 hcomm hn1 hn2 hin1
  obtain ⟨k, hk, hck⟩ := hin2
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hkC : k ∈ Cz z := hK₂C hk
  have hcC : a * k⁻¹ ∈ Cz z := mul_mem haC (inv_mem hkC)
  have hcs1 : a * k⁻¹ ∈ cSec K₁ := mul_mem hc1 (inv_mem (hM.cs₁ hk))
  have hP1 : pPrimeCoreOf 2 K₁ ≤ Oz z := pPrimeCoreOf_le_Oz (h.comp_isPCompIn (Or.inl rfl))
  have hP2 : pPrimeCoreOf 2 K₂ ≤ Oz z := pPrimeCoreOf_le_Oz (h.comp_isPCompIn (Or.inr rfl))
  have hcomm' : ∀ k' ∈ K₁ ⊔ K₂, ⁅k', a * k⁻¹⁆ ∈ Oz z :=
    forall_comm_mem_sup hK₁C hK₂C (fun x hx n hn => Oz_conj hx hn)
      (fun k' hk' => hP1 (hcs1.2.2 k' hk')) (fun k' hk' => hP2 (hck.2.2 k' hk'))
  have hfs := hF G z S K₁ K₂ h hQ (a * k⁻¹) hcC hcomm'
  have hzK₂ : z ∈ K₂ := hM.z_mem_comp (Or.inr rfl)
  have hOle : zpowers z ⊔ Oz z ≤ K₂ ⊔ Oz z := sup_le_sup_right (zpowers_le.2 hzK₂) _
  have haK₂O : a ∈ K₂ ⊔ Oz z := by
    have h1 : a = a * k⁻¹ * k := by group
    rw [h1]
    exact mul_mem (hOle hfs) (mem_sup_left hk)
  have hSyl := Pof_card hM (K := K₂) (Or.inr rfl)
  have hinf := inf_sup_le_of_odd hM.S_pgroup hSyl card_Oz_odd (le_normalizer_Oz hK₂C)
  have haK₂ : a ∈ K₂ := hinf ⟨haS, haK₂O⟩
  exact haz (eq_of_pRank_one (h.comp_pRank (Or.inr rfl)) haK₂ hzK₂ ha2 h.orderOf_z
    (Subgroup.mem_centralizer_singleton_iff.1 haC))

theorem prop_5_9 (hII : II4_4_4_center) (hF : FStar_C) (h95 : III2_9_5_r2) (h41 : Prop4_1) :
    Prop5_9 := by
  intro G _ _ z S K₁ K₂ h K hK _ a haQ ha2 haz
  have hQ : Qz S z = zpowers z := (h41 G z S K₁ K₂ h).1
  rcases hK with rfl | hK
  · exact prop59_aux hII hF h95 h hQ haQ ha2 haz
  · rw [Set.mem_singleton_iff] at hK
    subst hK
    exact prop59_aux hII hF h95 h.swap hQ haQ ha2 haz

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
