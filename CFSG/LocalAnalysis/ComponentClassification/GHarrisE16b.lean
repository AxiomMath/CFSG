module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC10

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

namespace ThmC

theorem ut_comm_E (u : UT3 F4c) {w : UT3 F4c} (hw : w.b = 0) :
    w⁻¹ * (u * w * u⁻¹) = ⟨0, 0, w.a * u.b⟩ := by
  obtain ⟨wa, wb, wc⟩ := w
  change wb = 0 at hw
  subst hw
  rw [ut_conj]
  ext : 1 <;> simp only [UT3.mul_def, UT3.inv_def] <;> ring

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

theorem mem_Z_of_comm_of_not_mem {e x : X} (he : e ∈ D.E) (hx : x ∈ (D.T : Subgroup X))
    (hxE : x ∉ D.E) (hc : e * x = x * e) : e ∈ D.Z := by
  obtain ⟨w, hw, rfl⟩ := he
  obtain ⟨u, rfl⟩ := D.exists_toX hx
  have hub : u.b ≠ 0 := fun h => hxE (D.toX_mem_E_iff.mpr h)
  rw [← map_mul, ← map_mul] at hc
  have h := (ut_mul_comm_iff w u).mp (D.toX_injective hc)
  rw [mem_Eu.mp hw, mul_zero] at h
  exact ⟨w, mem_Zu.mpr ⟨(mul_eq_zero.mp h).resolve_right hub, mem_Eu.mp hw⟩, rfl⟩

theorem exists_E_conj_eq {x z : X} (hx : x ∈ (D.T : Subgroup X)) (hxE : x ∉ D.E)
    (hz : z ∈ D.Z) : ∃ e ∈ D.E, e⁻¹ * (x * e * x⁻¹) = z := by
  obtain ⟨u, rfl⟩ := D.exists_toX hx
  obtain ⟨v, hv, rfl⟩ := hz
  obtain ⟨hva, hvb⟩ := mem_Zu.mp hv
  have hub : u.b ≠ 0 := fun h => hxE (D.toX_mem_E_iff.mpr h)
  refine ⟨D.toX ⟨v.c / u.b, 0, 0⟩, D.toX_mem_E_iff.mpr rfl, ?_⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    ut_comm_E u (w := ⟨v.c / u.b, 0, 0⟩) rfl]
  congr 1
  ext : 1
  · exact hva.symm
  · exact hvb.symm
  · exact div_mul_cancel₀ v.c hub

theorem le_Z_or_Z_le {N : Subgroup X} (hNE : N ≤ D.E)
    (hNT : ∀ t ∈ (D.T : Subgroup X), ∀ n ∈ N, t * n * t⁻¹ ∈ N) : N ≤ D.Z ∨ D.Z ≤ N := by
  by_cases h : N ≤ D.Z
  · exact Or.inl h
  right
  obtain ⟨n, hn, hnZ⟩ := Set.not_subset.mp h
  obtain ⟨w, hw, rfl⟩ := hNE hn
  have hwa : w.a ≠ 0 := fun ha => hnZ ⟨w, mem_Zu.mpr ⟨ha, mem_Eu.mp hw⟩, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨hva, hvb⟩ := mem_Zu.mp hv
  have h2 : (D.toX w)⁻¹ * (D.toX ⟨0, v.c / w.a, 0⟩ * D.toX w * (D.toX ⟨0, v.c / w.a, 0⟩)⁻¹) ∈
      N := mul_mem (inv_mem hn) (hNT _ (D.toX_mem _) _ hn)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ut_comm_E _ (mem_Eu.mp hw)] at h2
  convert h2 using 2
  ext : 1
  · exact hva
  · exact hvb
  · exact (mul_div_cancel₀ v.c hwa).symm

theorem exists_inv_mul_mem_F {x : X} (hx : x ∈ (D.T : Subgroup X)) :
    ∃ e ∈ D.E, e⁻¹ * x ∈ D.F := by
  obtain ⟨u, rfl⟩ := D.exists_toX hx
  refine ⟨D.toX ⟨u.a, 0, 0⟩, D.toX_mem_E_iff.mpr rfl, ?_⟩
  rw [← map_inv, ← map_mul, D.toX_mem_F_iff]
  change -u.a + u.a = 0
  ring

theorem F_mul_self {x : X} (hx : x ∈ D.F) : x * x = 1 :=
  D.swap.E_mul_self (by rw [swap_E]; exact hx)

end UTSylow

end ThmC

namespace E16

open ThmC

variable {X : Type} [Group X] [Finite X] (D : ThmC.UTSylow X)

omit [Finite X] in
theorem E_isMulCommutative : IsMulCommutative D.E :=
  ⟨⟨fun a b => Subtype.ext (D.E_comm a.2 b.2)⟩⟩

theorem T_inf_gL_le_E (hG : CFSG.Goldschmidt.TopStatement) (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E) :
    (D.T : Subgroup X) ⊓ gL D.E ≤ D.E := by
  obtain ⟨-, hE, -⟩ := gold_facts hG hO D.T D.E_le_T (E_isMulCommutative D) hcl
  set W := closure {t | t ∈ (D.T : Subgroup X) ⊓ gL D.E ∧ t ^ 2 = 1}
  have hPE : gP D.E ≤ D.E := le_sup_left.trans hE.ge
  have hWE : W ≤ D.E := le_sup_right.trans hE.ge
  have hWTL : W ≤ (D.T : Subgroup X) ⊓ gL D.E := (closure_le _).mpr fun t ht => ht.1
  intro x hx
  by_contra hxE
  obtain ⟨hxT, hxL⟩ := mem_inf.mp hx
  have hZTL : D.Z ≤ (D.T : Subgroup X) ⊓ gL D.E := fun z hz => by
    refine mem_inf.mpr ⟨D.Z_le_T hz, ?_⟩
    obtain ⟨e, -, rfl⟩ := D.exists_E_conj_eq hxT hxE hz
    have h1 : e⁻¹ * x * e⁻¹⁻¹ ∈ gL D.E := (gL_normal D.E).conj_mem x hxL e⁻¹
    rw [show e⁻¹ * (x * e * x⁻¹) = e⁻¹ * x * e⁻¹⁻¹ * x⁻¹ by group]
    exact mul_mem h1 (inv_mem hxL)
  have hPZ : gP D.E ≤ D.Z := fun p hp =>
    D.mem_Z_of_comm_of_not_mem (hPE hp) hxT hxE (gP_comm_gL D.E p hp x hxL)
  have hZW : D.Z ≤ W := fun z hz => subset_closure ⟨hZTL hz, by rw [sq]; exact D.Z_sq hz⟩
  have hEL : D.E ≤ (D.T : Subgroup X) ⊓ gL D.E :=
    hE.le.trans ((sup_le (hPZ.trans hZW) le_rfl).trans hWTL)
  obtain ⟨e, he, hf⟩ := D.exists_inv_mul_mem_F hxT
  have hfTL : e⁻¹ * x ∈ (D.T : Subgroup X) ⊓ gL D.E := mul_mem (inv_mem (hEL he)) hx
  have hfW : e⁻¹ * x ∈ W := subset_closure ⟨hfTL, by rw [sq]; exact D.F_mul_self hf⟩
  apply hxE
  rw [show x = e * (e⁻¹ * x) by group]
  exact mul_mem he (hWE hfW)

theorem normal_of_le_Z (hG : CFSG.Goldschmidt.TopStatement) (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E)
    (hZ : (D.T : Subgroup X) ⊓ gL D.E ≤ D.Z) : D.E.Normal := by
  obtain ⟨-, hE, -⟩ := gold_facts hG hO D.T D.E_le_T (E_isMulCommutative D) hcl
  set W := closure {t | t ∈ (D.T : Subgroup X) ⊓ gL D.E ∧ t ^ 2 = 1}
  have hPE : gP D.E ≤ D.E := le_sup_left.trans hE.ge
  have hWZ : W ≤ D.Z := ((closure_le _).mpr fun t ht => ht.1).trans hZ
  have hPT : ∀ t ∈ (D.T : Subgroup X), ∀ p ∈ gP D.E, t * p * t⁻¹ ∈ gP D.E :=
    fun t _ p hp => (gP_normal D.E).conj_mem p hp t
  rcases D.le_Z_or_Z_le hPE hPT with hPZ | hZP
  · exfalso
    have h := Subgroup.card_le_of_le (hE.le.trans (sup_le hPZ hWZ))
    rw [D.card_E, D.card_Z] at h
    omega
  · have hEP : D.E = gP D.E :=
      le_antisymm (hE.le.trans (sup_le le_rfl (hWZ.trans hZP))) hPE
    rw [hEP]
    exact gP_normal D.E

theorem normal_or_Z_le (hG : CFSG.Goldschmidt.TopStatement) (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E) :
    D.E.Normal ∨ D.Z ≤ (D.T : Subgroup X) ⊓ gL D.E := by
  have hNT : ∀ t ∈ (D.T : Subgroup X), ∀ s ∈ (D.T : Subgroup X) ⊓ gL D.E,
      t * s * t⁻¹ ∈ (D.T : Subgroup X) ⊓ gL D.E := fun t ht s hs =>
    mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hs).1) (inv_mem ht),
      (gL_normal D.E).conj_mem s (mem_inf.mp hs).2 t⟩
  rcases D.le_Z_or_Z_le (T_inf_gL_le_E D hG hO hcl) hNT with h | h
  · exact Or.inl (normal_of_le_Z D hG hO hcl h)
  · exact Or.inr h

end E16

end CFSG.ComponentClassification.GHarris
