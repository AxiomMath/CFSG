module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem48b
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

namespace Cfg1K

theorem sdf_of_Y (h : Cfg1K G z S P Q F FA) {y : G} (hy : Is47b S P F y) :
    (∀ p ∈ P, y * p = p * y → p = 1 ∨ p = z) ∧
    (∀ v ∈ P, (v * y) * (v * y) = 1 → ∃ p ∈ P, p⁻¹ * y * p = v * y) ∧
    (∀ v ∈ P, (v * y) * (v * y) ≠ z) := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  have hyP : y ∉ P := fun hm => hyPF (mem_sup_left hm)
  have hSD := h.sd y hyS hy2 (h.toCfg1.not_R_of_not_PF hyPF)
    (h.toCfg1.not_FA_of_not_PF hyS hy2 hyPF)
  exact h.sdf y hy2 hyP (fun p hp => h.P_norm y hyS p hp) hSD

theorem conj_in_Py (h : Cfg1K G z S P Q F FA) {y w : G} (hy : Is47b S P F y) (hw2 : w * w = 1)
    (hwy : w * y⁻¹ ∈ P) : ∃ p ∈ P, p⁻¹ * y * p = w := by
  obtain ⟨-, hs2, -⟩ := h.sdf_of_Y hy
  have e : (w * y⁻¹) * y = w := by group
  have := hs2 (w * y⁻¹) hwy (by rw [e]; exact hw2)
  rw [e] at this
  exact this

theorem cfg_for_y (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer) {y : G} (hy : Is47b S P F y) :
    ∃ U : Subgroup G, U ≤ P ⊔ Q ∧ Four U ∧ (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) ∧
      (∀ v ∈ U, y * v = v * y) ∧ ∃ u ∈ U, u ≠ 1 ∧ u ≠ z ∧ ∃ u₁ ∈ P, ∃ u₂ ∈ Q,
        u = u₁ * u₂ ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z ∧ y * u₂ * y⁻¹ = u₂⁻¹ ∧ y * u₁ * y⁻¹ = u₁⁻¹ := by
  classical
  obtain ⟨U, hUR, hU4, hUn, hUy⟩ := ((h.lemma47 hF h1024).2 y hy).2.2.2
  refine ⟨U, hUR, hU4, hUn, hUy, ?_⟩
  obtain ⟨u, huU, hu1, huz⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ e ∈ U, e ∈ ({1, z} : Finset G) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases he1 : e = 1
      · exact Or.inl he1
      · exact Or.inr (hcon e he he1)
    have h1 := B.card_subgroup_le_finset U _ hsub
    have h2 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
    have h3 := hU4.2
    omega
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    h.decomp_four hF (hUR huU) (hU4.1 u huU) hu1 huz
  have hc : y * (u₁ * u₂) = (u₁ * u₂) * y := by rw [← hu]; exact hUy u huU
  have hinv₂ : y * u₂ * y⁻¹ = u₂⁻¹ := h.inverts_u₂ hy hu₁P hu₂Q hu₁sq hu₂sq hc
  have hinv₁ : y * u₁ * y⁻¹ = u₁⁻¹ := by
    have e1 : y * u₁ * y⁻¹ = (y * (u₁ * u₂) * y⁻¹) * (y * u₂ * y⁻¹)⁻¹ := by group
    have e2 : y * (u₁ * u₂) * y⁻¹ = u₁ * u₂ := by rw [hc]; group
    rw [e1, e2, hinv₂, inv_inv, h.toCfg1.inv_eq_mul_z hu₁sq]
    calc u₁ * u₂ * u₂ = u₁ * (u₂ * u₂) := by group
      _ = u₁ * z := by rw [hu₂sq]
  exact ⟨u, huU, hu1, huz, u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq, hinv₂, hinv₁⟩

theorem u_not_zG (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer)
    (h119 : ∀ s ∈ P ⊔ F, s ∉ P ⊔ Q → ∀ V : Subgroup G, V ≤ P → IsCyclic ↥V →
      V.relIndex P = 2 → ∃ v ∈ V, s * v ≠ v * s)
    (hT : HThompson G z S) :
    ∃ u ∈ P ⊔ Q, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ ¬ IsConj z u := by
  obtain ⟨y, hy⟩ := ((h.lemma47 hF h1024).1)
  obtain ⟨U, hUR, hU4, hUn, hUy, u, huU, hu1, huz, -⟩ := h.cfg_for_y hF h1024 hy
  exact ⟨u, hUR huU, hU4.1 u huU, hu1, huz, h.lemma48 hF h119 hT hy hUR hU4 hUn hUy huU hu1 huz⟩

theorem R_not_zG (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer)
    (h119 : ∀ s ∈ P ⊔ F, s ∉ P ⊔ Q → ∀ V : Subgroup G, V ≤ P → IsCyclic ↥V →
      V.relIndex P = 2 → ∃ v ∈ V, s * v ≠ v * s)
    (hT : HThompson G z S)
    (hCR : ∀ w ∈ P ⊔ Q, ∀ w' ∈ P ⊔ Q, w * w = 1 → w' * w' = 1 → w ≠ 1 → w ≠ z → w' ≠ 1 → w' ≠ z →
      IsConj w w') :
    ∀ w ∈ P ⊔ Q, w * w = 1 → w ≠ 1 → w ≠ z → ¬ IsConj z w := by
  intro w hw hw2 hw1 hwz hconj
  obtain ⟨u, hu, hu2, hu1, huz, hnu⟩ := h.u_not_zG hF h1024 h119 hT
  exact hnu (hconj.trans (hCR w hw u hu hw2 hu2 hw1 hwz hu1 huz))

theorem Y_of_conj (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (hR : ∀ w ∈ P ⊔ Q, w * w = 1 → w ≠ 1 → w ≠ z → ¬ IsConj z w)
    {t : G} (htS : t ∈ S) (hzt : IsConj z t) (htz : t ≠ z) : Is47b S P F t := by
  have ht2 : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hzt
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have ht1 : t ≠ 1 := by
    intro e
    obtain ⟨c, hc⟩ := isConj_iff.1 hzt
    apply h.z_ne
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [hc, e]; group
  have htPF : t ∉ P ⊔ F := by
    intro hmem
    exact hR t (h.toCfg1.invol_PF_in_R hF (h.exists_q hF) hmem ht2) ht2 ht1 htz hzt
  exact h.toCfg1.is47b_of htS ht2 htPF

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
