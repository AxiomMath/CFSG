module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem false_of_hyperplane_F4 (h : Hyp147 G T L V) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {H₀ : Subgroup G}
    (hH₀V : H₀ ≤ V) (hne : ¬ V ≤ H₀)
    (hidx : ∀ a ∈ V, a ∉ H₀ → ∀ b ∈ V, b ∉ H₀ → a * b ∈ H₀)
    (hN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (H₀ : Set G)) : False := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, hV2⟩ := h.exists_V2_F4 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  by_cases hV1 : fsuV1 T V ≤ H₀
  · rcases hF.irred H₀ hV1 hH₀V hN with e | e
    · have haH : a ∉ H₀ := e ▸ haV
      have hbH : b ∉ H₀ := e ▸ fun hb' => hbV (hV2.1 hb')
      have hab := hidx a (hV2.2.1 ha) haH b hb hbH
      rw [e] at hab
      apply hbV
      rw [show b = a⁻¹ * (a * b) by group]
      exact mul_mem (inv_mem ha) (hV2.1 hab)
    · exact hne e.ge
  · have hzH : z ∉ H₀ := fun hz' => hV1 fun v hv => by
      rcases S14.eq_of_mem_V1_F4 hz0 hz1 hv with rfl | rfl
      · exact one_mem _
      · exact hz'
    have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans hF.L₁T_le_H
    have hcomm : ⁅V, pCoreOf 2 (L₁Of L (fsuV1 T V))⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv p hp
      have hpL : p ∈ L₁Of L (fsuV1 T V) := pCoreOf_le 2 _ hp
      have hpH : p ∈ hz T V := hL1H hpL
      have hpN : p ∈ Subgroup.normalizer (H₀ : Set G) := hN (Subgroup.mem_sup_left hpL)

      have key : ∀ w ∈ V, w ∈ H₀ → w * p * w⁻¹ * p⁻¹ = 1 := by
        intro w hw hwH
        have h1 : ⁅w, p⁆ ∈ fsuV1 T V := by
          rw [← S14.comm3_F4]
          exact Subgroup.commutator_mem_commutator hw hp
        have h2 : w * p * w⁻¹ * p⁻¹ ∈ H₀ := by
          rw [show w * p * w⁻¹ * p⁻¹ = w * (p * w⁻¹ * p⁻¹) by group]
          exact mul_mem hwH ((Subgroup.mem_normalizer_iff.mp hpN _).mp (inv_mem hwH))
        rw [commutatorElement_def] at h1
        rcases S14.eq_of_mem_V1_F4 hz0 hz1 h1 with e | e
        · exact e
        · exact absurd (e ▸ h2) hzH
      have hzp : z * p = p * z :=
        (Subgroup.mem_centralizer_iff.mp hpH z hz0)
      rw [commutatorElement_def, Subgroup.mem_bot]
      by_cases hvH : v ∈ H₀
      · exact key v hv hvH
      · have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
        have hzv := hidx z hzV hzH v hv hvH
        have h1 := key (z * v) (mul_mem hzV hv) hzv
        have e : z * v * p * (z * v)⁻¹ * p⁻¹ = z * (v * p * v⁻¹ * p⁻¹) * z⁻¹ := by
          calc z * v * p * (z * v)⁻¹ * p⁻¹ = z * v * p * v⁻¹ * (p * z)⁻¹ := by group
            _ = z * v * p * v⁻¹ * (z * p)⁻¹ := by rw [hzp]
            _ = z * (v * p * v⁻¹ * p⁻¹) * z⁻¹ := by group
        rw [e] at h1
        calc v * p * v⁻¹ * p⁻¹ = z⁻¹ * (z * (v * p * v⁻¹ * p⁻¹) * z⁻¹) * z := by group
          _ = 1 := by rw [h1]; group
    have := S14.comm3_F4
    rw [hcomm] at this
    have hc := hF.card_V₁
    rw [← this, Subgroup.card_bot] at hc
    omega

end CFSG.Quasithin.H13.L32A
