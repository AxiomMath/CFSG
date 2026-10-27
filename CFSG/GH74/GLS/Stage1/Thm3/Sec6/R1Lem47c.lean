module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

namespace Cfg1K

theorem lemma47 (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer) :
    (∃ y, Is47b S P F y) ∧ ∀ y, Is47b S P F y →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers y) n) ∧
      IsNonabelianMaximalClassTwoGroup ↥(Q ⊔ zpowers y) ∧
      (∀ s ∈ S, s * s = 1 → s ∈ (P ⊔ Q) ⊔ zpowers y) ∧
      ∃ U : Subgroup G, U ≤ P ⊔ Q ∧ Four U ∧ (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) ∧
        ∀ v ∈ U, y * v = v * y := by
  classical
  have hq := h.exists_q hF
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hyS, hy2, hyPF⟩ := h.toCfg1.exists_outside hF
    exact ⟨y, h.toCfg1.is47b_of hyS hy2 hyPF⟩
  intro y₁ hy₁
  obtain ⟨hy₁S, hy₁2, hy₁PF, -⟩ := hy₁
  have hy₁' : Is47b S P F y₁ := h.toCfg1.is47b_of hy₁S hy₁2 hy₁PF
  have hQne : Q ≠ zpowers z := by
    obtain ⟨q, hqQ, hq1, hqz⟩ := hq
    intro e
    rw [e] at hqQ
    rcases (mem_zpowers_of_sq h.z_sq).1 hqQ with h1 | h1
    · exact hq1 h1
    · exact hqz h1
  obtain ⟨U, hUR, hU4, hUn⟩ := h.rn4 hQne
  have hUS : U ≤ S := hUR.trans (sup_le h.P_le h.Q_le)
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
  obtain ⟨E, hES, hEx, hE8, hEc⟩ := h.cent_rank U hUS hU4 hUn
  obtain ⟨y₀, hy₀E, hy₀PF⟩ : ∃ y₀ ∈ E, y₀ ∉ P ⊔ F := by
    by_contra hcon
    push Not at hcon
    have := h.card_PF_le hF (fun e he => hcon e he) hEx
    omega
  have hy₀S : y₀ ∈ S := hES hy₀E
  have hy₀2 : y₀ * y₀ = 1 := hEx y₀ hy₀E
  have hy₀ : Is47b S P F y₀ := h.toCfg1.is47b_of hy₀S hy₀2 hy₀PF
  obtain ⟨p, hp, q, hqQ, hy₁eq, hqy2⟩ := h.lemma_C hy₀ hy₁'
  have hy₂S : q * y₀ ∈ S := mul_mem (h.Q_le hqQ) hy₀S
  have hy₂PF : q * y₀ ∉ P ⊔ F := by
    intro hmem
    apply hy₀PF
    have : q⁻¹ * (q * y₀) ∈ P ⊔ F :=
      mul_mem (inv_mem (mem_sup_right (h.Q_le_F hqQ))) hmem
    simpa using this
  have hy₂ : Is47b S P F (q * y₀) := h.toCfg1.is47b_of hy₂S hqy2 hy₂PF
  have hy₂c : ∀ v ∈ U, (q * y₀) * v = v * (q * y₀) := by
    intro v hv
    have h1 : y₀ * v = v * y₀ := hEc y₀ hy₀E v hv
    have h2 : v * q = q * v := h.Q_comm_R hF hqQ (hUR hv)
    calc (q * y₀) * v = q * (y₀ * v) := by group
      _ = q * (v * y₀) := by rw [h1]
      _ = (q * v) * y₀ := by group
      _ = (v * q) * y₀ := by rw [h2]
      _ = v * (q * y₀) := by group
  have hc : (q * y₀) * (u₁ * u₂) = (u₁ * u₂) * (q * y₀) := by
    rw [← hu]; exact hy₂c u huU
  have hinv₂ : (q * y₀) * u₂ * (q * y₀)⁻¹ = u₂⁻¹ :=
    h.inverts_u₂ hy₂ hu₁P hu₂Q hu₁sq hu₂sq hc
  have hpu : p * u₂ = u₂ * p := h.PQ_comm p hp u₂ hu₂Q
  have hpu' : p⁻¹ * u₂ * p = u₂ := by
    calc p⁻¹ * u₂ * p = p⁻¹ * (u₂ * p) := by group
      _ = p⁻¹ * (p * u₂) := by rw [hpu]
      _ = u₂ := by group
  have hinv₁ : y₁ * u₂ * y₁⁻¹ = u₂⁻¹ := by
    rw [hy₁eq]
    calc p⁻¹ * (q * y₀) * p * u₂ * (p⁻¹ * (q * y₀) * p)⁻¹
        = p⁻¹ * ((q * y₀) * (p * u₂ * p⁻¹) * (q * y₀)⁻¹) * p := by group
      _ = p⁻¹ * ((q * y₀) * u₂ * (q * y₀)⁻¹) * p := by
          rw [show p * u₂ * p⁻¹ = u₂ by rw [hpu]; group]
      _ = p⁻¹ * u₂⁻¹ * p := by rw [hinv₂]
      _ = (p⁻¹ * u₂ * p)⁻¹ := by group
      _ = u₂⁻¹ := by rw [hpu']
  refine ⟨h.sd y₁ hy₁S hy₁2 (h.toCfg1.not_R_of_not_PF hy₁PF)
      (h.toCfg1.not_FA_of_not_PF hy₁S hy₁2 hy₁PF),
    h.toCfg1.maxClass_Qy hF h1024 hy₁' hu₂Q hu₂sq hinv₁, ?_, U, hUR, hU4, hUn, ?_⟩
  · intro s hsS hs2
    by_cases hsPF : s ∈ P ⊔ F
    · exact mem_sup_left (h.invol_PF_in_R hF hq hsPF hs2)
    · have hd := h.diag' hsS hy₁S hs2 hy₁2 hsPF hy₁PF
      have e : s = s * y₁⁻¹ * y₁ := by group
      rw [e]
      exact mul_mem (mem_sup_left hd) (mem_sup_right (mem_zpowers y₁))
  · intro v hv
    have hv' : p * v * p⁻¹ ∈ U := hUn p (h.P_le hp) v hv
    have hcv : (q * y₀) * (p * v * p⁻¹) = (p * v * p⁻¹) * (q * y₀) := hy₂c _ hv'
    rw [hy₁eq]
    calc p⁻¹ * (q * y₀) * p * v = p⁻¹ * ((q * y₀) * (p * v * p⁻¹)) * p := by group
      _ = p⁻¹ * ((p * v * p⁻¹) * (q * y₀)) * p := by rw [hcv]
      _ = v * (p⁻¹ * (q * y₀) * p) := by group

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
