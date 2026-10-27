module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalSwap
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalCore4

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace Sec11

omit [Finite G] in
theorem conjSub_mem_maximals_signalizersPerm_of {H X Y U : Subgroup G} {p : ℕ} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G))
    (hH : conjSub g H = H) (hU : U ∈ maximals (signalizersPerm H X Y p)) :
    conjSub g U ∈ maximals (signalizersPerm H X Y p) := by
  have hH' : conjSub g⁻¹ H = H := by rw [← hH, conjSub_inv_conjSub, hH]
  refine conjSub_mem_maximals (fun V hV => ?_) (fun V hV => ?_) hU
  · simpa [hH] using conjSub_mem_signalizersPerm hX hY hV
  · simpa [hH'] using conjSub_mem_signalizersPerm (Subgroup.inv_mem _ hX)
      (Subgroup.inv_mem _ hY) hV

theorem pGroupR_of_comp_one (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (hI : Inputs Δ) (h91 : ConjugateMaximalTC σ r) {V : Subgroup G}
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) (hRV : R Δ 0 ≤ V)
    (hX : ∃ u ∈ comp σ V 1, u ≠ 1 ∧ u ∈ Subgroup.centralizer (R Δ 0 : Set G)) :
    PGroupR Δ := by
  rcases lemma11_4 hσ hF Δ homni hI hV hX with h | ⟨hδ, hq, hXe, hRRs⟩
  · exact h
  · exact core hσ hF Δ homni hI h91 ⟨hδ, hq⟩ hV hRV hXe hRRs

end Sec11

open Sec11

theorem pGroupR (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r) (homni : Omnibus Δ)
    (h91 : ConjugateMaximalTC σ r) (hI : Inputs Δ) : PGroupR Δ := by
  have hR0 : R Δ 0 ∈ signalizersPerm (Kp σ r) σ.T σ.C r :=
    ⟨⟨(R_le_Ns Δ hσ 0).trans N_le_Kp, isPGroup_R Δ hσ 0,
      (σ.T_le_C hσ).trans (C_le_normalizer_R Δ 0),
      inf_T_eq_bot hσ Δ.prime Δ.ne_two (isPGroup_R Δ hσ 0)⟩,
      mul_comm_of_le_normalizer (C_le_normalizer_R Δ 0)⟩
  obtain ⟨V, hV, hRV⟩ := exists_le_mem_maximals hR0
  rcases lemma11_3_iv hσ Δ homni hV hRV with hX | ⟨u, hu, hu1, huc⟩
  · exact pGroupR_of_comp_one hσ hF Δ homni hI h91 hV hRV hX
  · by_cases hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q
    ·
      obtain ⟨z, hz⟩ := exists_isSwap Δ hδq
      set Δ' := Data.swapQ hσ Δ
      have hzK : conjSub z (Kp σ r) = Kp σ r := by
        rw [Kp, ← normalizer_conjSub, hz.conj_Ps_zero hσ]
      have hV' : conjSub z V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r) :=
        conjSub_mem_maximals_signalizersPerm_of hz.mem_normalizer_T hz.mem_M hzK hV
      have hRV' : R Δ' 0 ≤ conjSub z V := by
        rw [R_swapQ, ← hz.conj_R_zero hσ]
        exact conjSub_mono hRV
      have hX' : ∃ u ∈ comp σ (conjSub z V) 1, u ≠ 1 ∧
          u ∈ Subgroup.centralizer (R Δ' 0 : Set G) := by
        refine ⟨z * u * z⁻¹, ⟨conj_mem_conjSub hu.1, ?_, ?_⟩, ?_, ?_⟩
        · have hx₃ := hz.conj_x₃ hδq hσ
          have hc : σ.xs 2 * u = u * σ.xs 2 := hu.2.1
          change σ.x₂ * (z * u * z⁻¹) = z * u * z⁻¹ * σ.x₂
          rw [← hx₃]
          calc z * σ.xs 2 * z⁻¹ * (z * u * z⁻¹) = z * (σ.xs 2 * u) * z⁻¹ := by group
            _ = z * (u * σ.xs 2) * z⁻¹ := by rw [hc]
            _ = z * u * z⁻¹ * (z * σ.xs 2 * z⁻¹) := by group
        · have hx₂ := hz.conj_x₂ hδq hσ
          have hinv : σ.xs (2 + 2) * u * (σ.xs (2 + 2))⁻¹ = u⁻¹ :=
            conj_xs_add_two_of_mem_comp hσ hu
          change σ.xs 2 * (z * u * z⁻¹) * (σ.xs 2)⁻¹ = (z * u * z⁻¹)⁻¹
          rw [← hx₂]
          have hinv' : σ.x₂ * u * σ.x₂⁻¹ = u⁻¹ := hinv
          calc z * σ.x₂ * z⁻¹ * (z * u * z⁻¹) * (z * σ.x₂ * z⁻¹)⁻¹ =
                z * (σ.x₂ * u * σ.x₂⁻¹) * z⁻¹ := by group
            _ = (z * u * z⁻¹)⁻¹ := by rw [hinv']; group
        · intro h1
          apply hu1
          have : u = z⁻¹ * (z * u * z⁻¹) * z := by group
          rw [this, h1]
          group
        · have hc := conj_mem_conjSub (g := z) huc
          rwa [conjSub_centralizer, hz.conj_R_zero hσ, ← R_swapQ hσ Δ] at hc
      have h' := pGroupR_of_comp_one hσ hF Δ' (omnibus_swapQ hσ Δ homni) (inputs_swapQ hσ Δ hI)
        h91 hV' hRV' hX'
      exact pGroupR_of_Rs02 hσ Δ h'
    ·
      obtain ⟨W, hW, -, hWcases⟩ := (omnibusAt_V Δ homni hV).part_i_b 2
      have hR : R Δ 2 = σ.Ps r 2 := by rw [R, (Δ.Q_trivial hδq 2).1, bot_sup_eq]
      have hRs : Rs Δ 2 = σ.Ps r 2 := by rw [Rs, (Δ.Q_trivial hδq 2).2, bot_sup_eq]
      have hWP : W ≤ σ.Ps r 2 := by
        rcases hWcases with h | h | h
        · exact h
        · exact hR ▸ h
        · exact hRs ▸ h
      have huW : u ∈ W := by rw [← SetLike.mem_coe, hW]; exact hu
      apply pGroupR_of_centralizer_Ps2_R0 hσ hF Δ homni
      intro hb
      have : u ∈ σ.Ps r 2 ⊓ Subgroup.centralizer (R Δ 0 : Set G) := ⟨hWP huW, huc⟩
      rw [hb] at this
      exact hu1 this

end CFSG.ABGTheoremB.TotallyInverted
