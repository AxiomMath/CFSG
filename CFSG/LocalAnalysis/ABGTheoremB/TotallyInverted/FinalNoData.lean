module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalBasic

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools Sec11

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem no_data (hσ : σ.IsValid) (Δ : Data σ r) (h92 : NotPGroupP σ r)
    (h101 : Transitivity σ r) (h111 : PGroupR Δ) : False := by
  set X : Subgroup G := R Δ 0 ⊔ R Δ 2 with hX
  have hCX : σ.C ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_sup (C_le_normalizer_R Δ 0) (C_le_normalizer_R Δ 2)
  have hXmem : X ∈ signalizersPerm ⊤ σ.T σ.C r :=
    ⟨⟨le_top, h111, (σ.T_le_C hσ).trans hCX, inf_T_eq_bot hσ Δ.prime Δ.ne_two h111⟩,
      mul_comm_of_le_normalizer hCX⟩
  obtain ⟨U, hU, hXU⟩ := exists_le_mem_maximals hXmem
  set V : Subgroup G := conjSub Δ.a U with hV
  have hVmax : V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r) :=
    conjSub_mem_maximals_signalizersPerm (a_mem_normalizer_T Δ) (a_mem_normalizer_C Δ) hU
  have hR0U : R Δ 0 ≤ U := le_sup_left.trans hXU
  have hR0V : R Δ 0 ≤ V := by
    have h : conjSub Δ.a (R Δ 2) = R Δ 0 := conjSub_R Δ 2
    rw [← h]
    exact conjSub_mono (le_sup_right.trans hXU)
  have hP0U : σ.Ps r 0 ≤ U := le_sup_right.trans hR0U
  have hP2U : σ.Ps r 2 ≤ U := le_sup_right.trans (le_sup_right.trans hXU)
  have hP0V : σ.Ps r 0 ≤ V := le_sup_right.trans hR0V
  have hP1V : σ.Ps r 1 ≤ V := by
    have h : conjSub Δ.a (σ.Ps r 0) = σ.Ps r 1 := Δ.P_conj 0
    rw [← h]
    exact conjSub_mono hP0U
  have key : ∀ W : Subgroup G, IsPGroup r W → σ.Ps r 0 ≤ W → σ.Ps r 1 ≤ W → σ.Ps r 2 ≤ W →
      False :=
    fun W hW h0 h1 h2 => h92 (hW.to_le (sup_le (sup_le h0 h1) h2))
  rcases h101 _ (R_mem_maximals Δ 0) U hU V hVmax hR0U hR0V with ⟨c, hc, hcUV⟩ | h | h
  · have hP1U : σ.Ps r 1 ≤ U := by
      have h' := conjSub_mono (g := c⁻¹) hP1V
      rwa [← hcUV, conjSub_inv_conjSub,
        conjSub_eq_self_iff.mpr (C_le_normalizer_Ps r 1 (inv_mem hc))] at h'
    exact key U hU.1.1.2.1 hP0U hP1U hP2U
  · exact key U hU.1.1.2.1 hP0U (h.trans inf_le_left) hP2U
  · exact key V hVmax.1.1.2.1 hP0V hP1V (h.trans inf_le_right)

end CFSG.ABGTheoremB.TotallyInverted
