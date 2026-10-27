module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NStmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctxWN_le_ctxCQ (t tau x₁ x₂ rho : G) :
    ctxWN t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho :=
  inf_le_left

theorem ctxCQ_comm {c q : G} (hc : c ∈ ctxCQ t tau x₁ x₂ rho) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    c * q = q * c :=
  (mem_centralizer_iff.mp hc q hq).symm

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem nPre : Z4Pre t L S x₁ x₂ lam rho tau := ⟨hz.toCtx4Q, hz.q_iso⟩

theorem nGood : Z4Good t L S x₁ x₂ lam rho tau := ⟨hz.nPre, hz.tau_cent_Y⟩

private theorem t_not_mem_ctxCQ_aux : t ∉ ctxCQ t tau x₁ x₂ rho := by
  intro ht
  have hsub : ctxQ t tau x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
    rw [← hz.CQ_t]
    refine le_inf le_rfl ?_
    intro q hq
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht q hq)
  have hcard := Subgroup.card_le_of_le hsub
  rw [hz.card_Q, hz.nGood.card_B] at hcard
  norm_num at hcard

theorem mem_ctxWN_iff {w : G} :
    w ∈ ctxWN t tau x₁ x₂ rho ↔
      w ∈ ctxCQ t tau x₁ x₂ rho ∧ w * t * w⁻¹ * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hnormC : ∀ c ∈ zpowers t, ∀ a ∈ ctxQ t tau x₁ x₂ rho, c * a * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun c hc a ha => hz.normal_Q.2 c ((Subgroup.zpowers_le.mpr hz.t_mem_M) hc) a ha
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    have hwt : w * t * w⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers t :=
      (Subgroup.mem_set_normalizer_iff.mp hw.2 t).mp
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    obtain ⟨a, ha, c, hc, hac⟩ :=
      mem_sup_of_normalizes (A := ctxQ t tau x₁ x₂ rho) (C := zpowers t) hnormC hwt
    rcases z4_mem_zpowers_of_mul_self hz.t_mul_self hc with hc1 | hct
    · exfalso
      have htQ : w * t * w⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by rw [hac, hc1, mul_one]; exact ha
      exact (hz.tG_Qtau w (w * t * w⁻¹) (Subgroup.mem_sup_left htQ)) rfl
    · rw [hac, hct, mul_assoc, mul_inv_cancel, mul_one]
      exact ha
  · rintro ⟨hwC, hwt⟩
    refine ⟨hwC, ?_⟩
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨a, ha, c, hc, hac⟩ :=
      mem_sup_of_normalizes (A := ctxQ t tau x₁ x₂ rho) (C := zpowers t) hnormC hn
    have hwa : w * a * w⁻¹ = a := by
      have hcomm := mem_centralizer_iff.mp hwC a ha
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hwt' : w * t * w⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers t := by
      rw [show w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t from by group]
      exact mul_mem (Subgroup.mem_sup_left hwt) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hwc : w * c * w⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers t := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← conj_zpow]
      exact zpow_mem hwt' k
    rw [hac, show w * (a * c) * w⁻¹ = (w * a * w⁻¹) * (w * c * w⁻¹) from by group,
      hwa]
    exact mul_mem (Subgroup.mem_sup_left ha) hwc

theorem Q_le_ctxWN : ctxQ t tau x₁ x₂ rho ≤ ctxWN t tau x₁ x₂ rho := by
  intro q hq
  rw [hz.mem_ctxWN_iff]
  refine ⟨mem_centralizer_iff.mpr fun a ha => (hz.Q_comm q hq a ha).symm, ?_⟩
  have htq : t * q⁻¹ * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hz.normal_Q.2 t hz.t_mem_M q⁻¹ (inv_mem hq)
  rw [show q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) from by group]
  exact mul_mem hq htq

theorem base_le_ctxWN : baseGrp x₁ x₂ ≤ ctxWN t tau x₁ x₂ rho :=
  hz.base_le_Q.trans hz.Q_le_ctxWN

theorem Y_le_ctxWN : ctxYq t tau x₁ x₂ rho ≤ ctxWN t tau x₁ x₂ rho :=
  (hz.Y_le_Q).trans hz.Q_le_ctxWN

theorem conj_mem_ctxWN {g w : G} (hg : g ∈ ctxM t tau x₁ x₂) (hgt : g * t = t * g)
    (hw : w ∈ ctxWN t tau x₁ x₂ rho) : g * w * g⁻¹ ∈ ctxWN t tau x₁ x₂ rho := by
  obtain ⟨hwC, hwt⟩ := hz.mem_ctxWN_iff.mp hw
  rw [hz.mem_ctxWN_iff]
  constructor
  · refine mem_centralizer_iff.mpr fun q hq => ?_
    have hgq : g⁻¹ * q * g ∈ ctxQ t tau x₁ x₂ rho := by
      simpa using hz.normal_Q.2 g⁻¹ (inv_mem hg) q hq
    have hcomm : (g⁻¹ * q * g) * w = w * (g⁻¹ * q * g) := mem_centralizer_iff.mp hwC _ hgq
    calc q * (g * w * g⁻¹) = g * ((g⁻¹ * q * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * w * g⁻¹) * q := by group
  · have hgt' : g * t * g⁻¹ = t := by rw [hgt, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : (g * w * g⁻¹) * t * (g * w * g⁻¹)⁻¹ * t⁻¹
        = g * (w * t * w⁻¹ * t⁻¹) * g⁻¹ := by
      have hmap : MulAut.conj g (w * t * w⁻¹ * t⁻¹)
          = (g * w * g⁻¹) * t * (g * w * g⁻¹)⁻¹ * t⁻¹ := by
        simp only [map_mul, map_inv, MulAut.conj_apply, hgt']
      rw [← hmap, MulAut.conj_apply]
    rw [hconj]
    exact hz.normal_Q.2 g hg (w * t * w⁻¹ * t⁻¹) hwt

theorem t_conj_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    t * w * t⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
  hz.conj_mem_ctxWN hz.t_mem_M rfl hw

theorem tau_conj_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    tau * w * tau⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
  hz.conj_mem_ctxWN hz.tau_mem_M hz.t_comm_tau.symm hw

theorem lam_conj_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    lam * w * lam⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
  hz.conj_mem_ctxWN hz.lam_mem_M hz.t_lam_comm.symm hw

theorem rho_conj_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    rho * w * rho⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
  hz.conj_mem_ctxWN hz.rho_mem_M hz.rho_comm_t hw

theorem sigma_conj_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    (lam * t) * w * (lam * t)⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
  hz.conj_mem_ctxWN hz.sigma_mem_M hz.sigma_comm_t hw

theorem ctxWN_inf_centralizer_t :
    ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ := by
  apply le_antisymm
  · rintro w ⟨hwW, hwt⟩
    have hwinv : w ∈ invCent t := S4A.mem_invCent_iff.mpr (mem_centralizer_singleton_iff.mp hwt)
    have hcentB : w ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hwW.1 b (hz.base_le_Q hb)
    have hwW' : w ∈ ctxW t x₁ x₂ := by
      rw [← hz.cent_baseGrp]
      exact ⟨hwinv, hcentB⟩
    rw [ctxW, hz.l43] at hwW'
    have hnormB : ∀ c ∈ baseGrp x₁ x₂, ∀ a ∈ zpowers t, c * a * c⁻¹ ∈ zpowers t := by
      intro c hc a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hct : c * t * c⁻¹ = t := by
        rw [hz.nGood.B_comm_t c hc, mul_assoc, mul_inv_cancel, mul_one]
      rw [← conj_zpow, hct]
      exact zpow_mem (Subgroup.mem_zpowers t) k
    obtain ⟨a, ha, c, hc, hwac⟩ :=
      mem_sup_of_normalizes (A := zpowers t) (C := baseGrp x₁ x₂) hnormB hwW'
    rcases z4_mem_zpowers_of_mul_self hz.t_mul_self ha with ha1 | hat
    · rw [hwac, ha1, one_mul]; exact hc
    · exfalso
      apply t_not_mem_ctxCQ_aux hz
      have hcC : c⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := by
        refine inv_mem ?_
        exact mem_centralizer_iff.mpr fun q hq => (hz.Q_comm c (hz.base_le_Q hc) q hq).symm
      have hmem : w * c⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := mul_mem hwW.1 hcC
      have ht_eq : t = w * c⁻¹ := by rw [hwac, hat]; group
      refine mem_centralizer_iff.mpr fun q hq => ?_
      have hqc := mem_centralizer_iff.mp hmem q hq
      rw [← ht_eq] at hqc
      exact hqc
  · intro b hb
    exact ⟨hz.base_le_ctxWN hb, mem_centralizer_singleton_iff.mpr (hz.nGood.B_comm_t b hb)⟩

theorem t_not_mem_ctxCQ : t ∉ ctxCQ t tau x₁ x₂ rho := t_not_mem_ctxCQ_aux hz

theorem tau_not_mem_ctxCQ : tau ∉ ctxCQ t tau x₁ x₂ rho := by
  intro ht
  have hsqu : x₁ * x₁ = 1 := by
    have hcomm : x₁ * tau = tau * x₁ := mem_centralizer_iff.mp ht x₁ hz.x₁_mem_Q
    have h1 : tau * x₁ * tau⁻¹ = x₁ := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : tau * x₁ * tau⁻¹ = x₁⁻¹ := hz.tau_inv_Q x₁ hz.x₁_mem_Q
    rw [h1] at h2
    nth_rewrite 1 [h2]
    exact inv_mul_cancel x₁
  exact hz.y_ne_one (by rw [pow_two]; exact hsqu)

theorem ttau_not_mem_ctxCQ : t * tau ∉ ctxCQ t tau x₁ x₂ rho := by
  intro ht
  have hcomm : x₁ * (t * tau) = (t * tau) * x₁ := mem_centralizer_iff.mp ht x₁ hz.x₁_mem_Q
  have hconj1 : (t * tau) * x₁ * (t * tau)⁻¹ = x₁ := by rw [← hcomm]; group
  have hx1B : x₁⁻¹ ∈ baseGrp x₁ x₂ := inv_mem (subset_closure (by simp))
  have hconj2 : (t * tau) * x₁ * (t * tau)⁻¹ = x₁⁻¹ := by
    rw [show (t * tau) * x₁ * (t * tau)⁻¹ = t * (tau * x₁ * tau⁻¹) * t⁻¹ from by group,
      hz.tau_x₁, hz.nGood.t_conj_B hx1B]
  have hx : x₁ * x₁ = 1 := by
    rw [hconj1] at hconj2
    nth_rewrite 1 [hconj2]
    exact inv_mul_cancel x₁
  exact hz.y_ne_one (by rw [pow_two]; exact hx)

theorem sigma_not_mem_ctxCQ : lam * t ∉ ctxCQ t tau x₁ x₂ rho := by
  intro ht
  have hq : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho := pow_mem hz.x₁_mem_Q 2
  have hcomm : (x₁ ^ 2) * (lam * t) = (lam * t) * (x₁ ^ 2) := mem_centralizer_iff.mp ht (x₁ ^ 2) hq
  have hconj : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by rw [← hcomm]; group
  exact hz.y_ne_x₂_sq (by rw [← hconj, hz.sigma_y])

theorem P0_inf_ctxCQ : ∀ g ∈ closure ({t, tau} : Set G), g ∈ ctxCQ t tau x₁ x₂ rho → g = 1 := by
  intro g hg hgC
  rcases (S4B.mem_closure_pair_of_invol hz.t_mul_self hz.tau_mul_self hz.t_comm_tau).mp hg
    with h1 | h1 | h1 | h1
  · exact h1
  · exact absurd hgC (by rw [h1]; exact hz.t_not_mem_ctxCQ)
  · exact absurd hgC (by rw [h1]; exact hz.tau_not_mem_ctxCQ)
  · exact absurd hgC (by rw [h1]; exact hz.ttau_not_mem_ctxCQ)

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
