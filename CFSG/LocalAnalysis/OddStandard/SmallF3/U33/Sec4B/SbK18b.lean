module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Fpf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Y
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem k18_K_normalizes_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ ctxK t tau x₁ x₂ rho, ∀ v ∈ fourGrp x₁ x₂, k * v * k⁻¹ ∈ fourGrp x₁ x₂ := by
  have hsq : ∀ v ∈ fourGrp x₁ x₂, ∃ q ∈ ctxQ t tau x₁ x₂ rho, v = q * q := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem g hg =>
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact ⟨x₁, hc.base_le_Q (Subgroup.subset_closure (by simp)), by rw [pow_two]⟩
        · exact ⟨x₁ * x₂, hc.base_le_Q (Subgroup.mul_mem _
              (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))),
            by rw [pow_two]⟩
    | one => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | mul a b _ _ iha ihb =>
        obtain ⟨q, hq, rfl⟩ := iha
        obtain ⟨p, hp, rfl⟩ := ihb
        refine ⟨q * p, Subgroup.mul_mem _ hq hp, ?_⟩
        have hcomm : q * p = p * q := IsZ4Z4E4.comm hc.q_iso hq hp
        calc (q * q) * (p * p) = q * (q * p) * p := by group
          _ = q * (p * q) * p := by rw [hcomm]
          _ = (q * p) * (q * p) := by group
    | inv a _ iha =>
        obtain ⟨q, hq, rfl⟩ := iha
        exact ⟨q⁻¹, Subgroup.inv_mem _ hq, by group⟩
  intro k hk v hv
  obtain ⟨q, hq, rfl⟩ := hsq v hv
  have hkq : k * q * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q_K.2 k hk q hq
  have heq : k * (q * q) * k⁻¹ = (k * q * k⁻¹) ^ 2 := by
    rw [pow_two]
    group
  rw [heq]
  exact l17_Q_sq_mem hc _ hkq

theorem k18_OK_cent_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxOK t tau x₁ x₂ rho, ∀ v ∈ fourGrp x₁ x₂, n * v * n⁻¹ = v := by
  have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hOKK : ctxOK t tau x₁ x₂ rho ≤ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1
  have hOKnorm : ∀ g ∈ ctxK t tau x₁ x₂ rho, ∀ k ∈ ctxOK t tau x₁ x₂ rho,
      g * k * g⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
  have hOKp : IsPGroup 2 (ctxOK t tau x₁ x₂ rho) := l18_OK_pgroup
  have hVOK : fourGrp x₁ x₂ ≤ ctxOK t tau x₁ x₂ rho :=
    (l17_V_le_Y hc).trans (ctxYq_le_ctxQ.trans (le_sup_left.trans (l18_R_le_OK hc)))
  have hmain : ∀ n ∈ ctxOK t tau x₁ x₂ rho, ∀ w ∈ fourGrp x₁ x₂,
      n * w * n⁻¹ * w⁻¹ ∈ (⊥ : Subgroup G) :=
    comm_mem_of_fpf_section (P := ctxOK t tau x₁ x₂ rho) (U := ⊥)
      (W := fourGrp x₁ x₂) (ρ := rho) hOKp hρ3 hVOK bot_le
      (by norm_num [l17_card_V hc, Subgroup.card_bot])
      (fun n hn w hw => k18_K_normalizes_V hc n (hOKK hn) w hw)
      (fun n _ u hu => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hu]; group))
      (fun n hn => hOKnorm rho hρK n hn)
      (fun w hw => k18_K_normalizes_V hc rho hρK w hw)
      (fun u hu => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hu]; group))
      (fun w hw hwbot => by
        have h2 : rho * w * rho⁻¹ = w := by
          rw [Subgroup.mem_bot] at hwbot
          exact mul_inv_eq_one.mp hwbot
        have hwcomm : w * rho = rho * w := by
          calc w * rho = (rho * w * rho⁻¹) * rho := by rw [h2]
            _ = rho * w := by group
        have hwP : w ∈ ctxP t tau x₁ x₂ rho :=
          l17_Q_le_P hc (ctxYq_le_ctxQ (l17_V_le_Y hc hw))
        exact Subgroup.mem_bot.mpr (l17_CP_rho hc w hwP hwcomm))
  intro n hn v hv
  have h := hmain n hn v hv
  rw [Subgroup.mem_bot] at h
  exact mul_inv_eq_one.mp h

theorem k18_OK_comm_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxOK t tau x₁ x₂ rho, ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      n * y * n⁻¹ * y⁻¹ ∈ fourGrp x₁ x₂ := by
  have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hOKK : ctxOK t tau x₁ x₂ rho ≤ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1
  have hOKnorm : ∀ g ∈ ctxK t tau x₁ x₂ rho, ∀ k ∈ ctxOK t tau x₁ x₂ rho,
      g * k * g⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
  have hOKp : IsPGroup 2 (ctxOK t tau x₁ x₂ rho) := l18_OK_pgroup
  have hYOK : ctxYq t tau x₁ x₂ rho ≤ ctxOK t tau x₁ x₂ rho :=
    ctxYq_le_ctxQ.trans (le_sup_left.trans (l18_R_le_OK hc))
  have hVY : fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := l17_V_le_Y hc
  have hfpf : ∀ w ∈ ctxYq t tau x₁ x₂ rho,
      rho * w * rho⁻¹ * w⁻¹ ∈ fourGrp x₁ x₂ → w ∈ fourGrp x₁ x₂ :=
    fpf_section_of_fixed (U := fourGrp x₁ x₂) (W := ctxYq t tau x₁ x₂ rho) (ρ := rho)
      hρ3
      (fun u hu => k18_K_normalizes_V hc rho hρK u hu)
      hVY
      (fun w hw u hu => by
        have hcomm := IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ hw) (ctxYq_le_ctxQ (hVY hu))
        have hwu : w * u * w⁻¹ = u := by rw [hcomm]; group
        rw [hwu]; exact hu)
      (by norm_num [l17_card_V hc])
      (fun x hx hxfix => by
        have hxcomm : x * rho = rho * x := by
          calc x * rho = (rho * x * rho⁻¹) * rho := by rw [hxfix]
            _ = rho * x := by group
        have hxP : x ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc (ctxYq_le_ctxQ hx)
        rw [l17_CP_rho hc x hxP hxcomm]
        exact Subgroup.one_mem _)
  exact comm_mem_of_fpf_section (P := ctxOK t tau x₁ x₂ rho) (U := fourGrp x₁ x₂)
    (W := ctxYq t tau x₁ x₂ rho) (ρ := rho) hOKp hρ3 hYOK hVY
    (by norm_num [l17_card_Y hc, l17_card_V hc])
    (fun n hn w hw => l17_K_normalizes_Y hc n (hOKK hn) w hw)
    (fun n hn u hu => k18_K_normalizes_V hc n (hOKK hn) u hu)
    (fun n hn => hOKnorm rho hρK n hn)
    (fun w hw => l17_K_normalizes_Y hc rho hρK w hw)
    (fun u hu => k18_K_normalizes_V hc rho hρK u hu)
    hfpf

theorem k18_OK_comm_Q (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxOK t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      n * q * n⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hOKK : ctxOK t tau x₁ x₂ rho ≤ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1
  have hOKnorm : ∀ g ∈ ctxK t tau x₁ x₂ rho, ∀ k ∈ ctxOK t tau x₁ x₂ rho,
      g * k * g⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
  have hOKp : IsPGroup 2 (ctxOK t tau x₁ x₂ rho) := l18_OK_pgroup
  have hQOK : ctxQ t tau x₁ x₂ rho ≤ ctxOK t tau x₁ x₂ rho :=
    le_sup_left.trans (l18_R_le_OK hc)
  have hYQ : ctxYq t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ
  have hfpf : ∀ w ∈ ctxQ t tau x₁ x₂ rho,
      rho * w * rho⁻¹ * w⁻¹ ∈ ctxYq t tau x₁ x₂ rho → w ∈ ctxYq t tau x₁ x₂ rho :=
    fpf_section_of_fixed (U := ctxYq t tau x₁ x₂ rho) (W := ctxQ t tau x₁ x₂ rho) (ρ := rho)
      hρ3
      (fun u hu => l17_K_normalizes_Y hc rho hρK u hu)
      hYQ
      (fun w hw u hu => l17_K_normalizes_Y hc w (hc.normal_Q_K.1 hw) u hu)
      (by norm_num [l17_card_Y hc])
      (fun x hx hxfix => by
        have hxcomm : x * rho = rho * x := by
          calc x * rho = (rho * x * rho⁻¹) * rho := by rw [hxfix]
            _ = rho * x := by group
        have hxP : x ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc hx
        rw [l17_CP_rho hc x hxP hxcomm]
        exact Subgroup.one_mem _)
  exact comm_mem_of_fpf_section (P := ctxOK t tau x₁ x₂ rho) (U := ctxYq t tau x₁ x₂ rho)
    (W := ctxQ t tau x₁ x₂ rho) (ρ := rho) hOKp hρ3 hQOK hYQ
    (by norm_num [IsZ4Z4E4.card hc.q_iso, l17_card_Y hc])
    (fun n hn w hw => hc.normal_Q_K.2 n (hOKK hn) w hw)
    (fun n hn u hu => l17_K_normalizes_Y hc n (hOKK hn) u hu)
    (fun n hn => hOKnorm rho hρK n hn)
    (fun w hw => hc.normal_Q_K.2 rho hρK w hw)
    (fun u hu => l17_K_normalizes_Y hc rho hρK u hu)
    hfpf

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
