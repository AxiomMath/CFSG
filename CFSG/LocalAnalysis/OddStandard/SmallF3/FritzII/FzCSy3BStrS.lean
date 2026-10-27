module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrM

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_s_FU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : F ≤ U :=
  hs.chain.2.1.trans hs.chain.2.2.1

private theorem fzc_sy3_s_aU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ U :=
  fzc_sy3_s_FU hs hs.a_mem

private theorem fzc_sy3_s_bU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b ∈ U :=
  hs.chain.2.2.1 hs.b_mem

private theorem fzc_sy3_s_cU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : c ∈ U :=
  hs.chain.2.2.2.2.1 hs.c_mem

private theorem fzc_sy3_s_abU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a * b ∈ U :=
  mul_mem (fzc_sy3_s_aU hs) (fzc_sy3_s_bU hs)

private theorem fzc_sy3_s_acU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a * c ∈ U :=
  mul_mem (fzc_sy3_s_aU hs) (fzc_sy3_s_cU hs)

private theorem fzc_sy3_s_bcU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : b * c ∈ U :=
  mul_mem (fzc_sy3_s_bU hs) (fzc_sy3_s_cU hs)

private theorem fzc_sy3_s_shift (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {s : G} (hsU : s ∈ U) : ∀ w ∈ Wp, w * (s * w * s⁻¹) ∈ baseGrp x₁ x₂ := by
  intro w hw
  rcases (hs.Wp_mem).mp hw with hwE | htwE
  · exact mul_mem hwE (hs.nrm_E s hsU w hwE)
  · set e : G := t * w with he
    have heE : e ∈ baseGrp x₁ x₂ := by rw [he]; exact htwE
    have hw_eq : w = e * t := by rw [he]; exact hs.fzc_eq_mul_t htwE
    have he3 : s * e * s⁻¹ ∈ baseGrp x₁ x₂ := by
      rw [he]; exact hs.nrm_E s hsU (t * w) htwE
    have he2 : s * t * s⁻¹ * t ∈ baseGrp x₁ x₂ := hs.conj_t s hsU
    have hxE : (s * e * s⁻¹) * (s * t * s⁻¹ * t) ∈ baseGrp x₁ x₂ := mul_mem he3 he2
    have htcomm : Commute t ((s * e * s⁻¹) * (s * t * s⁻¹ * t)) :=
      hs.fzc_commute_t_E _ hxE
    have hprod : w * (s * w * s⁻¹) = e * ((s * e * s⁻¹) * (s * t * s⁻¹ * t)) := by
      rw [hw_eq]
      calc (e * t) * (s * (e * t) * s⁻¹)
          = e * (t * ((s * e * s⁻¹) * (s * t * s⁻¹ * t))) * t⁻¹ := by group
        _ = e * (((s * e * s⁻¹) * (s * t * s⁻¹ * t)) * t) * t⁻¹ := by
              rw [htcomm.eq]
        _ = e * ((s * e * s⁻¹) * (s * t * s⁻¹ * t)) := by group
    rw [hprod]
    exact mul_mem heE hxE

private theorem fzc_sy3_s_F_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ f ∈ F, f * f ∈ Wp := by
  intro f hf
  obtain ⟨w, hw, rfl | hf_eq⟩ := (hs.F_mem).mp hf
  · exact mul_mem hw hw
  · rw [hf_eq]
    have h := mul_mem (mul_mem hw (hs.nrm a (fzc_sy3_s_aU hs) w hw)) (hs.sq_mem.1)
    have heq : (w * a) * (w * a) = (w * (a * w * a⁻¹)) * (a * a) := by group
    rw [heq]
    exact h

private theorem fzc_sy3_s_F_cong (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ f ∈ F, ∃ z ∈ Wp, (b * c) * f * (b * c)⁻¹ = z * f := by
  intro f hf
  have hbcU : b * c ∈ U := fzc_sy3_s_bcU hs
  obtain ⟨w, hw, hf_eq | hf_eq⟩ := (hs.F_mem).mp hf
  · refine ⟨((b * c) * w * (b * c)⁻¹) * w⁻¹,
      mul_mem (hs.nrm (b * c) hbcU w hw) (inv_mem hw), ?_⟩
    rw [hf_eq]; group
  · rw [hf_eq]
    refine ⟨((b * c) * w * (b * c)⁻¹) * ((b * c) * a * (b * c)⁻¹ * a⁻¹) * w⁻¹,
      mul_mem (mul_mem (hs.nrm (b * c) hbcU w hw) hs.bc_a) (inv_mem hw), ?_⟩
    group

private theorem fzc_sy3_s_sq_aux (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {s : G} (hsU : s ∈ U) (hts : t * (s * s) ∈ baseGrp x₁ x₂) :
    ∀ w ∈ Wp, (w * s) ^ 2 ∉ baseGrp x₁ x₂ := by
  intro w hw h
  have hm : w * (s * w * s⁻¹) ∈ baseGrp x₁ x₂ := fzc_sy3_s_shift hs hsU w hw
  have hssE : s * s ∈ baseGrp x₁ x₂ := by
    have hsq : (w * s) ^ 2 = (w * (s * w * s⁻¹)) * (s * s) := by
      rw [pow_two]; group
    have : s * s = (w * (s * w * s⁻¹))⁻¹ * (w * s) ^ 2 := by rw [hsq]; group
    rw [this]
    exact mul_mem (inv_mem hm) h
  exact hs.t_notin (by
    have : t = (t * (s * s)) * (s * s)⁻¹ := by group
    rw [this]
    exact mul_mem hts (inv_mem hssE))

theorem M₃_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ v ∈ M₃, v ∉ F → v ^ 2 ∈ F ∧ v ^ 2 ∉ Wp := by
  intro v hv hvF
  have hWF : Wp ≤ F := hs.chain.1
  rcases (hs.M₃_mem).mp hv with ⟨f, hf, hfeq | hfeq⟩
  · exact absurd (by rw [hfeq]; exact hf) hvF
  · obtain ⟨z, hz, hz_eq⟩ := fzc_sy3_s_F_cong hs f hf
    obtain ⟨w₀, hw₀, hw₀_eq⟩ := hs.bc_sq
    have hz' : (f * z * f⁻¹) * (f * f) * w₀ ∈ Wp :=
      mul_mem (mul_mem (hs.nrm f (fzc_sy3_s_FU hs hf) z hz) (fzc_sy3_s_F_sq hs f hf)) hw₀
    have hv2 : v ^ 2 = ((f * z * f⁻¹) * (f * f) * w₀) * a := by
      rw [hfeq]
      calc (f * (b * c)) ^ 2
          = f * ((b * c) * f * (b * c)⁻¹) * ((b * c) * (b * c)) := by
            rw [pow_two]; group
        _ = f * (z * f) * (w₀ * a) := by rw [hz_eq, hw₀_eq]
        _ = ((f * z * f⁻¹) * (f * f) * w₀) * a := by group
    constructor
    · rw [hv2]
      exact mul_mem (hWF hz') hs.a_mem
    · intro hv2W
      have haW : a ∈ Wp := by
        have hthis : a = ((f * z * f⁻¹) * (f * f) * w₀)⁻¹ * v ^ 2 := by
          rw [hv2]; group
        rw [hthis]
        exact mul_mem (inv_mem hz') hv2W
      exact hs.a_notin haW

theorem sq_notE (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ u ∈ U, u ∉ Wp → u ^ 2 ∈ Wp → u ^ 2 ∉ baseGrp x₁ x₂ := by
  intro u hu huW hu2
  have hPU : P ≤ U := hs.chain.2.2.1
  have hFP : F ≤ P := hs.chain.2.1
  have hWF : Wp ≤ F := hs.chain.1
  obtain ⟨sq_a, sq_b, sq_c, sq_ab, sq_ac⟩ := hs.sq_tE
  rcases (hs.U_mem).mp hu with ⟨p, hp, rfl | rfl⟩
  · rcases (hs.P_mem).mp hp with ⟨f, hf, rfl | rfl⟩
    · rcases (hs.F_mem).mp hf with ⟨w, hw, h_eq | h_eq⟩
      · rw [h_eq] at huW
        exact absurd hw huW
      · rw [h_eq]
        exact fzc_sy3_s_sq_aux hs (fzc_sy3_s_aU hs) sq_a w hw
    · rcases (hs.F_mem).mp hf with ⟨w, hw, h_eq | h_eq⟩
      · rw [h_eq]
        exact fzc_sy3_s_sq_aux hs (fzc_sy3_s_bU hs) sq_b w hw
      · rw [h_eq, mul_assoc]
        exact fzc_sy3_s_sq_aux hs (fzc_sy3_s_abU hs) sq_ab w hw
  · rcases (hs.P_mem).mp hp with ⟨f, hf, rfl | rfl⟩
    · rcases (hs.F_mem).mp hf with ⟨w, hw, h_eq | h_eq⟩
      · rw [h_eq]
        exact fzc_sy3_s_sq_aux hs (fzc_sy3_s_cU hs) sq_c w hw
      · rw [h_eq, mul_assoc]
        exact fzc_sy3_s_sq_aux hs (fzc_sy3_s_acU hs) sq_ac w hw
    · rcases (hs.F_mem).mp hf with ⟨w, hw, h_eq | h_eq⟩
      · rw [h_eq]
        have huM₃ : (w * b) * c ∈ M₃ := by
          rw [hs.M₃_mem]
          exact ⟨w, hWF hw, Or.inr (by group)⟩
        have huF' : (w * b) * c ∉ F := by
          intro hF
          have hbcF : b * c ∈ F := by
            have h : b * c = w⁻¹ * ((w * b) * c) := by group
            rw [h]
            exact mul_mem (inv_mem (hWF hw)) hF
          have hcP : c ∈ P := by
            have h : c = b⁻¹ * (b * c) := by group
            rw [h]
            exact mul_mem (inv_mem hs.b_mem) (hFP hbcF)
          exact hs.c_notin hcP
        have hnotW : ((w * b) * c) ^ 2 ∉ Wp := (hs.M₃_sq _ huM₃ huF').2
        intro hE
        exact hnotW (hs.E_le_Wp hE)
      · rw [h_eq]
        have hwaF : w * a ∈ F := mul_mem (hWF hw) hs.a_mem
        have huM₃ : ((w * a) * b) * c ∈ M₃ := by
          rw [hs.M₃_mem]
          exact ⟨w * a, hwaF, Or.inr (by group)⟩
        have huF' : ((w * a) * b) * c ∉ F := by
          intro hF
          have hbcF : b * c ∈ F := by
            have h : b * c = (w * a)⁻¹ * (((w * a) * b) * c) := by group
            rw [h]
            exact mul_mem (inv_mem hwaF) hF
          have hcP : c ∈ P := by
            have h : c = b⁻¹ * (b * c) := by group
            rw [h]
            exact mul_mem (inv_mem hs.b_mem) (hFP hbcF)
          exact hs.c_notin hcP
        have hnotW : (((w * a) * b) * c) ^ 2 ∉ Wp := (hs.M₃_sq _ huM₃ huF').2
        intro hE
        exact hnotW (hs.E_le_Wp hE)

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
