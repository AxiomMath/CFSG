module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Cpe2

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section F0

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA7.cpe_le_F0 (hb : PAB G L t E W z) (a : PA7 L t E z) {g : G} (hgC : g ∈ Cen a.ub)
    (hgE : ∀ x ∈ a.E₁, g * x = x * g) (hgF : g ∈ Open.pCoreOf 2 (Cen a.ub)) : g ∈ a.F₀ := by
  have hEub : ∀ x ∈ a.E₁, x * a.ub = a.ub * x := fun x hx =>
    mem_Cen.1 (componentLayerOf_le _ (a.E₁_le hx))
  have htt := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hub2 := PA5.ub_sq a.toPA6.toPA5
  have hubne := PA5.ub_ne_one a.toPA6.toPA5
  have htub := PA5.t_ub a.toPA6.toPA5 hb
  have hnotE : ¬ ∀ x ∈ a.E₁, t * x = x * t := fun h =>
    PA7.E1_not_cent_t hb a fun e he => (h e he).symm
  have hubF : a.ub ∈ Open.pCoreOf 2 (Cen a.ub) := a.ub_F
  have hgJ : ∀ j ∈ derivedIn a.Abar, g * j = j * g := fun j hj => hgE j (a.J_E₁ hj)
  have hubF0 : a.ub ∈ a.F₀ := by
    cases hdc : a.dcase
    · obtain ⟨-, -, -, -, hF, -⟩ := a.d8_props hdc
      rw [hF]; exact mem_sup_left (mem_zpowers _)
    · obtain ⟨hF, -⟩ := a.F₀_e4 hdc
      rw [hF]; exact mem_zpowers _
  by_cases hg1 : g = 1
  · rw [hg1]; exact one_mem _
  by_cases hgub : g = a.ub
  · rw [hgub]; exact hubF0
  cases hdc : a.dcase
  ·
    obtain ⟨ho, hu1Cen, hu1J, htu1, hF0, hnot, -⟩ := a.d8_props hdc
    have hF4 : Nat.card ↥(Open.pCoreOf 2 (Cen a.ub)) ≤ 4 := by
      have := a.F_card
      rw [hdc] at this
      simpa using this
    have hsq : a.u₁ * a.u₁ = 1 := by
      have := pow_orderOf_eq_one a.u₁
      rwa [ho, pow_two] at this
    have hu1F0 : a.u₁ ∈ a.F₀ := by rw [hF0]; exact mem_sup_right (mem_zpowers _)
    have hu1E : ∀ x ∈ a.E₁, a.u₁ * x = x * a.u₁ := fun x hx =>
      Subgroup.mem_centralizer_iff.1 (a.E₁_cent_F₀ hx) a.u₁ hu1F0
    have htF : t * g * t⁻¹ ∈ Open.pCoreOf 2 (Cen a.ub) :=
      pCoreOf_normal (Cen a.ub) (mem_Cen.2 htub) hgF
    have h4 := four_elements (Open.pCoreOf 2 (Cen a.ub)) hF4 hubF hgF hubne hub2 hg1 hgub htF
    rcases h4 with h | h | h | h
    · exfalso; apply hg1
      calc g = t⁻¹ * (t * g * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    · exfalso; apply hgub
      calc g = t⁻¹ * (t * g * t⁻¹) * t := by group
        _ = t⁻¹ * a.ub * t := by rw [h]
        _ = a.ub := by rw [hti, htub, mul_assoc, htt, mul_one]
    · exfalso
      have hgt : g * t = t * g := (mul_inv_eq_iff_eq_mul.1 h).symm
      have hV := PA5.cent_t_J hb a.toPA6.toPA5 hgt hgJ
      rw [mem_Vsub_iff htt hub2 htub] at hV
      rcases hV with h' | h' | h' | h'
      · exact hg1 h'
      · exact hnotE fun x hx => by have := hgE x hx; rw [h'] at this; exact this
      · exact hgub h'
      · exact hnotE fun x hx => cent_of_tub (by have := hgE x hx; rw [h'] at this; exact this)
          (hEub x hx)
    · have hg'ub : t * g * t⁻¹ = g * a.ub := h
      have hg't : (g * a.u₁) * t = t * (g * a.u₁) := by
        have e : t * (g * a.u₁) * t⁻¹ = g * a.u₁ := by
          calc t * (g * a.u₁) * t⁻¹ = (t * g * t⁻¹) * (t * a.u₁ * t⁻¹) := by group
            _ = (g * a.ub) * (a.ub * a.u₁) := by rw [hg'ub, htu1]
            _ = g * (a.ub * a.ub) * a.u₁ := by simp only [mul_assoc]
            _ = g * a.u₁ := by rw [hub2, mul_one]
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
      have hg'J : ∀ j ∈ derivedIn a.Abar, (g * a.u₁) * j = j * (g * a.u₁) := by
        intro j hj
        have h1 : j * a.u₁ = a.u₁ * j := Subgroup.mem_centralizer_iff.1 hu1J j hj
        calc (g * a.u₁) * j = g * (a.u₁ * j) := by rw [mul_assoc]
          _ = g * (j * a.u₁) := by rw [h1]
          _ = (g * j) * a.u₁ := by rw [mul_assoc]
          _ = (j * g) * a.u₁ := by rw [hgJ j hj]
          _ = j * (g * a.u₁) := by rw [mul_assoc]
      have hV := PA5.cent_t_J hb a.toPA6.toPA5 hg't hg'J
      rw [mem_Vsub_iff htt hub2 htub] at hV
      have hg_eq : g = (g * a.u₁) * a.u₁ := by rw [mul_assoc, hsq, mul_one]
      have hcE : ∀ x ∈ a.E₁, (g * a.u₁) * x = x * (g * a.u₁) := by
        intro x hx
        calc (g * a.u₁) * x = g * (a.u₁ * x) := by rw [mul_assoc]
          _ = g * (x * a.u₁) := by rw [hu1E x hx]
          _ = (g * x) * a.u₁ := by rw [mul_assoc]
          _ = (x * g) * a.u₁ := by rw [hgE x hx]
          _ = x * (g * a.u₁) := by rw [mul_assoc]
      rw [hF0]
      rcases hV with h' | h' | h' | h'
      · rw [h', one_mul] at hg_eq
        rw [hg_eq]; exact mem_sup_right (mem_zpowers _)
      · exfalso; exact hnotE fun x hx => by have := hcE x hx; rw [h'] at this; exact this
      · rw [h'] at hg_eq
        rw [hg_eq]
        exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
      · exfalso
        exact hnotE fun x hx => cent_of_tub (by have := hcE x hx; rw [h'] at this; exact this)
          (hEub x hx)
  ·
    obtain ⟨hF, -⟩ := a.F₀_e4 hdc
    have hF2 : Nat.card ↥(Open.pCoreOf 2 (Cen a.ub)) ≤ 2 := by
      have := a.F_card
      rw [hdc] at this
      simpa using this
    rw [hF]
    by_contra hgz
    have hl : [1, a.ub, g].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨hubne.symm, fun h => hg1 h.symm⟩, fun h => hgub h.symm, by simp⟩
    have := list_length_le_card (Open.pCoreOf 2 (Cen a.ub)) [1, a.ub, g] hl (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact one_mem _
      · exact hubF
      · exact hgF)
    simp at this
    omega

end F0

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
