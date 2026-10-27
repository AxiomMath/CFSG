module

public import CFSG.LargeExtraspecial.AS35QIxBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem fiveNineTwo_of_hyp (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet)
    (hR : ∀ (htM : t ∈ S.M) (U : Subgroup S.O), U ≤ S.Mbar → (∀ u ∈ U, u * u = 1) →
      S.ρ ⟨t, htM⟩ ∈ U →
      (∀ c ∈ S.Mbar, c * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) →
        U ≤ zpowers (S.ρ ⟨t, htM⟩)) {c : G}
    (hc : c * (S.z * t) = S.z * t * c) : c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have hS4 := hS.sixFour
  have htM := S.mem_M_of_mem_ESet hS4 ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htQ := S.not_mem_QG_of_mem_ESet hS.weak ht.1
  set Γ : Set G := {a | ∃ x : G, x * S.z * x⁻¹ = a ∧ x⁻¹ * (S.z * t) * x ∈ S.QG} with hΓ
  have hΓc : ∀ d : G, d * (S.z * t) = S.z * t * d → ∀ a ∈ Γ, d * a * d⁻¹ ∈ Γ := by
    rintro d hd _ ⟨x, rfl, hx⟩
    refine ⟨d * x, by group, ?_⟩
    have hd' : d⁻¹ * (S.z * t) * d = S.z * t := by rw [mul_assoc, ← hd]; group
    rwa [show (d * x)⁻¹ * (S.z * t) * (d * x) = x⁻¹ * (d⁻¹ * (S.z * t) * d) * x by group, hd']
  have hΔΓ : ∀ p ∈ S.zConj (S.HAt h), p ≠ S.z → p ≠ t → p ∈ Γ := by
    intro p hp hpz hpt
    obtain ⟨k, hk, hkQ⟩ := S.exists_conj_mem_QG_J hS ht hh hp hpz hpt
    exact ⟨k, hk, hkQ⟩
  have hzΓ : S.z ∉ Γ := by
    rintro ⟨x, hx, hxQ⟩
    apply htQ
    have h1 := S.conj_mem_QG (S.mem_M_of_conj_eq_z hx) hxQ
    rw [show x * (x⁻¹ * (S.z * t) * x) * x⁻¹ = S.z * t by group] at h1
    have h2 := S.QG.mul_mem S.z_mem_QG h1
    rwa [← mul_assoc, S.z_mul_z, one_mul] at h2
  have hΓM : ∀ a ∈ Γ, a ∈ S.M := by
    rintro _ ⟨x, rfl, hx⟩
    exact S.mem_M_iff.mpr (S.conj_z_commute_J hS ht hh hx)
  have hΓΓ : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a := by
    rintro _ ⟨x, rfl, hx⟩ _ ⟨y, rfl, hy⟩
    exact (S.commute_of_mem_oTwoCent_J hS ht hx (S.conj_z_mem_oTwoCent_J hS ht hy)).symm
  have hΓ2 : ∀ a ∈ Γ, a * a = 1 := by
    rintro _ ⟨x, rfl, -⟩
    rw [show x * S.z * x⁻¹ * (x * S.z * x⁻¹) = x * (S.z * S.z) * x⁻¹ by group, S.z_mul_z]
    group
  set B : Set S.O := {σ | ∃ a ∈ Γ, ∃ ha : a ∈ S.M, S.ρ ⟨a, ha⟩ = σ} with hB
  have hUM : closure B ≤ S.Mbar := by
    rw [closure_le]
    rintro _ ⟨a, -, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hU2 : ∀ u ∈ closure B, u * u = 1 := by
    intro u hu
    have h1 := AS35J.mul_self_mem_pair_of_mem_closure (A := B) (e := (1 : S.O)) (mul_one 1)
      (by rintro _ ⟨a, haΓ, ha, rfl⟩; exact S.ρ_mul_self_eq_one ha (hΓ2 a haΓ))
      (fun _ _ => by group)
      (by
        rintro _ ⟨a, haΓ, ha, rfl⟩ _ ⟨b, hbΓ, hb, rfl⟩
        left
        have hab : S.ρ ⟨a, ha⟩ * S.ρ ⟨b, hb⟩ = S.ρ ⟨b, hb⟩ * S.ρ ⟨a, ha⟩ := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hΓΓ a haΓ b hbΓ)
        rw [hab]
        group) u hu
    rcases h1 with h1 | h1 <;> exact h1
  obtain ⟨p, -, hpH, hpz, hpt, -⟩ := S.exists_two_mem_delta_J ht hh
  have htU : S.ρ ⟨t, htM⟩ ∈ closure B := by
    have hpΓ := hΔΓ p hpH hpz hpt
    have hpM := hΓM p hpΓ
    have hpt' := (S.mul_mem_QG_of_mem_zConj hS ht hh htM hpH hpz).1
    have e : S.ρ ⟨p, hpM⟩ = S.ρ ⟨t, htM⟩ := by
      have h1 : S.ρ ⟨p, hpM⟩ * S.ρ ⟨t, htM⟩ = 1 := by
        rw [← map_mul]
        exact (S.ρ_eq_one_iff _).mpr hpt'
      calc S.ρ ⟨p, hpM⟩ = S.ρ ⟨p, hpM⟩ * (S.ρ ⟨t, htM⟩ * S.ρ ⟨t, htM⟩) := by
            rw [S.ρ_mul_self_eq_one htM htt, mul_one]
        _ = S.ρ ⟨t, htM⟩ := by rw [← mul_assoc, h1, one_mul]
    rw [← e]
    exact subset_closure ⟨p, hpΓ, hpM, rfl⟩
  have hUn : ∀ c' ∈ S.Mbar, c' * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c' →
      ∀ u ∈ closure B, c' * u * c'⁻¹ ∈ closure B := by
    rintro _ ⟨⟨m, hmM⟩, rfl⟩ hcm u hu
    obtain ⟨m', hm'M, hm't, hm'ρ⟩ := S.exists_commute_rho_eq_J hS ht htM hmM hcm
    rw [← hm'ρ]
    have hm'zt : m' * (S.z * t) = S.z * t * m' := by
      calc m' * (S.z * t) = m' * S.z * t := by group
        _ = S.z * (m' * t) := by rw [S.mem_M_iff.mp hm'M]; group
        _ = S.z * t * m' := by rw [hm't]; group
    induction hu using closure_induction with
    | mem σ hσ =>
      obtain ⟨a, haΓ, ha, rfl⟩ := hσ
      have hmaM : m' * a * m'⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm'M ha) (S.M.inv_mem hm'M)
      refine subset_closure ⟨m' * a * m'⁻¹, hΓc m' hm'zt a haΓ, hmaM, ?_⟩
      have e : (⟨m' * a * m'⁻¹, hmaM⟩ : S.M) = ⟨m', hm'M⟩ * ⟨a, ha⟩ * ⟨m', hm'M⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    | one => simp
    | mul u₁ u₂ _ _ ih₁ ih₂ =>
      rw [show S.ρ ⟨m', hm'M⟩ * (u₁ * u₂) * (S.ρ ⟨m', hm'M⟩)⁻¹ =
        S.ρ ⟨m', hm'M⟩ * u₁ * (S.ρ ⟨m', hm'M⟩)⁻¹ * (S.ρ ⟨m', hm'M⟩ * u₂ * (S.ρ ⟨m', hm'M⟩)⁻¹)
        by group]
      exact mul_mem ih₁ ih₂
    | inv u _ ih =>
      rw [show S.ρ ⟨m', hm'M⟩ * u⁻¹ * (S.ρ ⟨m', hm'M⟩)⁻¹ =
        (S.ρ ⟨m', hm'M⟩ * u * (S.ρ ⟨m', hm'M⟩)⁻¹)⁻¹ by group]
      exact inv_mem ih
  have hle := hR htM (closure B) hUM hU2 htU hUn
  have hΓt : ∀ a ∈ Γ, a * t ∈ S.QG := by
    intro a haΓ
    have haM := hΓM a haΓ
    have h1 : S.ρ ⟨a, haM⟩ ∈ zpowers (S.ρ ⟨t, htM⟩) := hle (subset_closure ⟨a, haΓ, haM, rfl⟩)
    rw [Setting.mem_zpowers_iff_of_mul_self (S.ρ_mul_self_eq_one htM htt)] at h1
    rcases h1 with h1 | h1
    · exfalso
      have haQ : a ∈ S.QG := (S.ρ_eq_one_iff _).mp h1
      obtain ⟨x, rfl, hx⟩ := haΓ
      exact hzΓ ⟨x, hS.weak x haQ, hx⟩
    · have e : (⟨a * t, S.M.mul_mem haM htM⟩ : S.M) = ⟨a, haM⟩ * ⟨t, htM⟩ := rfl
      exact (S.ρ_eq_one_iff ⟨a * t, S.M.mul_mem haM htM⟩).mp
        (by rw [e, map_mul, h1, S.ρ_mul_self_eq_one htM htt])
  obtain ⟨g, hg1, hg2⟩ := S.exists_swap_J hS ht hh
  have hgzt : g⁻¹ * (S.z * t) = S.z * t * g⁻¹ := by
    have e : g * (S.z * t) * g⁻¹ = S.z * t := by
      rw [show g * (S.z * t) * g⁻¹ = (g * S.z * g⁻¹) * (g * t * g⁻¹) by group, hg1, hg2]
      exact S.mem_M_iff.mp htM
    calc g⁻¹ * (S.z * t) = g⁻¹ * (g * (S.z * t) * g⁻¹) := by rw [e]
      _ = S.z * t * g⁻¹ := by group
  have hΓz : ∀ a ∈ Γ, a * S.z ∈ S.Qa h := by
    intro a haΓ
    have h1 := hΓt _ (hΓc g⁻¹ hgzt a haΓ)
    rw [← S.Qa_eq_of_conj_eq (hg1.trans hh.symm), S.mem_Qa_iff_inv_conj_mem]
    have e : g⁻¹ * S.z * g = t := by rw [← hg2]; group
    rwa [show g⁻¹ * (a * S.z) * g = g⁻¹ * a * g⁻¹⁻¹ * t by rw [← e]; group]
  have hΓΩ : ∀ a ∈ Γ, a ∈ S.zConj (S.HAt h) := by
    intro a haΓ
    have haz : IsConj S.z a := by
      obtain ⟨x, rfl, -⟩ := haΓ
      exact isConj_iff.mpr ⟨x, rfl⟩
    exact S.mem_zConj_of_mul_mem_J hS ht hh haz (hΓt a haΓ) (hΓz a haΓ)
  obtain ⟨p₁, p₂, hp₁H, hp₁z, hp₁t, hp₂H, hp₂z, hp₂t, hne⟩ := S.exists_two_mem_delta_J ht hh
  have hc₁ := hΓΩ _ (hΓc c hc p₁ (hΔΓ p₁ hp₁H hp₁z hp₁t))
  have hc₂ := hΓΩ _ (hΓc c hc p₂ (hΔΓ p₂ hp₂H hp₂z hp₂t))
  have hzH := S.conj_mem_zConj_J hS ht hh hp₁H hp₂H hne hc₁ hc₂ (Asc77.self_mem_conjIn S.z _)
  by_contra hcon
  push Not at hcon
  have hcinv : c⁻¹ * (S.z * t) = S.z * t * c⁻¹ := by
    calc c⁻¹ * (S.z * t) = c⁻¹ * (S.z * t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (S.z * t)) * c⁻¹ := by rw [hc]
      _ = S.z * t * c⁻¹ := by group
  have h1 := hΓc c⁻¹ hcinv _ (hΔΓ _ hzH hcon.1 hcon.2)
  rw [show c⁻¹ * (c * S.z * c⁻¹) * c⁻¹⁻¹ = S.z by group] at h1
  exact hzΓ h1


namespace IxSetup

variable (T : IxSetup S)

theorem alpha_ne_one : T.α ≠ 1 := by
  intro h
  apply T.hζ1
  have e := T.hαβ
  rw [h, one_mul, mul_one] at e
  calc T.ζ = T.ζ * T.β * T.β⁻¹ := by group
    _ = 1 := by rw [← e]; group

theorem tb_ne_one : T.tb ≠ 1 := by
  intro h
  have e : T.tb * T.α * T.tb⁻¹ = T.α⁻¹ := T.htα
  rw [h, one_mul, inv_one, mul_one] at e
  apply T.alpha_ne_one
  have h2 : T.α * T.α = 1 := by
    calc T.α * T.α = T.α * T.α⁻¹ := by rw [← e]
      _ = 1 := mul_inv_cancel _
  calc T.α = T.α ^ 3 * (T.α * T.α)⁻¹ := by group
    _ = 1 := by rw [T.hα3, h2]; group

theorem fiveNineHyp {U : Subgroup S.O} (hUM : U ≤ S.Mbar) (hU2 : ∀ u ∈ U, u * u = 1)
    (htU : T.tb ∈ U) (hUn : ∀ c ∈ S.Mbar, c * T.tb = T.tb * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) :
    U ≤ zpowers T.tb := by
  intro u hu
  by_cases hζu : u * T.ζ = T.ζ * u
  · have hcomm : u * T.tb = T.tb * u := by
      have h := hU2 _ (U.mul_mem hu htU)
      calc u * T.tb = (u * T.tb)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
        _ = T.tb⁻¹ * u⁻¹ := mul_inv_rev _ _
        _ = T.tb * u := by
          rw [inv_eq_of_mul_eq_one_right (hU2 _ htU), inv_eq_of_mul_eq_one_right (hU2 _ hu)]
    rcases T.eq_or_of_commute_O hζu T.tb_comm_zeta (hU2 u hu) T.tb_mul_self hcomm with
      h | h | h
    · rw [h]
      exact mem_zpowers _
    · rw [h]
      exact one_mem _
    · exact absurd h T.tb_ne_one
  · exfalso
    have hinv := T.conj_inv_of_not_comm (hUM hu) hζu
    have h1 : T.ζ * u * T.ζ⁻¹ ∈ U := hUn T.ζ T.zeta_mem_Mbar T.zeta_comm_tb u hu
    have h2 : T.ζ * u * T.ζ⁻¹ * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have e : T.ζ * u * T.ζ⁻¹ * u⁻¹ = T.ζ * T.ζ := by
      have : u * T.ζ⁻¹ * u⁻¹ = T.ζ := by
        rw [show u * T.ζ⁻¹ * u⁻¹ = (u * T.ζ * u⁻¹)⁻¹ by group, hinv, inv_inv]
      calc T.ζ * u * T.ζ⁻¹ * u⁻¹ = T.ζ * (u * T.ζ⁻¹ * u⁻¹) := by group
        _ = T.ζ * T.ζ := by rw [this]
    rw [e] at h2
    have h4 := hU2 _ h2
    apply T.hζ1
    calc T.ζ = (T.ζ * T.ζ * (T.ζ * T.ζ)) * (T.ζ ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, T.hζ3]; group

theorem fiveNineTwo (hS : S.SixHyp) {c : G} (hc : c * (S.z * T.t) = S.z * T.t * c) :
    c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = T.t :=
  fiveNineTwo_of_hyp hS T.hgD (fun _ _ hUM hU2 htU hUn => T.fiveNineHyp hUM hU2 htU hUn) hc

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
