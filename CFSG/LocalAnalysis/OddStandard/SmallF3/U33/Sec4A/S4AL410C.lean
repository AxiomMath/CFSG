module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL45

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem inf_S_eq_fourGrp_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮)
    (hC : invCent t ⊓ 𝒮 = S) (hE𝒮 : E ≤ 𝒮) (hEn : (E.subgroupOf 𝒮).Normal)
    (hEe : CFSG.Open.IsElemAbelian 2 E) (hEc : Nat.card E = 8)
    (hno : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e) (hES : ¬ E ≤ S)
    (hCE : 4 ≤ Nat.card ↥(E ⊓ invCent t)) : E ⊓ S = fourGrp x₁ x₂ := by
  have hE0_eq : E ⊓ invCent t = E ⊓ S := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hx' : x ∈ invCent t ⊓ 𝒮 := ⟨hx.2, hE𝒮 hx.1⟩
      rwa [hC] at hx'
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, h.toCtx0.le_invCent hx.2⟩
  set V : Subgroup G := E ⊓ S with hVdef
  have hEin : E ⊓ invCent t = V := by rw [hE0_eq, hVdef]
  have hV_le_E : V ≤ E := by rw [hVdef]; exact inf_le_left
  have hV_le_S : V ≤ S := by rw [hVdef]; exact inf_le_right
  have hCE' : 4 ≤ Nat.card V := by
    have h := hCE
    rw [hEin] at h
    exact h
  have hV_ne_E : V ≠ E := by
    intro hEq
    apply hES
    intro x hx
    exact hV_le_S (by rw [hEq]; exact hx)
  have hcard_lt8 : Nat.card V < 8 := by
    have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne hV_le_E hV_ne_E)
    rwa [hEc] at h
  have hcard_sub : Nat.card (V.subgroupOf E) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_E).toEquiv
  have hdiv8 : Nat.card V ∣ 8 := by
    rw [← hcard_sub]
    simpa [hEc] using Subgroup.card_subgroup_dvd_card (V.subgroupOf E)
  have hcardV : Nat.card V = 4 := by
    have hdiv8' : Nat.card V ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdiv8
    obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv8'
    have h4le : 4 ≤ 2 ^ k := by rw [← hk]; exact hCE'
    have hlt8 : 2 ^ k < 8 := by rw [← hk]; exact hcard_lt8
    interval_cases k
    · norm_num at h4le
    · norm_num at h4le
    · norm_num at hk
      exact hk
    · norm_num at hlt8
  have hEn' : ∀ h k, h ∈ E → k ∈ 𝒮 → k * h * k⁻¹ ∈ E :=
    (Subgroup.normal_subgroupOf_iff hE𝒮).mp hEn
  have hN : NormalIn V S := by
    refine ⟨hV_le_S, ?_⟩
    intro g hg k hk
    rw [Subgroup.mem_inf] at hk ⊢
    exact ⟨hEn' k g hk.1 (hS𝒮 hg), S.mul_mem (S.mul_mem hg hk.2) (S.inv_mem hg)⟩
  have hVel : CFSG.Open.IsElemAbelian 2 V := CFSG.Open.IsElemAbelian.mono hEe hV_le_E
  have hno' : ∀ g : G, ∀ v ∈ V, g * t * g⁻¹ ≠ v := fun g v hv => hno g v (hV_le_E hv)
  exact (lemma4_5_of h h2 h43 h44 V hN hVel hcardV hno').1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
