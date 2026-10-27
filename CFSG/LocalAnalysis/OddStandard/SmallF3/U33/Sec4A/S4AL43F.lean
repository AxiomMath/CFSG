module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem false_of_card_eq_four (hI : Sec4Inputs) (hG : Sec4Glob G)
    (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index) (hP : Nat.card (twoCore t) = 4) :
    False := by
  obtain ⟨p, hp, hpt⟩ := exists_sq_root_of_four_le_card h.hyp (by omega)
  have hτ : tau * p * tau⁻¹ = p⁻¹ := tau_conj_eq_inv_of_sq_eq_t h h2 hp hpt
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.toCtx0.isPGroup h2
  have hC : invCent t ⊓ (𝒮 : Subgroup G) = S := (sylow_facts_of_l42 h h2 𝒮 h𝒮).1
  obtain ⟨E, hE𝒮, hEn, hEe, hEc⟩ := hI.exists_normal_e8 hG h.hyp 𝒮
  have hcardS : Nat.card S = 2 ^ 8 := by rw [h.card_S, hP]; norm_num
  have hno : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e := by
    intro g e he hge
    have he1 : e ≠ 1 := by
      intro heq
      apply t_ne_one h.hyp
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * e * g := by rw [hge]
        _ = 1 := by rw [heq]; group
    refine false_of_mem_normal_E8_of_le_two_pow_eight hE𝒮 hEn hEc hG.dvd he he1 ?_
    intro Q hQ hQc
    have hQc' : Q ≤ centralizer ({g * t * g⁻¹} : Set G) := by
      rw [hge]; exact hQc
    calc Nat.card Q ≤ Nat.card S :=
          card_le_card_of_isPGroup_le_centralizer_conj (S := S) (t := t)
            h.toCtx0.le_invCent h.toCtx0.isPGroup h.toCtx0.relIndex_odd g hQ hQc'
      _ = 2 ^ 8 := hcardS
  have htE : t ∉ E := by
    intro htEmem
    exact hno 1 t htEmem (by group)
  have hEnS : NormalIn (E ⊓ S) S := by
    refine ⟨inf_le_right, fun s hs k hk => ?_⟩
    have hs𝒮 : s ∈ (𝒮 : Subgroup G) := h𝒮.le hs
    have hkE : k ∈ E := hk.1
    have hkS : k ∈ S := hk.2
    have hk𝒮 : k ∈ (𝒮 : Subgroup G) := h𝒮.le hkS
    have hkmem : (⟨k, hk𝒮⟩ : ↥(𝒮 : Subgroup G)) ∈ E.subgroupOf (𝒮 : Subgroup G) := by
      rw [Subgroup.mem_subgroupOf]; exact hkE
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hconj := hEn.conj_mem (⟨k, hk𝒮⟩ : ↥(𝒮 : Subgroup G)) hkmem
          (⟨s, hs𝒮⟩ : ↥(𝒮 : Subgroup G))
      simpa using Subgroup.mem_subgroupOf.mp hconj
    · exact S.mul_mem (S.mul_mem hs hkS) (S.inv_mem hs)
  have htV : t ∉ E ⊓ S := fun ht => htE ht.1
  have hVPT : E ⊓ S ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    le_PT_of_normal_of_t_not_mem h hp hpt hτ hEnS htV
  by_cases hES : E ≤ S
  · have hEPT : E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
      fun e he => hVPT (Subgroup.mem_inf.mpr ⟨he, hES he⟩)
    exact false_of_elemAbelian_eight_le_PT h hEPT hEe hEc htE
  · have htS : t ∈ S := by
      have := h.center_ge (Subgroup.subset_closure (by simp) : t ∈ closure {t, (x₁ * x₂) ^ 2})
      exact this.1
    have ht𝒮 : t ∈ (𝒮 : Subgroup G) := h𝒮.le htS
    have h4 : 4 ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G)) :=
      four_le_card_inf_centralizer hE𝒮 hEn hEe hEc ht𝒮 (t_mul_self h.hyp)
    have hle_inf : E ⊓ centralizer ({t} : Set G) ≤ E ⊓ S := by
      intro x hx
      obtain ⟨hxE, hxc⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxE, ?_⟩
      have hx𝒮 : x ∈ (𝒮 : Subgroup G) := hE𝒮 hxE
      have hxin : x ∈ invCent t ⊓ (𝒮 : Subgroup G) := ⟨hxc, hx𝒮⟩
      rwa [hC] at hxin
    have h4' : 4 ≤ Nat.card ↥(E ⊓ S) := le_trans h4 (Subgroup.card_le_of_le hle_inf)
    have hcard_ltE : Nat.card ↥(E ⊓ S) < Nat.card E := by
      rcases lt_or_ge (Nat.card ↥(E ⊓ S)) (Nat.card E) with hlt | hge
      · exact hlt
      · exfalso
        have heq : E ⊓ S = E := Subgroup.eq_of_le_of_card_ge inf_le_left hge
        exact hES (by
          intro e he
          have hmem : e ∈ E ⊓ S := by rw [heq]; exact he
          exact hmem.2)
    have hcard_inf : Nat.card ↥(E ⊓ S) = 4 := by
      have hdvd : Nat.card ↥(E ⊓ S) ∣ 2 ^ 3 := by
        have hdd := Subgroup.card_dvd_of_le (H := E ⊓ S) (K := E) inf_le_left
        rw [hEc] at hdd
        simpa using hdd
      obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hk] at h4' hcard_ltE ⊢
      rw [hEc] at hcard_ltE
      have h4'' : (2 : ℕ) ^ 2 ≤ 2 ^ k := by simpa using h4'
      have hlt'' : 2 ^ k < (2 : ℕ) ^ 3 := by simpa using hcard_ltE
      have hk_ge : 2 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4''
      have hk_lt : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt''
      have hk_eq : k = 2 := by omega
      rw [hk_eq]; norm_num
    have hidx : (E ⊓ S).relIndex E = 2 := by
      have h := Subgroup.relIndex_mul_card (H := E ⊓ S) (K := E)
      rw [inf_eq_left.mpr inf_le_left, hcard_inf, hEc] at h
      omega
    exact false_of_inf_index_two h hp hpt h𝒮.le hC hE𝒮 hEn hEe hES hVPT hidx

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
