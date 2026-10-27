module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem e17_gamma (h : L41GPh16 t L S x₁ x₂ lam rho)
    (hab : ∀ a ∈ l41Q1 t x₁ x₂ rho, ∀ b ∈ l41Q1 t x₁ x₂ rho, a * b = b * a)
    (hq : ∃ a ∈ l41Q1 t x₁ x₂ rho, a ^ 4 ≠ 1) :
    ∃ γ ∈ l41Q1 t x₁ x₂ rho, γ ^ 4 ≠ 1 ∧ ∃ E : Subgroup G,
      E ≤ centralizer ({lam * t} : Set G) ∧ IsPGroup 2 E ∧ 32 ≤ Nat.card E ∧ γ ∈ E ∧
        ∀ e ∈ E, e * γ = γ * e := by
  let u : G := lam * t
  let C : Subgroup G := l41Q1 t x₁ x₂ rho ⊓ centralizer ({u} : Set G)
  have hu2 : u * u = 1 := by simpa [u] using m11_lamt_sq h.toL41GPh5
  have huρ : u * rho * u⁻¹ = rho⁻¹ := by simpa [u] using m11_lamt_rho h.toL41GPh5
  have hρ3 : rho ^ 3 = 1 := n4_rho_cube h.toCtx0
  have hX : IsPGroup 2 (l41Q1 t x₁ x₂ rho) := h.q1facts.V1_pGroup.to_le le_sup_left
  have hρX : ∀ x ∈ l41Q1 t x₁ x₂ rho, rho * x * rho⁻¹ ∈ l41Q1 t x₁ x₂ rho :=
    fun x hx => z18_conj_Q1 h.toL41GPh15 (z18_rho_mem_M h.toL41GPh14) hx
  have huX : ∀ x ∈ l41Q1 t x₁ x₂ rho, u * x * u⁻¹ ∈ l41Q1 t x₁ x₂ rho := by
    intro x hx
    have hM : u ∈ l41M t x₁ x₂ rho := by
      show lam * t ∈ l41M t x₁ x₂ rho
      exact Subgroup.mul_mem _ (z18_lam_mem_M h.toL41GPh14) (z18_t_mem_M t x₁ x₂ rho)
    exact z18_conj_Q1 h.toL41GPh15 hM hx
  have hfix : ∀ x ∈ l41Q1 t x₁ x₂ rho, rho * x = x * rho → x = 1 :=
    fun x hx hc => z18_cent_Q1_rho h.toL41GPh15 hx hc
  have hle := e17_card_le_sq hX hab hρX huX hρ3 hu2 huρ hfix
  have hC16 : 16 ≤ Nat.card C := by
    have hsq : 2 ^ 8 ≤ Nat.card C * Nat.card C := by
      rw [← h.q1facts.card_Q1]
      exact hle
    have hsq' : (16 : ℕ) * 16 ≤ Nat.card C * Nat.card C := by simpa using hsq
    by_contra hlt
    have h1 : Nat.card C ≤ 15 := by omega
    have h2 : Nat.card C * Nat.card C ≤ 15 * 15 := Nat.mul_le_mul h1 h1
    omega
  obtain ⟨a, haQ1, ha4⟩ := hq
  obtain ⟨c1, hc1Q, c2, hc2Q, hc1u, hc2u, hsplit⟩ :=
    e17_fpf_split hX hab hρX huX hρ3 hu2 huρ hfix a haQ1
  have hdQ : rho * c2 * rho⁻¹ ∈ l41Q1 t x₁ x₂ rho := hρX c2 hc2Q
  have hcomm1d : Commute c1 (rho * c2 * rho⁻¹) := hab c1 hc1Q _ hdQ
  have ha_pow : a ^ 4 = c1 ^ 4 * (rho * c2 * rho⁻¹) ^ 4 := by
    rw [hsplit]
    exact hcomm1d.mul_pow 4
  have hconj : (rho * c2 * rho⁻¹) ^ 4 = rho * c2 ^ 4 * rho⁻¹ := conj_pow
  have huV1 : u ∈ l41V1 t x₁ x₂ rho lam := by
    show lam * t ∈ l41V1 t x₁ x₂ rho lam
    exact Subgroup.mem_sup_right (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  have hCpg : IsPGroup 2 C := hX.to_le inf_le_left
  have hzu : IsPGroup 2 (zpowers u : Subgroup G) :=
    h.q1facts.V1_pGroup.to_le (Subgroup.zpowers_le.mpr huV1)
  have hu_centC : u ∈ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  have hnorm : (zpowers u : Subgroup G) ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hu_centC)
  let E : Subgroup G := C ⊔ zpowers u
  have hEpg : IsPGroup 2 E := hCpg.to_sup_of_normal_left' hzu hnorm
  have hE_cent : E ≤ centralizer ({lam * t} : Set G) := by
    show C ⊔ zpowers u ≤ _
    refine sup_le inf_le_right ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hlam1 : lam ≠ 1 := by
    intro h1
    have := h.wreath.ord_lam
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨g, hg⟩ := h.fusion.conj_tu lam (Subgroup.subset_closure (by simp))
    (n4_lam_sq h.toCtx0) hlam1
  have htl : t * lam = lam * t :=
    m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  have hgt : g * t * g⁻¹ = u := by
    rw [hg, htl]
  have hu_not_Q1 : u ∉ l41Q1 t x₁ x₂ rho :=
    fun huQ => z18_tG_Q1 h g⁻¹ huQ (by simpa using hgt)
  have hu_not_C : u ∉ C := fun hc => hu_not_Q1 (Subgroup.mem_inf.mp hc).1
  have hCE : C ≤ E := le_sup_left
  have hEcomm_c1 : ∀ e ∈ E, e * c1 = c1 * e := by
    have hEc1 : E ≤ centralizer ({c1} : Set G) := by
      show C ⊔ zpowers u ≤ _
      refine sup_le ?_ ?_
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hab c (Subgroup.mem_inf.mp hc).1 c1 hc1Q
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hc1u
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEc1 he)
  have hEcomm_c2 : ∀ e ∈ E, e * c2 = c2 * e := by
    have hEc2 : E ≤ centralizer ({c2} : Set G) := by
      show C ⊔ zpowers u ≤ _
      refine sup_le ?_ ?_
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hab c (Subgroup.mem_inf.mp hc).1 c2 hc2Q
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hc2u
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEc2 he)
  have hc1C : c1 ∈ C :=
    Subgroup.mem_inf.mpr ⟨hc1Q, Subgroup.mem_centralizer_singleton_iff.mpr hc1u.symm⟩
  have hc2C : c2 ∈ C :=
    Subgroup.mem_inf.mpr ⟨hc2Q, Subgroup.mem_centralizer_singleton_iff.mpr hc2u.symm⟩
  have hc1E : c1 ∈ E := Subgroup.mem_sup_left hc1C
  have hc2E : c2 ∈ E := Subgroup.mem_sup_left hc2C
  have h32 : 32 ≤ Nat.card E := by
    have hCElt : C < E := by
      refine lt_of_le_of_ne hCE ?_
      intro hCEq
      exact hu_not_C (hCEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    have hcardlt : Nat.card C < Nat.card E := Subgroup.card_lt_of_lt hCElt
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hCE
    have hm2 : 2 ≤ m := by
      rcases m with _ | _ | m
      · simp at hm
        omega
      · simp at hm
        omega
      · omega
    have hmul : 2 * Nat.card C ≤ Nat.card E := by
      rw [hm, mul_comm (Nat.card C) m]
      exact Nat.mul_le_mul_right (Nat.card C) hm2
    omega
  by_cases hc1p : c1 ^ 4 = 1
  · have hc2p : c2 ^ 4 ≠ 1 := by
      intro hc2eq
      apply ha4
      rw [ha_pow, hconj, hc1p, hc2eq]
      group
    exact ⟨c2, hc2Q, hc2p, E, hE_cent, hEpg, h32, hc2E, hEcomm_c2⟩
  · exact ⟨c1, hc1Q, hc1p, E, hE_cent, hEpg, h32, hc1E, hEcomm_c1⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
