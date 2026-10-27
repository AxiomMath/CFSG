module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem l17_tlam_invol_comm (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * t = 1 ∧ lam * lam = 1 ∧ t * lam = lam * t := by
  obtain ⟨ht2, _, _, _, _, _, _⟩ := ctx13_relations hc
  obtain ⟨hlam2, _⟩ := ctx13_lam_facts hc
  exact ⟨by simpa [pow_two] using ht2, by simpa [pow_two] using hlam2,
    (l17_lam_comm hc).1.symm⟩

private theorem l17_inv_t (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (l17_tlam_invol_comm hc).1

private theorem l17_inv_lam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : lam⁻¹ = lam :=
  inv_eq_of_mul_eq_one_right (l17_tlam_invol_comm hc).2.1

theorem l17_card_tlam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure ({t, lam} : Set G)) = 4 := by
  obtain ⟨ht2, ht1, _, _, _, _, _⟩ := ctx13_relations hc
  obtain ⟨hlam2, _⟩ := ctx13_lam_facts hc
  have hcomm : t * lam = lam * t := (l17_lam_comm hc).1.symm
  have hnotmem := l17_not_mem_E0 hc
  have hlam1 : lam ≠ 1 := fun h1 => hnotmem.2.1 (h1 ▸ Subgroup.one_mem _)
  have hlamt : lam ≠ t := by
    intro h
    apply hnotmem.2.2
    rw [h, ← pow_two, ht2]
    exact Subgroup.one_mem _
  have hlamZ : lam ∉ zpowers t := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hord : orderOf t = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime ht2 ht1
    have hmod : t ^ (k % 2) = lam := by
      have h := zpow_mod_orderOf t k
      rw [hord] at h
      norm_num at h
      rw [hk] at h
      exact h
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · rw [hk0, zpow_zero] at hmod
      exact hlam1 hmod.symm
    · rw [hk1, zpow_one] at hmod
      exact hlamt hmod.symm
  exact card_closure_pair ht2 ht1 hlam2 hcomm hlamZ

theorem l17_E0_inf_tlam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxE0 t tau x₁ x₂ rho om ⊓ closure ({t, lam} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxE0, hxcl⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨ht2', hlam2', hcomm⟩ := l17_tlam_invol_comm hc
  rcases (mem_closure_pair_of_invol ht2' hlam2' hcomm).mp hxcl with hx | hx | hx | hx
  · subst x
    rfl
  · subst x
    exact absurd hxE0 (l17_not_mem_E0 hc).1
  · subst x
    exact absurd hxE0 (l17_not_mem_E0 hc).2.1
  · subst x
    exact absurd hxE0 (l17_not_mem_E0 hc).2.2

theorem l17_sylow_decomp (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ s ∈ 𝒮, ∃ e ∈ ctxE0 t tau x₁ x₂ rho om, ∃ b ∈ closure ({t, lam} : Set G), s = e * b := by
  have hB : closure ({t, lam} : Set G) ≤ 𝒮 := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (l17_T_le_sylow hc).1
    · exact (l17_T_le_sylow hc).2.2.2
  have hcard : Nat.card ↥(ctxE0 t tau x₁ x₂ rho om) *
      Nat.card ↥(closure ({t, lam} : Set G)) = Nat.card ↥𝒮 := by
    rw [l17_card_E0 hc, l17_card_tlam hc.toCtx13, l17_card_sylow hc]
    norm_num
  exact exists_mul_of_card_eq (l17_E0_le_sylow hc) hB (l17_E0_inf_tlam hc.toCtx13) hcard

theorem l17_sylow_cosets (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ s ∈ 𝒮, s ∈ ctxE0 t tau x₁ x₂ rho om ∨ t⁻¹ * s ∈ ctxE0 t tau x₁ x₂ rho om ∨
      lam⁻¹ * s ∈ ctxE0 t tau x₁ x₂ rho om ∨
      (t * lam)⁻¹ * s ∈ ctxE0 t tau x₁ x₂ rho om := by
  intro s hs
  obtain ⟨e, heE0, b, hbcl, rfl⟩ := l17_sylow_decomp hc s hs
  obtain ⟨ht2', hlam2', hcomm⟩ := l17_tlam_invol_comm hc.toCtx13
  rcases (mem_closure_pair_of_invol ht2' hlam2' hcomm).mp hbcl with hb | hb | hb | hb
  · left
    subst b
    simpa using heE0
  · right; left
    subst b
    have h1 : t * e * t⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om :=
      (l17_E0_normalized hc.toCtx13 e heE0).1
    simpa only [l17_inv_t hc.toCtx13, mul_assoc] using h1
  · right; right; left
    subst b
    have h2 : lam * e * lam⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om :=
      (l17_E0_normalized hc.toCtx13 e heE0).2
    simpa only [l17_inv_lam hc.toCtx13, mul_assoc] using h2
  · right; right; right
    subst b
    have h1 : lam * e * lam⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om :=
      (l17_E0_normalized hc.toCtx13 e heE0).2
    have h2 : t * (lam * e * lam⁻¹) * t⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om :=
      (l17_E0_normalized hc.toCtx13 (lam * e * lam⁻¹) h1).1
    have hinv : (t * lam)⁻¹ = t * lam := by
      rw [mul_inv_rev, l17_inv_t hc.toCtx13, l17_inv_lam hc.toCtx13, ← hcomm]
    have hkey : (t * lam)⁻¹ * (e * (t * lam)) = t * (lam * e * lam⁻¹) * t⁻¹ := by
      rw [hinv, l17_inv_t hc.toCtx13, l17_inv_lam hc.toCtx13]
      nth_rewrite 2 [hcomm]
      group
    rw [hkey]
    exact h2

theorem l17_cent_sylow_Y (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    𝒮 ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxE0 t tau x₁ x₂ rho om := by
  apply le_antisymm
  · intro s hs
    obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨e, he, b, hb, rfl⟩ := l17_sylow_decomp hc s hsS
    have heC : e ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      l17_E0_le_cent hc.toCtx13 he
    have hbC : b ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      have hmem : e⁻¹ * (e * b) ∈
          centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
        (centralizer _).mul_mem ((centralizer _).inv_mem heC) hsC
      simpa using hmem
    obtain ⟨ht2', hlam2', hcomm⟩ := l17_tlam_invol_comm hc.toCtx13
    rcases (mem_closure_pair_of_invol ht2' hlam2' hcomm).mp hb with hb | hb | hb | hb
    · subst b
      simpa using he
    · subst b
      exact absurd hbC (l17_not_cent_Y hc.toCtx13).1
    · subst b
      exact absurd hbC (l17_not_cent_Y hc.toCtx13).2.1
    · subst b
      exact absurd hbC (l17_not_cent_Y hc.toCtx13).2.2
  · exact le_inf (l17_E0_le_sylow hc) (l17_E0_le_cent hc.toCtx13)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
