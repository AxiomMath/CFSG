module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem l18_tlam_invol_comm (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * t = 1 ∧ lam * lam = 1 ∧ t * lam = lam * t := by
  obtain ⟨ht2, _, _, _, _, _, _⟩ := ctx13_relations hc
  obtain ⟨hlam2, _⟩ := ctx13_lam_facts hc
  exact ⟨by simpa [pow_two] using ht2, by simpa [pow_two] using hlam2,
    (l17_lam_comm hc).1.symm⟩

private theorem l18_inv_t (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (l18_tlam_invol_comm hc).1

private theorem l18_inv_lam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : lam⁻¹ = lam :=
  inv_eq_of_mul_eq_one_right (l18_tlam_invol_comm hc).2.1

theorem l18_C_le_cent :
    ctxCY t tau x₁ x₂ rho ≤ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
  inf_le_right

theorem l18_C_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxCY t tau x₁ x₂ rho ≤ 𝒮 :=
  (l18_C_le_OK hc.toCtx13).trans (l18_OK_le_sylow hc)

theorem l18_C_normalized (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ e ∈ ctxCY t tau x₁ x₂ rho,
      t * e * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho ∧ lam * e * lam⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
  fun e he => ⟨(l18_C_normal hc).2 t (l17_mem_K hc).1 e he,
    (l18_C_normal hc).2 lam (l17_mem_K hc).2.2.2.1 e he⟩

theorem l18_C_inf_tlam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxCY t tau x₁ x₂ rho ⊓ closure ({t, lam} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxC, hxcl⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨ht2', hlam2', hcomm⟩ := l18_tlam_invol_comm hc
  rcases (mem_closure_pair_of_invol ht2' hlam2' hcomm).mp hxcl with hx | hx | hx | hx
  · subst x
    rfl
  · subst x
    exact absurd hxC (l18_not_mem_C hc).1
  · subst x
    exact absurd hxC (l18_not_mem_C hc).2.1
  · subst x
    exact absurd hxC (l18_not_mem_C hc).2.2

theorem l18_sylow_decomp (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ s ∈ 𝒮, ∃ e ∈ ctxCY t tau x₁ x₂ rho, ∃ b ∈ closure ({t, lam} : Set G), s = e * b := by
  have hB : closure ({t, lam} : Set G) ≤ 𝒮 := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (l18_T_le_sylow hc.toCtx18S).1
    · exact (l18_T_le_sylow hc.toCtx18S).2.2.2
  have hcard : Nat.card ↥(ctxCY t tau x₁ x₂ rho) *
      Nat.card ↥(closure ({t, lam} : Set G)) = Nat.card ↥𝒮 := by
    rw [hc.card_C, l17_card_tlam hc.toCtx13, l18_card_sylow hc.toCtx18S]
    norm_num
  exact exists_mul_of_card_eq (l18_C_le_sylow hc.toCtx18S) hB (l18_C_inf_tlam hc.toCtx13) hcard

theorem l18_sylow_cosets (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ s ∈ 𝒮, s ∈ ctxCY t tau x₁ x₂ rho ∨ t⁻¹ * s ∈ ctxCY t tau x₁ x₂ rho ∨
      lam⁻¹ * s ∈ ctxCY t tau x₁ x₂ rho ∨
      (t * lam)⁻¹ * s ∈ ctxCY t tau x₁ x₂ rho := by
  intro s hs
  obtain ⟨e, heC, b, hbcl, rfl⟩ := l18_sylow_decomp hc s hs
  obtain ⟨ht2', hlam2', hcomm⟩ := l18_tlam_invol_comm hc.toCtx13
  rcases (mem_closure_pair_of_invol ht2' hlam2' hcomm).mp hbcl with hb | hb | hb | hb
  · left
    subst b
    simpa using heC
  · right; left
    subst b
    have h1 : t * e * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      (l18_C_normalized hc.toCtx13 e heC).1
    simpa only [l18_inv_t hc.toCtx13, mul_assoc] using h1
  · right; right; left
    subst b
    have h2 : lam * e * lam⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      (l18_C_normalized hc.toCtx13 e heC).2
    simpa only [l18_inv_lam hc.toCtx13, mul_assoc] using h2
  · right; right; right
    subst b
    have h1 : lam * e * lam⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      (l18_C_normalized hc.toCtx13 e heC).2
    have h2 : t * (lam * e * lam⁻¹) * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      (l18_C_normalized hc.toCtx13 (lam * e * lam⁻¹) h1).1
    have hinv : (t * lam)⁻¹ = t * lam := by
      rw [mul_inv_rev, l18_inv_t hc.toCtx13, l18_inv_lam hc.toCtx13, ← hcomm]
    have hkey : (t * lam)⁻¹ * (e * (t * lam)) = t * (lam * e * lam⁻¹) * t⁻¹ := by
      rw [hinv, l18_inv_t hc.toCtx13, l18_inv_lam hc.toCtx13]
      nth_rewrite 2 [hcomm]
      group
    rw [hkey]
    exact h2

theorem l18_cent_sylow_Y (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    𝒮 ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxCY t tau x₁ x₂ rho := by
  apply le_antisymm
  · intro s hs
    obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
    exact Subgroup.mem_inf.mpr ⟨hc.sylow.1 hsS, hsC⟩
  · exact le_inf (l18_C_le_sylow hc) l18_C_le_cent

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
