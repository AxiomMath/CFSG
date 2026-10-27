module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18q
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18n
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma k18q2_conj_mem_centralizer {Y H : Subgroup G} {g k : G}
    (hYH : ∀ e ∈ H, ∀ y ∈ Y, e * y * e⁻¹ ∈ Y)
    (hg : g ∈ H) (hk : k ∈ centralizer (Y : Set G)) :
    g * k * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro y hy
  have hgy : g⁻¹ * y * g ∈ Y := by
    simpa using hYH g⁻¹ (H.inv_mem hg) y hy
  exact (calc (g * k * g⁻¹) * y = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by rw [← hk (g⁻¹ * y * g) hgy]
    _ = y * (g * k * g⁻¹) := by group).symm

theorem k18_exit_D (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {ℰ : Subgroup G}
    (hℰ : IsPGroup 2 ℰ) (h𝒮ℰ : 𝒮 ≤ ℰ)
    (hYℰ : ∀ e ∈ ℰ, ∀ y ∈ ctxYq t tau x₁ x₂ rho, e * y * e⁻¹ ∈ ctxYq t tau x₁ x₂ rho) :
    ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxCY t tau x₁ x₂ rho := by
  have hc13 := hc.toCtx13
  have hc18S := hc.toCtx18S
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (ctx13_relations hc13).1
  refine le_antisymm ?_ ?_
  · by_contra hle
    have hCD : ctxCY t tau x₁ x₂ rho ≤
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      le_inf ((l18_C_le_sylow hc18S).trans h𝒮ℰ) l18_C_le_cent
    have hne : ctxCY t tau x₁ x₂ rho ≠
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      fun h => hle (le_of_eq h.symm)
    have hlt : ctxCY t tau x₁ x₂ rho <
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      lt_of_le_of_ne hCD hne
    have hD2 : IsPGroup 2
        (ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) : Subgroup G) :=
      hℰ.to_le inf_le_left
    have htd : t ∈ ℰ := h𝒮ℰ (l18_T_le_sylow hc18S).1
    have htN : ∀ n ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G),
        t * n * t⁻¹ ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      intro n hn
      exact ⟨ℰ.mul_mem (ℰ.mul_mem htd hn.1) (ℰ.inv_mem htd),
        k18q2_conj_mem_centralizer hYℰ htd hn.2⟩
    have htC : ∀ e ∈ ctxCY t tau x₁ x₂ rho, t * e * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      fun e he => (l18_C_normalized hc13 e he).1
    obtain ⟨n, hnD, hnC, he⟩ := exists_fixed_coset hD2 hlt ht2 htN htC
    let e : G := n⁻¹ * (t * n * t⁻¹)
    let e' : G := t * e * t⁻¹
    have he'mem : e' ∈ ctxCY t tau x₁ x₂ rho := (l18_C_normalized hc13 e he).1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have htn : t * e' = n⁻¹ * t * n := by
      dsimp only [e', e]
      rw [htinv]
      calc t * (t * (n⁻¹ * (t * n * t)) * t) =
            (t * t) * (n⁻¹ * (t * n * t)) * t := by group
        _ = (n⁻¹ * (t * n * t)) * t := by rw [ht2, one_mul]
        _ = n⁻¹ * t * n * (t * t) := by group
        _ = n⁻¹ * t * n := by rw [ht2, mul_one]
    have ht2' : (t * e') * (t * e') = 1 := by
      rw [htn]
      calc (n⁻¹ * t * n) * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n := by group
        _ = 1 := by simp [ht2]
    obtain ⟨x₀, hx0𝒮, hx0eq⟩ := k18_F3A hc he'mem ht2'
    have heq2 : n⁻¹ * t * n = x₀ * t * x₀⁻¹ := by rw [← htn, hx0eq]
    have hcomm : (n * x₀) * t = t * (n * x₀) := by
      calc (n * x₀) * t = n * (x₀ * t) * x₀⁻¹ * x₀ := by group
        _ = n * (x₀ * t * x₀⁻¹) * x₀ := by group
        _ = n * (n⁻¹ * t * n) * x₀ := by rw [← heq2]
        _ = t * (n * x₀) := by group
    have hnx0cent : n * x₀ ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hnx0ℰ : n * x₀ ∈ ℰ := ℰ.mul_mem hnD.1 (h𝒮ℰ hx0𝒮)
    have hnx0S : n * x₀ ∈ S := by
      rw [← c17_cent_eq hc13.toCtx11.toCtx10 hℰ
        ((l18_le_sylow hc18S).2.2.1.trans h𝒮ℰ)]
      exact ⟨hnx0ℰ, hnx0cent⟩
    have hn𝒮 : n ∈ 𝒮 := by
      have hnx0𝒮 : n * x₀ ∈ 𝒮 := (l18_le_sylow hc18S).2.2.1 hnx0S
      have hn_eq : n = (n * x₀) * x₀⁻¹ := by group
      rw [hn_eq]
      exact 𝒮.mul_mem hnx0𝒮 (𝒮.inv_mem hx0𝒮)
    have hnC' : n ∈ ctxCY t tau x₁ x₂ rho := by
      rw [← l18_cent_sylow_Y hc18S]
      exact ⟨hn𝒮, hnD.2⟩
    exact hnC hnC'
  · exact le_inf ((l18_C_le_sylow hc18S).trans h𝒮ℰ) l18_C_le_cent

theorem k18_C_sylow (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    IsSylowIn 2 (ctxCY t tau x₁ x₂ rho)
      (centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) := by
  have hc18S := hc.toCtx18S
  have h𝒮N : 𝒮 ≤ normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro k hk
    exact mem_normalizer_of_conj_le (A := ctxYq t tau x₁ x₂ rho)
      ((k18_sylow_normalizes hc18S).2 k hk)
  have h𝒮2 : IsPGroup 2 𝒮 := hc.sylow.2.1
  obtain ⟨ℰ, hℰsylow, h𝒮ℰ⟩ := exists_isSylowIn_of_le
    (K := normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) (U := 𝒮) h𝒮N h𝒮2
  have hℰ2 : IsPGroup 2 ℰ := hℰsylow.2.1
  have hYℰ : ∀ e ∈ ℰ, ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      e * y * e⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    intro e he y hy
    exact (Subgroup.mem_normalizer_iff.mp (hℰsylow.1 he) y).mp hy
  have hD := k18_exit_D hc hℰ2 h𝒮ℰ hYℰ
  have hres := isSylowIn_inf_centralizer_of_normalizer hℰsylow
  simpa [hD] using hres

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
