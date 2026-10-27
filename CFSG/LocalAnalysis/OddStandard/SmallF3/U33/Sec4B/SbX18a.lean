module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbU18c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Exp

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma mem_normalizer_of_normalIn {G : Type} [Group G] {H Y : Subgroup G} {g : G}
    (hN : NormalIn Y H) (hg : g ∈ H) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hN.2 g hg h hh, fun hh => ?_⟩
  have hinv : g⁻¹ ∈ H := H.inv_mem hg
  have hconj := hN.2 g⁻¹ hinv (g * h * g⁻¹) hh
  have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
  rwa [heq] at hconj

private lemma conj_mem_centralizer {G : Type} [Group G] {H Y : Subgroup G} {g k : G}
    (hN : NormalIn Y H) (hg : g ∈ H) (hk : k ∈ centralizer (Y : Set G)) :
    g * k * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro y hy
  have hgN := mem_normalizer_of_normalIn hN hg
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).inv_mem hgN
  have hgy : g⁻¹ * y * g ∈ Y := by
    have h := (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
    simpa using h
  exact (calc (g * k * g⁻¹) * y = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by rw [← hk (g⁻¹ * y * g) hgy]
    _ = y * (g * k * g⁻¹) := by group).symm

theorem l18_exit_D (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {ℰ : Subgroup G}
    (hℰ : IsPGroup 2 ℰ) (h𝒮ℰ : 𝒮 ≤ ℰ) :
    ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxCY t tau x₁ x₂ rho := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  refine le_antisymm ?_ ?_
  · by_contra hle
    have hE0D : ctxCY t tau x₁ x₂ rho ≤
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      le_inf ((l18_C_le_sylow hc.toCtx18S).trans h𝒮ℰ) l18_C_le_cent
    have hne : ctxCY t tau x₁ x₂ rho ≠
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      fun h => hle (le_of_eq h.symm)
    have hlt : ctxCY t tau x₁ x₂ rho <
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      lt_of_le_of_ne hE0D hne
    have hD2 : IsPGroup 2
        (ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) : Subgroup G) :=
      hℰ.to_le inf_le_left
    have htd : t ∈ ℰ := h𝒮ℰ (l18_T_le_sylow hc.toCtx18S).1
    have htN : ∀ n ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G),
        t * n * t⁻¹ ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      intro n hn
      exact ⟨ℰ.mul_mem (ℰ.mul_mem htd hn.1) (ℰ.inv_mem htd),
        conj_mem_centralizer (l18_Y_normal_all hc ℰ hℰ h𝒮ℰ) htd hn.2⟩
    have htE : ∀ e ∈ ctxCY t tau x₁ x₂ rho, t * e * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
      fun e he => (l18_C_normalized hc.toCtx13 e he).1
    obtain ⟨n, hnD, hnE0, he⟩ := exists_fixed_coset hD2 hlt ht2 htN htE
    let e : G := n⁻¹ * (t * n * t⁻¹)
    let e' : G := t * e * t⁻¹
    have he'mem : e' ∈ ctxCY t tau x₁ x₂ rho := (l18_C_normalized hc.toCtx13 e he).1
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
    obtain ⟨x₀, hx0E0, hx0eq⟩ := l18_F3 hc he'mem ht2'
    have heq2 : n⁻¹ * t * n = x₀ * t * x₀⁻¹ := by rw [← htn, hx0eq]
    have hcomm : (n * x₀) * t = t * (n * x₀) := by
      calc (n * x₀) * t = n * (x₀ * t) * x₀⁻¹ * x₀ := by group
        _ = n * (x₀ * t * x₀⁻¹) * x₀ := by group
        _ = n * (n⁻¹ * t * n) * x₀ := by rw [← heq2]
        _ = t * (n * x₀) := by group
    have hnx0cent : n * x₀ ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hnx0ℰ : n * x₀ ∈ ℰ :=
      ℰ.mul_mem hnD.1 (h𝒮ℰ (l18_C_le_sylow hc.toCtx18S hx0E0))
    have hnx0S : n * x₀ ∈ S := by
      rw [← c17_cent_eq hc.toCtx13.toCtx11.toCtx10 hℰ
        ((l18_le_sylow hc.toCtx18S).2.2.1.trans h𝒮ℰ)]
      exact ⟨hnx0ℰ, hnx0cent⟩
    have hn𝒮 : n ∈ 𝒮 := by
      have hnx0𝒮 : n * x₀ ∈ 𝒮 := (l18_le_sylow hc.toCtx18S).2.2.1 hnx0S
      have hx0𝒮 : x₀ ∈ 𝒮 := l18_C_le_sylow hc.toCtx18S hx0E0
      have hn_eq : n = (n * x₀) * x₀⁻¹ := by group
      rw [hn_eq]
      exact 𝒮.mul_mem hnx0𝒮 (𝒮.inv_mem hx0𝒮)
    have hnE0' : n ∈ ctxCY t tau x₁ x₂ rho := by
      rw [← l18_cent_sylow_Y hc.toCtx18S]
      exact ⟨hn𝒮, hnD.2⟩
    exact hnE0 hnE0'
  · exact le_inf ((l18_C_le_sylow hc.toCtx18S).trans h𝒮ℰ) l18_C_le_cent

theorem l18_exit_normal (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {ℰ : Subgroup G}
    (hℰ : IsPGroup 2 ℰ) (h𝒮ℰ : 𝒮 ≤ ℰ) : NormalIn (ctxCY t tau x₁ x₂ rho) ℰ := by
  have hD := l18_exit_D hc hℰ h𝒮ℰ
  rw [← hD]
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  exact ⟨ℰ.mul_mem (ℰ.mul_mem hg hk.1) (ℰ.inv_mem hg),
    conj_mem_centralizer (l18_Y_normal_all hc ℰ hℰ h𝒮ℰ) hg hk.2⟩

theorem l18_exit_hexp (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {ℰ : Subgroup G}
    (hℰ : IsPGroup 2 ℰ) (h𝒮ℰ : 𝒮 ≤ ℰ) :
    ∀ x ∈ ℰ, x ^ 4 ∈ ctxCY t tau x₁ x₂ rho := by
  intro x hx
  rw [← l18_exit_D hc hℰ h𝒮ℰ]
  refine ⟨ℰ.pow_mem hx 4, ?_⟩
  change x ^ 4 ∈ Subgroup.centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  obtain ⟨k, hk⟩ := hℰ ⟨x, hx⟩
  have hk' : x ^ (2 ^ k) = 1 := by
    have hval := congrArg (Subtype.val) hk
    simpa using hval
  have h4 := pow_four_centralizes (l17_Y_elem hc.toCtx13) (l17_card_Y hc.toCtx13)
    (mem_normalizer_of_normalIn (l18_Y_normal_all hc ℰ hℰ h𝒮ℰ) hx) ⟨k, hk'⟩
  intro y hy
  have hy' := h4 y hy
  calc y * x ^ 4 = (x ^ 4 * y * (x ^ 4)⁻¹) * x ^ 4 := by rw [hy']
    _ = x ^ 4 * y := by group

theorem l18_exit_hC (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {ℰ : Subgroup G}
    (hℰ : IsPGroup 2 ℰ) (h𝒮ℰ : 𝒮 ≤ ℰ) :
    ∀ x ∈ ℰ, x * t * x⁻¹ * t⁻¹ ∈ ctxCY t tau x₁ x₂ rho →
      x ∈ ctxCY t tau x₁ x₂ rho ∨ t⁻¹ * x ∈ ctxCY t tau x₁ x₂ rho ∨
        lam⁻¹ * x ∈ ctxCY t tau x₁ x₂ rho ∨ (t * lam)⁻¹ * x ∈ ctxCY t tau x₁ x₂ rho := by
  intro x hx he
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let e : G := x * t * x⁻¹ * t⁻¹
  let e' : G := t * e * t⁻¹
  have he'mem : e' ∈ ctxCY t tau x₁ x₂ rho := (l18_C_normalized hc.toCtx13 e he).1
  have hte' : t * e' = x * t * x⁻¹ := by
    dsimp only [e', e]
    rw [htinv]
    calc t * (t * (x * t * x⁻¹ * t) * t) =
          (t * t) * (x * t * x⁻¹ * t) * t := by group
      _ = (x * t * x⁻¹ * t) * t := by rw [ht2, one_mul]
      _ = x * t * x⁻¹ * (t * t) := by group
      _ = x * t * x⁻¹ := by rw [ht2, mul_one]
  have ht2' : (t * e') * (t * e') = 1 := by
    rw [hte']
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by simp [ht2]
  obtain ⟨x₀, hx0E0, hx0eq⟩ := l18_F3 hc he'mem ht2'
  have heq2 : x * t * x⁻¹ = x₀ * t * x₀⁻¹ := by rw [← hte', hx0eq]
  have hconj : (x₀⁻¹ * x) * t * (x₀⁻¹ * x)⁻¹ = t := by
    calc (x₀⁻¹ * x) * t * (x₀⁻¹ * x)⁻¹ = x₀⁻¹ * (x * t * x⁻¹) * x₀ := by group
      _ = x₀⁻¹ * (x₀ * t * x₀⁻¹) * x₀ := by rw [heq2]
      _ = t := by group
  have hcomm : (x₀⁻¹ * x) * t = t * (x₀⁻¹ * x) := by
    calc (x₀⁻¹ * x) * t =
          ((x₀⁻¹ * x) * t * (x₀⁻¹ * x)⁻¹) * (x₀⁻¹ * x) := by group
      _ = t * (x₀⁻¹ * x) := by rw [hconj]
  have hcent : x₀⁻¹ * x ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hx0xℰ : x₀⁻¹ * x ∈ ℰ :=
    ℰ.mul_mem (ℰ.inv_mem (h𝒮ℰ (l18_C_le_sylow hc.toCtx18S hx0E0))) hx
  have hx0xS : x₀⁻¹ * x ∈ S := by
    rw [← c17_cent_eq hc.toCtx13.toCtx11.toCtx10 hℰ
      ((l18_le_sylow hc.toCtx18S).2.2.1.trans h𝒮ℰ)]
    exact ⟨hx0xℰ, hcent⟩
  have hx𝒮 : x ∈ 𝒮 := by
    have hx0x𝒮 : x₀⁻¹ * x ∈ 𝒮 := (l18_le_sylow hc.toCtx18S).2.2.1 hx0xS
    have hx0𝒮 : x₀ ∈ 𝒮 := l18_C_le_sylow hc.toCtx18S hx0E0
    have hx_eq : x = x₀ * (x₀⁻¹ * x) := by group
    rw [hx_eq]
    exact 𝒮.mul_mem hx0𝒮 hx0x𝒮
  exact l18_sylow_cosets hc x hx𝒮

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
