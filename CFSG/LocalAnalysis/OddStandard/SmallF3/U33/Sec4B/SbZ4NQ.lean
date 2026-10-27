module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Exp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NM

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mem_normalizer_of_normalIn' {H Y : Subgroup G} {g : G}
    (hN : NormalIn Y H) (hg : g ∈ H) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hN.2 g hg h hh, fun hh => ?_⟩
  have hinv : g⁻¹ ∈ H := H.inv_mem hg
  have hconj := hN.2 g⁻¹ hinv (g * h * g⁻¹) hh
  have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
  rwa [heq] at hconj

private lemma conj_mem_centralizer' {H Y : Subgroup G} {g k : G}
    (hN : NormalIn Y H) (hg : g ∈ H) (hk : k ∈ centralizer (Y : Set G)) :
    g * k * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro y hy
  have hgN := mem_normalizer_of_normalIn' hN hg
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).inv_mem hgN
  have hgy : g⁻¹ * y * g ∈ Y := by
    have h := (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
    simpa using h
  exact (calc (g * k * g⁻¹) * y = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by rw [← hk (g⁻¹ * y * g) hgy]
    _ = y * (g * k * g⁻¹) := by group).symm


namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem exit_D {ℰ : Subgroup G} (hℰ : IsPGroup 2 ℰ)
    (hVℰ : ctxVN t tau x₁ x₂ lam rho ≤ ℰ) :
    ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxE0N t tau x₁ x₂ rho := by
  have ht2 : t * t = 1 := hw.t_mul_self
  have hE0cent : ctxE0N t tau x₁ x₂ rho ≤
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    fun e he => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hw.E0_le_cent_Y e he a ha).symm
  refine le_antisymm ?_ ?_
  · by_contra hle
    have hE0D : ctxE0N t tau x₁ x₂ rho ≤
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      le_inf (hw.E0_le_ctxVN.trans hVℰ) hE0cent
    have hne : ctxE0N t tau x₁ x₂ rho ≠
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      fun h => hle (le_of_eq h.symm)
    have hlt : ctxE0N t tau x₁ x₂ rho <
        ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      lt_of_le_of_ne hE0D hne
    have hD2 : IsPGroup 2
        (ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) : Subgroup G) :=
      hℰ.to_le inf_le_left
    have htd : t ∈ ℰ := hVℰ (hw.E8_le_ctxVN (Subgroup.subset_closure (by simp)))
    have htN : ∀ n ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G),
        t * n * t⁻¹ ∈ ℰ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      intro n hn
      exact ⟨ℰ.mul_mem (ℰ.mul_mem htd hn.1) (ℰ.inv_mem htd),
        conj_mem_centralizer' (hw.Y_normal_all ℰ hℰ hVℰ) htd hn.2⟩
    have htE : ∀ e ∈ ctxE0N t tau x₁ x₂ rho, t * e * t⁻¹ ∈ ctxE0N t tau x₁ x₂ rho :=
      fun e he => hw.t_conj_ctxE0N e he
    obtain ⟨n, hnD, hnE0, he⟩ := S4B.exists_fixed_coset hD2 hlt ht2 htN htE
    let e : G := n⁻¹ * (t * n * t⁻¹)
    let e' : G := t * e * t⁻¹
    have he'mem : e' ∈ ctxE0N t tau x₁ x₂ rho := hw.t_conj_ctxE0N e he
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
    obtain ⟨x₀, hx0E0, hx0eq⟩ := hw.F3 e' he'mem ht2' ⟨n⁻¹, by rw [htn]; group⟩
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
      ℰ.mul_mem hnD.1 (hVℰ (hw.E0_le_ctxVN hx0E0))
    have hnx0S : n * x₀ ∈ S := by
      rw [← S4B.c17_cent_eq hw.toCtx10 hℰ (hw.S_le_ctxVN.trans hVℰ)]
      exact ⟨hnx0ℰ, hnx0cent⟩
    have hnV : n ∈ ctxVN t tau x₁ x₂ lam rho := by
      have hnx0V : n * x₀ ∈ ctxVN t tau x₁ x₂ lam rho := hw.S_le_ctxVN hnx0S
      have hx0V : x₀ ∈ ctxVN t tau x₁ x₂ lam rho := hw.E0_le_ctxVN hx0E0
      have hn_eq : n = (n * x₀) * x₀⁻¹ := by group
      rw [hn_eq]
      exact Subgroup.mul_mem _ hnx0V (Subgroup.inv_mem _ hx0V)
    have hnE0' : n ∈ ctxE0N t tau x₁ x₂ rho := by
      rw [← hw.cent_Y_ctxVN]
      exact ⟨hnV, hnD.2⟩
    exact hnE0 hnE0'
  · exact le_inf (hw.E0_le_ctxVN.trans hVℰ) hE0cent

theorem exit_normal {ℰ : Subgroup G} (hℰ : IsPGroup 2 ℰ)
    (hVℰ : ctxVN t tau x₁ x₂ lam rho ≤ ℰ) : NormalIn (ctxE0N t tau x₁ x₂ rho) ℰ := by
  have hD := hw.exit_D hℰ hVℰ
  rw [← hD]
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  exact ⟨ℰ.mul_mem (ℰ.mul_mem hg hk.1) (ℰ.inv_mem hg),
    conj_mem_centralizer' (hw.Y_normal_all ℰ hℰ hVℰ) hg hk.2⟩

theorem exit_hexp {ℰ : Subgroup G} (hℰ : IsPGroup 2 ℰ)
    (hVℰ : ctxVN t tau x₁ x₂ lam rho ≤ ℰ) :
    ∀ x ∈ ℰ, x ^ 4 ∈ ctxE0N t tau x₁ x₂ rho := by
  intro x hx
  rw [← hw.exit_D hℰ hVℰ]
  refine ⟨ℰ.pow_mem hx 4, ?_⟩
  change x ^ 4 ∈ Subgroup.centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  obtain ⟨k, hk⟩ := hℰ ⟨x, hx⟩
  have hk' : x ^ (2 ^ k) = 1 := by
    have hval := congrArg (Subtype.val) hk
    simpa using hval
  have h4 := S4B.pow_four_centralizes (hw.Y_isElemAbelian) (hw.card_Y)
    (mem_normalizer_of_normalIn' (hw.Y_normal_all ℰ hℰ hVℰ) hx) ⟨k, hk'⟩
  intro y hy
  have hy' := h4 y hy
  calc y * x ^ 4 = (x ^ 4 * y * (x ^ 4)⁻¹) * x ^ 4 := by rw [hy']
    _ = x ^ 4 * y := by group

theorem exit_hC {ℰ : Subgroup G} (hℰ : IsPGroup 2 ℰ)
    (hVℰ : ctxVN t tau x₁ x₂ lam rho ≤ ℰ) :
    ∀ x ∈ ℰ, x * t * x⁻¹ * t⁻¹ ∈ ctxE0N t tau x₁ x₂ rho →
      x ∈ ctxE0N t tau x₁ x₂ rho ∨ t⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho ∨
        lam⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho ∨ (t * lam)⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho := by
  intro x hx he
  have ht2 : t * t = 1 := hw.t_mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let e : G := x * t * x⁻¹ * t⁻¹
  let e' : G := t * e * t⁻¹
  have he'mem : e' ∈ ctxE0N t tau x₁ x₂ rho := hw.t_conj_ctxE0N e he
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
  obtain ⟨x₀, hx0E0, hx0eq⟩ := hw.F3 e' he'mem ht2' ⟨x, hte'.symm⟩
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
    ℰ.mul_mem (ℰ.inv_mem (hVℰ (hw.E0_le_ctxVN hx0E0))) hx
  have hx0xS : x₀⁻¹ * x ∈ S := by
    rw [← S4B.c17_cent_eq hw.toCtx10 hℰ (hw.S_le_ctxVN.trans hVℰ)]
    exact ⟨hx0xℰ, hcent⟩
  have hxV : x ∈ ctxVN t tau x₁ x₂ lam rho := by
    have hx0xV : x₀⁻¹ * x ∈ ctxVN t tau x₁ x₂ lam rho := hw.S_le_ctxVN hx0xS
    have hx0V : x₀ ∈ ctxVN t tau x₁ x₂ lam rho := hw.E0_le_ctxVN hx0E0
    have hx_eq : x = x₀ * (x₀⁻¹ * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem _ hx0V hx0xV
  exact hw.vn_cosets x hxV

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
