module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13dI4a_relIndex (h : Q13Om t L S x₁ x₂ lam rho tau om)
    {𝒮 : Subgroup G} (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮)
    (hcard : Nat.card ↥𝒮 = 2 ^ 11) :
    (ctxU t tau x₁ x₂ lam).relIndex 𝒮 = 2 := by
  have hrelcard := Subgroup.relIndex_mul_card (H := ctxU t tau x₁ x₂ lam) (K := 𝒮)
  rw [inf_eq_left.mpr hU] at hrelcard
  have hUcard : Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 := q13b_card_U h
  have h1 : (ctxU t tau x₁ x₂ lam).relIndex 𝒮 * Nat.card ↥(ctxU t tau x₁ x₂ lam) =
      2 * Nat.card ↥(ctxU t tau x₁ x₂ lam) := by
    rw [hrelcard, hcard, hUcard]
    norm_num
  have hpos : 0 < Nat.card ↥(ctxU t tau x₁ x₂ lam) := by
    rw [hUcard]; norm_num
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem q13d_I_R2_card (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hU :
      ctxU t tau x₁ x₂ lam ≤ 𝒮)
    (hcard : Nat.card ↥𝒮 = 2 ^ 11) :
    Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) = 2 ^ 8 := by
  have hlow : 2 ^ 8 ≤
      Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) := by
    have h := q13d_card_le_cent_N h hB h𝒮 hU
    rw [hcard] at h
    norm_num at h ⊢
    omega
  have hhigh : Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) ≤
      2 ^ 8 := by
    have h2 := card_le_two_mul_card_inf (A := 𝒮)
      (B := 𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))
      (Q := ctxU t tau x₁ x₂ lam) inf_le_left (q13dI4a_relIndex h hU hcard)
    have hRinf : (𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) ⊓
        ctxU t tau x₁ x₂ lam =
        ctxU t tau x₁ x₂ lam ⊓
          centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
      ext y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨-, hyC⟩, hyU⟩; exact ⟨hyU, hyC⟩
      · rintro ⟨hyU, hyC⟩; exact ⟨⟨hU hyU, hyC⟩, hyU⟩
    rw [hRinf, q13d_E0_eq h, q13d_card_E0 h] at h2
    norm_num at h2 ⊢
    omega
  exact le_antisymm hhigh hlow

theorem q13d_I_R2_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hU :
      ctxU t tau x₁ x₂ lam ≤ 𝒮)
    (hcard : Nat.card ↥𝒮 = 2 ^ 11) :
    ∀ r ∈ 𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G),
      (t * lam)⁻¹ * (r * (t * lam) * r⁻¹) ∈ q13E0 t tau x₁ x₂ rho om := by
  intro r hr
  have hrel := q13dI4a_relIndex h hU hcard
  have hnorm : NormalIn (ctxU t tau x₁ x₂ lam) 𝒮 := by
    refine ⟨hU, ?_⟩
    have hsub : ((ctxU t tau x₁ x₂ lam).subgroupOf 𝒮).index = 2 := by
      simpa only [Subgroup.relIndex] using hrel
    have hNormal : ((ctxU t tau x₁ x₂ lam).subgroupOf 𝒮).Normal :=
      Subgroup.normal_of_index_eq_two hsub
    intro g hg k hk
    have hx : (⟨k, hU hk⟩ : ↥𝒮) ∈ (ctxU t tau x₁ x₂ lam).subgroupOf 𝒮 := by
      rw [Subgroup.mem_subgroupOf]; exact hk
    have hconj := hNormal.conj_mem (⟨k, hU hk⟩ : ↥𝒮) hx (⟨g, hg⟩ : ↥𝒮)
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  have hfU : t * lam ∈ ctxU t tau x₁ x₂ lam :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (q13b_t_mem_O h))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers lam))
  have hrS : r ∈ 𝒮 := (Subgroup.mem_inf.mp hr).1
  have hrCN : r ∈ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hr).2
  have hxU : (t * lam)⁻¹ * (r * (t * lam) * r⁻¹) ∈ ctxU t tau x₁ x₂ lam :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hfU) (hnorm.2 r hrS (t * lam) hfU)
  have hxCN : (t * lam)⁻¹ * (r * (t * lam) * r⁻¹) ∈
      centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
    have hB𝒮 : Q13B t x₁ x₂ tau 𝒮 := hB 𝒮 h𝒮 hU
    have hfr : (t * lam)⁻¹ * r * (t * lam) ∈
        centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hfn : (t * lam) * n * (t * lam)⁻¹ ∈ ctxN tau x₁ x₂ :=
        hB𝒮.N_normal.2 (t * lam) (hU hfU) n hn
      have hcomm : ((t * lam) * n * (t * lam)⁻¹) * r =
          r * ((t * lam) * n * (t * lam)⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hrCN) _ hfn
      calc n * ((t * lam)⁻¹ * r * (t * lam))
          = (t * lam)⁻¹ * (((t * lam) * n * (t * lam)⁻¹) * r) * (t * lam) := by group
        _ = (t * lam)⁻¹ * (r * ((t * lam) * n * (t * lam)⁻¹)) * (t * lam) := by rw [hcomm]
        _ = ((t * lam)⁻¹ * r * (t * lam)) * n := by group
    have hrinv : r⁻¹ ∈ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hrCN
    have hx' : (t * lam)⁻¹ * r * (t * lam) * r⁻¹ ∈
        centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ hfr hrinv
    have heq : (t * lam)⁻¹ * (r * (t * lam) * r⁻¹) =
        (t * lam)⁻¹ * r * (t * lam) * r⁻¹ := by group
    rwa [heq]
  rw [← q13d_E0_eq h]
  exact Subgroup.mem_inf.mpr ⟨hxU, hxCN⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
