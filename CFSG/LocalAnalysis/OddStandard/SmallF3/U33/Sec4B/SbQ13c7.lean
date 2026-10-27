module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c5b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c6

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_key (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    Nat.card ↥(𝒮 ⊓ centralizer ({t * lam} : Set G)) ≠ 2 ^ 7 := by
  intro hcard
  let D : Subgroup G := 𝒮 ⊓ centralizer ({t * lam} : Set G)
  have hD2 : IsPGroup 2 D := h𝒮.to_le (inf_le_left : D ≤ 𝒮)
  have hDc : D ≤ centralizer ({t * lam} : Set G) := inf_le_right
  obtain ⟨g, hg, hD⟩ := q13c_sylow_conj h hD2 hDc hcard
  set t' : G := g⁻¹ * t * g with ht'def
  have htD : t ∈ D := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hU (q13b_O_le_U h (q13b_t_mem_O h))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * (t * lam) = (t * t) * lam := by group
        _ = lam := by rw [q13a_t_mul_self h, one_mul]
        _ = (t * lam) * t := by
            rw [show (t * lam) * t = t * (lam * t) by group, ← (q13a_t_comm h).1]
            rw [← mul_assoc, q13a_t_mul_self h, one_mul]
  have ht'S : t' ∈ S := by
    rw [ht'def]
    exact (hD t).mp htD
  have ht't' : t' * t' = 1 := by
    rw [ht'def]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [q13a_t_mul_self h]; group
  have ht'H : t' ∈ invCent t := h.c11.le_invCent ht'S
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have htyN : g * (x₁ ^ 2) * g⁻¹ ∈ ctxN tau x₁ x₂ :=
    (Subgroup.mem_inf.mp (q13c_transport h hB h𝒮 hU hD (x₁ ^ 2) hyV)).1
  have hcomm_y : t' * x₁ ^ 2 = x₁ ^ 2 * t' := by
    have hc := q13c_t_cent_N h (g * (x₁ ^ 2) * g⁻¹) htyN
    calc t' * x₁ ^ 2 = g⁻¹ * (t * (g * x₁ ^ 2 * g⁻¹)) * g := by rw [ht'def]; group
      _ = g⁻¹ * ((g * x₁ ^ 2 * g⁻¹) * t) * g := by rw [hc]
      _ = x₁ ^ 2 * t' := by rw [ht'def]; group
  by_cases ht'F : t' ∈ twoCore t ⊔ L
  · rcases q13c_inv_PT h ht'S ht'F ht't' hcomm_y with ht'V | htV
    · have htN : t ∈ ctxN tau x₁ x₂ := by
        have hmem := (Subgroup.mem_inf.mp
          (q13c_transport h hB h𝒮 hU hD t' ht'V)).1
        rwa [show g * t' * g⁻¹ = t by rw [ht'def]; group] at hmem
      exact (hB 𝒮 h𝒮 hU).tG_N 1 (by simpa using htN)
    · have hlamN : lam ∈ ctxN tau x₁ x₂ := by
        have hmem := (Subgroup.mem_inf.mp
          (q13c_transport h hB h𝒮 hU hD (t * t') htV)).1
        rwa [show g * (t * t') * g⁻¹ = lam by
          rw [ht'def]
          calc g * (t * (g⁻¹ * t * g)) * g⁻¹ = (g * t * g⁻¹) * t := by group
            _ = (t * lam) * t := by rw [hg]
            _ = lam := by
                calc (t * lam) * t = t * (lam * t) := by group
                  _ = t * (t * lam) := by rw [← (q13a_t_comm h).1]
                  _ = (t * t) * lam := by group
                  _ = lam := by rw [q13a_t_mul_self h, one_mul]] at hmem
      exact q13c_lam_not_mem_O h (q13b_N_le_O h hlamN)
  · have h1 : Nat.card ↥(invCent t ⊓ centralizer ({t'} : Set G)) ≤ 96 :=
      q13c_card_cent_outer h ht'H ht't' ht'F
    have h2 : Nat.card ↥(invCent t ⊓ centralizer ({t'} : Set G)) =
        Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) := by
      rw [ht'def]
      exact q13c_card_cent_conj h hg
    have h3 : 2 ^ 7 ≤ Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) :=
      q13c_card_cent_lam_ge h
    have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [h128] at h3
    omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
