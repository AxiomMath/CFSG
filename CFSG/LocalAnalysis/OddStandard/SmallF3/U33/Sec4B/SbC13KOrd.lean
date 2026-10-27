module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KOrb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0Card

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_tK_sub (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    conjIn (ctxK t tau x₁ x₂ rho) t ⊆ c13KTp t tau x₁ x₂ rho := by
  rintro u ⟨k, hkK, hku⟩
  have ht2 : t * t = 1 := by
    have h := (c13K_rel hc).1
    rwa [pow_two] at h
  have ht_ne : t ≠ 1 := (c13K_rel hc).2.1
  have hkK' : k ∈ normalizer
      ((ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) : Subgroup G) : Set G) := hkK
  have ht_mem : t ∈ (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hr_mem : k * t * k⁻¹ ∈
      (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hkK' t).mp ht_mem
  have hR : k * t * k⁻¹ ∈ ctxR t tau x₁ x₂ := by
    rw [(c13K_lemma4_12a hc).2.2.2.2.1]
    exact hr_mem
  have hu2 : u ^ 2 = 1 := by
    rw [← hku, pow_two]
    calc (k * t * k⁻¹) * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hu_ne : u ≠ 1 := by
    intro h
    have h1 : k * t * k⁻¹ = 1 := by rw [hku, h]
    have h2 : t = 1 := by
      calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    exact ht_ne h2
  obtain ⟨q, hq, hcases⟩ := c13K_mem_R_cases hc hR
  have hqSup : q ∈ (ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_left hq
  have htauSup : tau ∈ (ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htauqSup : tau * q ∈
      (ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) : Subgroup G) :=
    (ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G)).mul_mem htauSup hqSup
  rcases hcases with hq_eq | htq_eq | htauq_eq | httauq_eq
  · exfalso
    exact hc.tG_Qom k q hqSup hq_eq
  · left
    refine ⟨?_, hu2, hu_ne⟩
    rw [Set.mem_smul_set]
    exact ⟨q, hq, by rw [smul_eq_mul]; rw [← htq_eq, hku]⟩
  · exfalso
    exact hc.tG_Qom k (tau * q) htauqSup htauq_eq
  · right
    refine ⟨?_, hu2, hu_ne⟩
    rw [Set.mem_smul_set]
    exact ⟨q, hq, by rw [smul_eq_mul]; rw [← httauq_eq, hku]⟩

theorem c13K_tK_eq
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om)
    (hne : ∃ k ∈ ctxK t tau x₁ x₂ rho, k ∉ ctxM t tau x₁ x₂) :
    conjIn (ctxK t tau x₁ x₂ rho) t = c13KTp t tau x₁ x₂ rho := by
  have hMT : conjIn (ctxM t tau x₁ x₂) t ⊆ conjIn (ctxK t tau x₁ x₂ rho) t := by
    rintro u ⟨m, hmM, rfl⟩
    exact ⟨m, hc.M_le_K hmM, rfl⟩
  have hstable : ∀ m ∈ ctxM t tau x₁ x₂,
      ∀ s ∈ conjIn (ctxK t tau x₁ x₂ rho) t,
      m * s * m⁻¹ ∈ conjIn (ctxK t tau x₁ x₂ rho) t := by
    intro m hmM s hs
    obtain ⟨k, hkK, rfl⟩ := hs
    exact ⟨m * k, (ctxK t tau x₁ x₂ rho).mul_mem (hc.M_le_K hmM) hkK, by group⟩
  have hne_TK : conjIn (ctxK t tau x₁ x₂ rho) t ≠ conjIn (ctxM t tau x₁ x₂) t := by
    intro heq
    have hKcard := card_eq_ncard_conjIn_mul (ctxK t tau x₁ x₂ rho) t
    have hMcard := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) t
    have hCK := c13K_CK_t_eq hc
    have hcard : Nat.card ↥(ctxK t tau x₁ x₂ rho) = Nat.card ↥(ctxM t tau x₁ x₂) := by
      rw [hKcard, hMcard, hCK, heq]
    have hMK : ctxM t tau x₁ x₂ ≤ ctxK t tau x₁ x₂ rho := hc.M_le_K
    have heqMK : ctxM t tau x₁ x₂ = ctxK t tau x₁ x₂ rho :=
      Subgroup.eq_of_le_of_card_ge hMK (le_of_eq hcard)
    obtain ⟨k, hkK, hknotM⟩ := hne
    exact hknotM (by rw [heqMK]; exact hkK)
  have hnotsub : ¬ conjIn (ctxK t tau x₁ x₂ rho) t ⊆ conjIn (ctxM t tau x₁ x₂) t :=
    fun hsub => hne_TK (Set.Subset.antisymm hsub hMT)
  obtain ⟨s₀, hs₀TK, hs₀nM⟩ := Set.not_subset.mp hnotsub
  have hs₀Tp : s₀ ∈ c13KTp t tau x₁ x₂ rho := c13K_tK_sub hc hs₀TK
  have hsub : c13KTp t tau x₁ x₂ rho ⊆ conjIn (ctxK t tau x₁ x₂ rho) t := by
    intro s' hs'
    by_cases hs'M : s' ∈ conjIn (ctxM t tau x₁ x₂) t
    · exact hMT hs'M
    · obtain ⟨m, hmM, hm⟩ := c13K_orbit_trans hc hs₀Tp hs' hs₀nM hs'M
      rw [← hm]
      exact hstable m hmM s₀ hs₀TK
  exact Set.Subset.antisymm (c13K_tK_sub hc) hsub

theorem c13K_card_K
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om)
    (hne : ∃ k ∈ ctxK t tau x₁ x₂ rho, k ∉ ctxM t tau x₁ x₂) :
    Nat.card ↥(ctxK t tau x₁ x₂ rho) = 3 * 2 ^ 12 := by
  have hcard := card_eq_ncard_conjIn_mul (ctxK t tau x₁ x₂ rho) t
  rw [hcard, c13K_tK_eq hc hne, c13K_ncard_Tp hc, c13K_CK_t_eq hc, c13K_card_CM_t hc]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
