module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzbs_not_conj_Z
    (h : Ctx t L S x₁ x₂ lam rho tau) (g : G) {z : G}
    (hz : z ∈ fourGrp x₁ x₂) : g * t * g⁻¹ ≠ z := by
  have ht_ne : t ≠ 1 := by
    intro h1
    have hord := h.hyp.ord_t
    rw [h1, orderOf_one] at hord
    norm_num at hord
  intro hgt
  by_cases hz1 : z = 1
  · exact ht_ne (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * z * g := by rw [hgt]
        _ = 1 := by rw [hz1]; group)
  · rcases S4A.mem_fourGrp_cases_rho h.toCtx0 hz with h1 | h1 | h1 | h1
    · exact hz1 h1
    · exact S4A.not_conj_z_of_ctx h ⟨g, hgt.trans h1⟩
    · refine S4A.not_conj_z_of_ctx h ⟨rho⁻¹ * g, ?_⟩
      calc (rho⁻¹ * g) * t * (rho⁻¹ * g)⁻¹
          = rho⁻¹ * (g * t * g⁻¹) * rho := by group
        _ = rho⁻¹ * z * rho := by rw [hgt]
        _ = (x₁ * x₂) ^ 2 := by rw [h1]; group
    · refine S4A.not_conj_z_of_ctx h ⟨rho * g, ?_⟩
      calc (rho * g) * t * (rho * g)⁻¹
          = rho * (g * t * g⁻¹) * rho⁻¹ := by group
        _ = rho * z * rho⁻¹ := by rw [hgt]
        _ = (x₁ * x₂) ^ 2 := by rw [h1]; group

theorem fzbs_conj_t
    (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ fzN2 t x₁ x₂) : ∃ z ∈ fourGrp x₁ x₂, n * t * n⁻¹ = t * z := by
  obtain ⟨htW, ht2, -, -⟩ := fzl_t_facts h
  have hn' : n ∈ Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := hn
  have hntW : n * t * n⁻¹ ∈ ctxW t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn' t).mp htW
  have hnt2 : (n * t * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow (a := n) (b := t) (i := 2), ht2, mul_one, mul_inv_cancel]
  rcases fzbs_invol_W h hntW hnt2 with hmem | ⟨z, hz, hwz⟩
  · exact (fzbs_not_conj_Z h n hmem rfl).elim
  · exact ⟨z, hz, hwz⟩

theorem fzbs_exists_swap
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) {z : G}
    (hz : z ∈ fourGrp x₁ x₂) : ∃ n ∈ fzN2 t x₁ x₂, n * t * n⁻¹ = t * z := by
  by_cases hz1 : z = 1
  · exact ⟨1, (fzN2 t x₁ x₂).one_mem, by rw [hz1]; group⟩
  obtain ⟨hrhoN2, hrhot, -, -⟩ := fzl_rho_Z h
  have hS : 2 ^ 6 ∣ Nat.card S := ⟨Nat.card (twoCore t), h.card_S⟩
  have h4 : 4 ∣ Nat.card G :=
    ((by norm_num : 4 ∣ 2 ^ 6).trans hS).trans (Subgroup.card_subgroup_dvd_card S)
  have h2 : 2 ∣ S.index := S4A.lemma4_2_of_simple (inferInstance : IsSimpleGroup G) h4 h
  obtain ⟨n₀, hn₀S, hn₀t⟩ := S4A.exists_swap_of_l42 h h2
  have hn₀N2 : n₀ ∈ fzN2 t x₁ x₂ := by
    rw [fzN2, Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact S4A.conj_mem_ctxW_of_mem_normalizer h hn₀S hw
    · intro hw
      have hn₀inv : n₀⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hn₀S
      have h' := S4A.conj_mem_ctxW_of_mem_normalizer h hn₀inv hw
      rwa [show n₀⁻¹ * (n₀ * w * n₀⁻¹) * (n₀⁻¹)⁻¹ = w by group] at h'
  have hrhot_inv : rho⁻¹ * t * rho = t := by
    calc rho⁻¹ * t * rho = rho⁻¹ * (rho * t * rho⁻¹) * rho := by rw [hrhot]
      _ = t := by group
  rcases S4A.mem_fourGrp_cases_rho h.toCtx0 hz with h1 | h1 | h1 | h1
  · exact absurd h1 hz1
  · exact ⟨n₀, hn₀N2, by rw [h1, hn₀t]⟩
  · refine ⟨rho * n₀ * rho⁻¹, ?_, ?_⟩
    · exact (fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hrhoN2 hn₀N2)
        ((fzN2 t x₁ x₂).inv_mem hrhoN2)
    · rw [h1]
      calc (rho * n₀ * rho⁻¹) * t * (rho * n₀ * rho⁻¹)⁻¹
          = rho * (n₀ * (rho⁻¹ * t * rho) * n₀⁻¹) * rho⁻¹ := by group
        _ = rho * (n₀ * t * n₀⁻¹) * rho⁻¹ := by rw [hrhot_inv]
        _ = rho * (t * (x₁ * x₂) ^ 2) * rho⁻¹ := by rw [hn₀t]
        _ = t * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) := by
              calc rho * (t * (x₁ * x₂) ^ 2) * rho⁻¹
                  = (rho * t * rho⁻¹) * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) := by group
                _ = t * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) := by rw [hrhot]
  · refine ⟨rho⁻¹ * n₀ * rho, ?_, ?_⟩
    · exact (fzN2 t x₁ x₂).mul_mem
        ((fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).inv_mem hrhoN2) hn₀N2) hrhoN2
    · rw [h1]
      calc (rho⁻¹ * n₀ * rho) * t * (rho⁻¹ * n₀ * rho)⁻¹
          = rho⁻¹ * (n₀ * (rho * t * rho⁻¹) * n₀⁻¹) * rho := by group
        _ = rho⁻¹ * (n₀ * t * n₀⁻¹) * rho := by rw [hrhot]
        _ = rho⁻¹ * (t * (x₁ * x₂) ^ 2) * rho := by rw [hn₀t]
        _ = t * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) := by
              calc rho⁻¹ * (t * (x₁ * x₂) ^ 2) * rho
                  = (rho⁻¹ * t * rho) * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) := by group
                _ = t * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) := by rw [hrhot_inv]

theorem fzbs_conj_Z
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ fzN2 t x₁ x₂) {z : G} (hz : z ∈ fourGrp x₁ x₂) : n * z * n⁻¹ ∈ fourGrp x₁ x₂ := by
  obtain ⟨m, hmN2, hmt⟩ := fzbs_exists_swap h hz
  obtain ⟨z₂, hz₂, hz₂eq⟩ := fzbs_conj_t h hn
  have hnmN2 : n * m ∈ fzN2 t x₁ x₂ := (fzN2 t x₁ x₂).mul_mem hn hmN2
  obtain ⟨z₁, hz₁, hz₁eq⟩ := fzbs_conj_t h hnmN2
  have hnz : n * (t * z) * n⁻¹ = t * z₁ := by
    calc n * (t * z) * n⁻¹ = n * (m * t * m⁻¹) * n⁻¹ := by rw [hmt]
      _ = (n * m) * t * (n * m)⁻¹ := by group
      _ = t * z₁ := hz₁eq
  have key : n * z * n⁻¹ = (t * z₂)⁻¹ * (t * z₁) := by
    calc n * z * n⁻¹ = (n * t * n⁻¹)⁻¹ * (n * (t * z) * n⁻¹) := by group
      _ = (t * z₂)⁻¹ * (t * z₁) := by rw [hz₂eq, hnz]
  rw [key]
  have hprod : (t * z₂)⁻¹ * (t * z₁) = z₂⁻¹ * z₁ := by group
  rw [hprod]
  exact (fourGrp x₁ x₂).mul_mem ((fourGrp x₁ x₂).inv_mem hz₂) hz₁

theorem fzbs_conj_X
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ fzN2 t x₁ x₂) {x : G} (hx : x ∈ fzbsX t x₁ x₂) : n * x * n⁻¹ ∈ fzbsX t x₁ x₂ := by
  have hXW : fzbsX t x₁ x₂ ≤ ctxW t x₁ x₂ := (fzbs_X_le h).2.2.2
  have hxW : x ∈ ctxW t x₁ x₂ := hXW hx
  have hn' : n ∈ Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := hn
  have hnxW : n * x * n⁻¹ ∈ ctxW t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn' x).mp hxW
  have hsq : x ^ 2 ∈ fourGrp x₁ x₂ := (fzbs_mem_X_iff h hxW).mp hx
  rw [fzbs_mem_X_iff h hnxW, conj_pow]
  exact fzbs_conj_Z h hn hsq

end CFSG.OddStandard.SmallF3.FritzII
