module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL42
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AA4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzl_conj_Z (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) {n : G}
    (hn : n ∈ fzN2 t x₁ x₂) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    n * z * n⁻¹ ∈ fourGrp x₁ x₂ := by
  obtain ⟨w, hw, hwz⟩ := fzl_exists_sq_Z h hz
  have hn' : n ∈ Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := hn
  have hwn : n * w * n⁻¹ ∈ ctxW t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn' w).mp hw
  have heq : n * z * n⁻¹ = (n * w * n⁻¹) ^ 2 := by rw [← hwz, conj_pow]
  rw [heq]
  exact fzl_sq_mem_Z h hK hwn

theorem fzl_conj_t (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) {n : G}
    (hn : n ∈ fzN2 t x₁ x₂) : ∃ z ∈ fourGrp x₁ x₂, n * t * n⁻¹ = t * z := by
  obtain ⟨htW, ht2, -, htZ⟩ := fzl_t_facts h
  have hn' : n ∈ Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := hn
  have hntW : n * t * n⁻¹ ∈ ctxW t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hn' t).mp htW
  have hnt2 : (n * t * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow (a := n) (b := t) (i := 2), ht2, mul_one, mul_inv_cancel]
  rcases fzl_invol_mem_W h hK hntW hnt2 with hmem | ⟨z, hz, hwz⟩
  · exfalso
    have hninv : n⁻¹ ∈ fzN2 t x₁ x₂ := (fzN2 t x₁ x₂).inv_mem hn
    have hconj := fzl_conj_Z h hK hninv hmem
    have heq : n⁻¹ * (n * t * n⁻¹) * (n⁻¹)⁻¹ = t := by group
    rw [heq] at hconj
    exact htZ hconj
  · exact ⟨z, hz, hwz⟩

theorem fzl_rho_Z (h : Ctx t L S x₁ x₂ lam rho tau) :
    rho ∈ fzN2 t x₁ x₂ ∧ rho * t * rho⁻¹ = t ∧ rho ^ 3 = 1 ∧
      (∀ z ∈ fourGrp x₁ x₂, z ≠ 1 → rho * z * rho⁻¹ ≠ z) := by
  refine ⟨h.rho_normalizes, ?_, ?_, ?_⟩
  · have htmem : t ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      rw [h.cent_rho]
      exact h.hyp.mem_twoCore
    have hc : rho * t = t * rho :=
      (Subgroup.mem_centralizer_iff.mp htmem.2) rho (by simp)
    rw [hc]; group
  · rw [← h.ord_rho]
    exact pow_orderOf_eq_one rho
  · intro z hz hzne hfix
    have hc : rho * z = z * rho := mul_inv_eq_iff_eq_mul.mp hfix
    have hzW : z ∈ ctxW t x₁ x₂ := fzl_Z_le_W h hz
    have hzC : z ∈ centralizer ({rho} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
    have hzP : z ∈ twoCore t := by
      have hmem : z ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hzW, hzC⟩
      rwa [h.cent_rho] at hmem
    have hzB : z ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hz
    have hbot : z ∈ (⊥ : Subgroup G) := by
      have hmem : z ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨hzP, hzB⟩
      rwa [S4A.pt_inf_base h.toCtx0] at hmem
    exact hzne (Subgroup.mem_bot.mp hbot)

theorem fzl_lam_Z (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam ∈ fzN2 t x₁ x₂ ∧ lam * t * lam⁻¹ = t ∧ lam ^ 2 = 1 ∧
      lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 ∧ lam * x₂ ^ 2 * lam⁻¹ = x₁ ^ 2 ∧
      lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
  have hlamS : lam ∈ S := by
    have hmem : lam ∈ S ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.subset_closure (by simp)
    exact hmem.1
  have hlamN2 : lam ∈ fzN2 t x₁ x₂ := fz_S_le_N2 h hlamS
  have hlam2 : lam ^ 2 = 1 := by
    rw [← h.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have hll : lam * lam = 1 := by rw [← pow_two]; exact hlam2
  have hllinv : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hll, inv_one]
  have hx2 : lam * x₂ * lam⁻¹ = x₁ := by
    have key : lam * (lam * x₁ * lam⁻¹) * lam⁻¹ = x₁ := by
      calc lam * (lam * x₁ * lam⁻¹) * lam⁻¹
          = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
        _ = x₁ := by rw [hll, hllinv, one_mul, mul_one]
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.wreath.conj_x₁]
      _ = x₁ := key
  have hx1sq : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
    calc lam * x₁ ^ 2 * lam⁻¹ = (lam * x₁ * lam⁻¹) ^ 2 :=
          (conj_pow (a := lam) (b := x₁) (i := 2)).symm
      _ = x₂ ^ 2 := by rw [h.wreath.conj_x₁]
  have hx2sq : lam * x₂ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
    calc lam * x₂ ^ 2 * lam⁻¹ = (lam * x₂ * lam⁻¹) ^ 2 :=
          (conj_pow (a := lam) (b := x₂) (i := 2)).symm
      _ = x₁ ^ 2 := by rw [hx2]
  have hprod : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
    calc lam * (x₁ * x₂) * lam⁻¹
        = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) := by group
      _ = x₂ * x₁ := by rw [h.wreath.conj_x₁, hx2]
      _ = x₁ * x₂ := h.wreath.comm.symm
  have hprod2 : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
    calc lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 :=
          (conj_pow (a := lam) (b := x₁ * x₂) (i := 2)).symm
      _ = (x₁ * x₂) ^ 2 := by rw [hprod]
  have hcommt : lam * t = t * lam := S4A.mem_invCent_iff.mp (h.le_invCent hlamS)
  refine ⟨hlamN2, ?_, hlam2, hx1sq, hx2sq, hprod2⟩
  rw [hcommt]; group

theorem fzl_lam_rho (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam * rho * lam⁻¹ = rho⁻¹ ∧ rho ≠ 1 ∧ lam ≠ 1 := by
  refine ⟨h.lam_rho, ?_, ?_⟩
  · intro h1
    have hord := h.ord_rho
    rw [h1, orderOf_one] at hord
    omega
  · intro h1
    have hord := h.wreath.ord_lam
    rw [h1, orderOf_one] at hord
    omega

theorem fzl_exists_swap
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    ∃ n ∈ fzN2 t x₁ x₂, n * t * n⁻¹ = t * z := by
  by_cases hz1 : z = 1
  · exact ⟨1, (fzN2 t x₁ x₂).one_mem, by rw [hz1]; group⟩
  obtain ⟨hrhoN2, hrhot, -, -⟩ := fzl_rho_Z h
  have h128 : Nat.card S = 128 := by rw [h.card_S, hK]; norm_num
  have hSdvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  rw [h128] at hSdvd
  have h4 : 4 ∣ Nat.card G := dvd_trans (by norm_num : 4 ∣ 128) hSdvd
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

end CFSG.OddStandard.SmallF3.FritzII
