module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbFit18
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem isPGroup_ctxO (t tau x₁ x₂ : G) : IsPGroup 2 (ctxO t tau x₁ x₂) := by
  rw [ctxO, CFSG.Open.pCoreOf]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(ctxM t tau x₁ x₂))).map
    (ctxM t tau x₁ x₂).subtype

private theorem CO_normalizes_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∀ k ∈ ctxCO t tau x₁ x₂ rho, ∀ h ∈ ctxR t tau x₁ x₂, k * h * k⁻¹ ∈ ctxR t tau x₁ x₂ := by
  intro k hk h hh
  have hk' : k ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := hk
  have hkO : k ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp hk').1
  exact hc.normal_R.2 k ((CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxM t tau x₁ x₂)) hkO) h hh

private theorem ctxN_le_ctxX (t tau x₁ x₂ : G) : ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxN, ctxX]
  apply Subgroup.closure_mono
  rintro a (rfl | rfl | rfl) <;> simp

theorem l12_rho_lam_mem_M (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    rho ∈ ctxM t tau x₁ x₂ ∧ lam ∈ ctxM t tau x₁ x₂ := by
  constructor
  · rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem l12_Q_le_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
  rw [hc.R_eq]
  exact le_sup_left

theorem l12_isPGroup_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    IsPGroup 2 (ctxR t tau x₁ x₂) :=
  (isPGroup_ctxO t tau x₁ x₂).to_le hc.R_le_O

theorem l12_Q_eq_comm_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho = ⁅ctxR t tau x₁ x₂, zpowers rho⁆ := by
  apply le_antisymm
  · change ⁅ctxO t tau x₁ x₂, zpowers rho⁆ ≤ ⁅ctxR t tau x₁ x₂, zpowers rho⁆
    rw [Subgroup.commutator_le]
    intro o ho g hg
    obtain ⟨r, hr, c, hcCO, rfl⟩ :=
      (mem_sup_iff_of_normalizes (H := ctxR t tau x₁ x₂)
        (K := ctxCO t tau x₁ x₂ rho) (CO_normalizes_R hc)).mp (hc.O_eq ▸ ho)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcommc : Commute c rho :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hcCO).2
    have hcρ : ⁅c, rho ^ k⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (hcommc.zpow_right k)
    have hval : ⁅r * c, rho ^ k⁆ = ⁅r, rho ^ k⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hcρ]
      group
    rw [← hk, hval]
    exact Subgroup.commutator_mem_commutator hr (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  · change ⁅ctxR t tau x₁ x₂, zpowers rho⁆ ≤ ⁅ctxO t tau x₁ x₂, zpowers rho⁆
    exact Subgroup.commutator_mono hc.R_le_O le_rfl

theorem l12_cent_Q_le (hc : Ctx11 t L S x₁ x₂ lam rho tau) {N : Subgroup G}
    (hNR : N ≤ ctxR t tau x₁ x₂) (hNn : ∀ c ∈ ctxR t tau x₁ x₂, ∀ q ∈ N, c * q * c⁻¹ ∈ N)
    (hNρ : ∀ q ∈ N, rho * q * rho⁻¹ ∈ N)
    (hab : ∀ c ∈ ctxR t tau x₁ x₂, ∀ c' ∈ ctxR t tau x₁ x₂, c * c' * c⁻¹ * c'⁻¹ ∈ N) :
    ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x ∈ N := by
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρR : ∀ c ∈ ctxR t tau x₁ x₂, rho * c * rho⁻¹ ∈ ctxR t tau x₁ x₂ :=
    fun c hcR => hc.normal_R.2 rho (l12_rho_lam_mem_M hc).1 c hcR
  rw [l12_Q_eq_comm_R hc]
  exact comm_zpowers_inf_cent_le hρ3 (l12_isPGroup_R hc) hNR hNn hNρ hρR hab

theorem l12_t_not_mem_Q (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    t ∉ ctxQ t tau x₁ x₂ rho := by
  intro ht
  have hNR : ctxN tau x₁ x₂ ≤ ctxR t tau x₁ x₂ :=
    (ctxN_le_ctxX t tau x₁ x₂).trans hc.X_le_R
  have hNn : ∀ c ∈ ctxR t tau x₁ x₂, ∀ q ∈ ctxN tau x₁ x₂, c * q * c⁻¹ ∈ ctxN tau x₁ x₂ := by
    intro c hcR q hq
    exact hc.normal_N.2 c ((CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxM t tau x₁ x₂))
      (hc.R_le_O hcR)) q hq
  have hNρ : ∀ q ∈ ctxN tau x₁ x₂, rho * q * rho⁻¹ ∈ ctxN tau x₁ x₂ := by
    intro q hq
    exact hc.normal_N.2 rho (l12_rho_lam_mem_M hc).1 q hq
  have hab : ∀ c ∈ ctxR t tau x₁ x₂, ∀ c' ∈ ctxR t tau x₁ x₂,
      c * c' * c⁻¹ * c'⁻¹ ∈ ctxN tau x₁ x₂ :=
    fun c hc' c' hc'' => l12_comm_mem_N hc hc' hc''
  have ht_comm : t * rho = rho * t := by
    have htmem : t ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      rw [hc.CR_rho]
      exact Subgroup.subset_closure (by simp)
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp htmem).2
  have htN : t ∈ ctxN tau x₁ x₂ :=
    l12_cent_Q_le hc (N := ctxN tau x₁ x₂) hNR hNn hNρ hab t ht ht_comm
  exact l12_t_not_mem_N hc.toCtx10.toCtx4 htN

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
