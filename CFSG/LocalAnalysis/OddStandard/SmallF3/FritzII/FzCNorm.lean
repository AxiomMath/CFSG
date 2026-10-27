module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNormA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_K_pGroup (t : G) : IsPGroup 2 (twoCore t) := by
  rw [twoCore]
  exact fzc_pCoreOf_two_isPGroup (invCent t)

theorem fzc_rho_cube (hs : FzCSteps t L S x₁ x₂ lam rho) : rho ^ 3 = 1 := by
  have := pow_orderOf_eq_one rho
  rwa [hs.ctx.ord_rho] at this

theorem fzc_lam_mem_S (hs : FzCSteps t L S x₁ x₂ lam rho) : lam ∈ S := by
  have hmem : lam ∈ S ⊓ L := by
    rw [hs.ctx.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.1

theorem fzc_rho_cent_t (hs : FzCSteps t L S x₁ x₂ lam rho) : rho * t * rho⁻¹ = t := by
  have hcomm : rho * t = t * rho :=
    Subgroup.mem_centralizer_iff.mp hs.ctx.hyp.mem_centralizer rho hs.ctx.rho_mem
  calc rho * t * rho⁻¹ = t * rho * rho⁻¹ := by rw [hcomm]
    _ = t := by group

theorem fzc_closure_cent_t (hs : FzCSteps t L S x₁ x₂ lam rho) {c : G}
    (hc : c ∈ closure ({rho, lam} : Set G)) : c * t * c⁻¹ = t := by
  have hcomm_rho : rho * t = t * rho :=
    Subgroup.mem_centralizer_iff.mp hs.ctx.hyp.mem_centralizer rho hs.ctx.rho_mem
  have hlamL : lam ∈ L := by
    have hmem : lam ∈ S ⊓ L := by
      rw [hs.ctx.inf_eq]
      exact Subgroup.subset_closure (by simp)
    exact hmem.2
  have hcomm_lam : lam * t = t * lam :=
    Subgroup.mem_centralizer_iff.mp hs.ctx.hyp.mem_centralizer lam hlamL
  have hle : closure ({rho, lam} : Set G) ≤ invCent t := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm_rho
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm_lam
  have hct : c * t = t * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
  calc c * t * c⁻¹ = t * c * c⁻¹ := by rw [hct]
    _ = t := by group

theorem fzc_N2_eq (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzN2 t x₁ x₂ = l41N t x₁ x₂ := by
  apply le_antisymm
  · intro n hn
    unfold fzN2 at hn
    rw [l41N, Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have ha2 : a * a = 1 := by
        have h := hs.basic.A_elem.1.2 a ha
        rwa [pow_two] at h
      have hnaW : n * a * n⁻¹ ∈ ctxW t x₁ x₂ :=
        (Subgroup.mem_normalizer_iff.mp hn a).mp (fzc_ctxE_le_ctxW hs ha)
      have hna2 : (n * a * n⁻¹) * (n * a * n⁻¹) = 1 := by
        calc (n * a * n⁻¹) * (n * a * n⁻¹) = n * (a * a) * n⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      exact fzc_omega_ctxW_le hs hnaW hna2
    · intro hna
      have hnaW : n * a * n⁻¹ ∈ ctxW t x₁ x₂ := fzc_ctxE_le_ctxW hs hna
      have hna2 : (n * a * n⁻¹) * (n * a * n⁻¹) = 1 := by
        have h := hs.basic.A_elem.1.2 (n * a * n⁻¹) hna
        rwa [pow_two] at h
      have haW : a ∈ ctxW t x₁ x₂ := by
        have h := (Subgroup.mem_normalizer_iff''.mp hn (n * a * n⁻¹)).mp hnaW
        have e : n⁻¹ * (n * a * n⁻¹) * n = a := by group
        rwa [e] at h
      have ha2 : a * a = 1 := by
        have e : n⁻¹ * ((n * a * n⁻¹) * (n * a * n⁻¹)) * n = a * a := by group
        rw [hna2] at e
        simpa using e.symm
      exact fzc_omega_ctxW_le hs haW ha2
  · intro n hn
    unfold fzN2
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fzc_conj_W hs hn
    · intro hw
      have h1 := fzc_conj_W hs (Subgroup.inv_mem _ hn) hw
      have e : n⁻¹ * (n * w * n⁻¹) * (n⁻¹)⁻¹ = w := by group
      rwa [e] at h1

theorem fzc_R_eq (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzR t x₁ x₂ = l41O2 t x₁ x₂ := by
  unfold fzR l41O2
  rw [fzc_N2_eq hs]

theorem fzc_rho_mem_N (hs : FzCSteps t L S x₁ x₂ lam rho) : rho ∈ l41N t x₁ x₂ := by
  rw [hs.N_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem fzc_lam_mem_N (hs : FzCSteps t L S x₁ x₂ lam rho) : lam ∈ l41N t x₁ x₂ := by
  rw [hs.N_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem fzc_conj_mem_R (hs : FzCSteps t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂)
    {x : G} (hx : x ∈ fzR t x₁ x₂) : n * x * n⁻¹ ∈ fzR t x₁ x₂ := by
  rw [fzc_R_eq hs] at hx ⊢
  exact fzc_pCoreOf_two_conj_mem hn hx

theorem fzc_W_le_R (hs : FzCSteps t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ fzR t x₁ x₂ := by
  unfold fzR
  refine fzc_le_pCoreOf_two (Q := ctxW t x₁ x₂) ?_ ?_ ?_
  · unfold fzN2
    exact Subgroup.le_normalizer
  · intro n hn q hq
    unfold fzN2 at hn
    exact (Subgroup.mem_normalizer_iff.mp hn q).mp hq
  · exact hs.ctx.isPGroup.to_le hs.basic.normal_W.1

theorem fzc_V_eq (hs : FzCSteps t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ = fzR t x₁ x₂ ⊔ zpowers lam := by
  have hWR : ctxW t x₁ x₂ ≤ l41O2 t x₁ x₂ := by
    have h := fzc_W_le_R hs
    rwa [fzc_R_eq hs] at h
  have hK : twoCore t ≤ l41O2 t x₁ x₂ :=
    (le_sup_left : twoCore t ≤ ctxW t x₁ x₂).trans hWR
  have hT : wreathGrp x₁ x₂ lam ≤ l41O2 t x₁ x₂ ⊔ zpowers lam := by
    rw [wreathGrp]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_left
        (hWR (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
    · rw [hg]
      exact Subgroup.mem_sup_left
        (hWR (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
    · rw [hg]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  have hS : S ≤ l41O2 t x₁ x₂ ⊔ zpowers lam := by
    rw [hs.basic.S_eq]
    exact sup_le (hK.trans le_sup_left) hT
  rw [fzc_R_eq hs, l41V]
  apply le_antisymm
  · exact sup_le le_sup_left hS
  · refine sup_le le_sup_left ?_
    exact (Subgroup.zpowers_le.mpr (fzc_lam_mem_S hs)).trans le_sup_right

theorem fzc_decomp (hs : FzCSteps t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂) :
    ∃ o ∈ fzR t x₁ x₂, ∃ c ∈ closure ({rho, lam} : Set G), n = o * c := by
  have hCnorm : closure ({rho, lam} : Set G) ≤
      normalizer ((l41O2 t x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact fzc_normalizer_O2 hs (fzc_rho_mem_N hs)
    · exact fzc_normalizer_O2 hs (fzc_lam_mem_N hs)
  have hn' : n ∈ l41O2 t x₁ x₂ ⊔ closure ({rho, lam} : Set G) := by
    rw [← hs.N_eq]
    exact hn
  have hset : n ∈ ((l41O2 t x₁ x₂ : Subgroup G) : Set G) *
      ((closure ({rho, lam} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCnorm]
    exact hn'
  obtain ⟨o, ho, c, hc, hoc⟩ := Set.mem_mul.mp hset
  exact ⟨o, by rw [fzc_R_eq hs]; exact ho, c, hc, hoc.symm⟩

theorem fzc_S_le_N2 (hs : FzCSteps t L S x₁ x₂ lam rho) : S ≤ fzN2 t x₁ x₂ := by
  intro g hg
  unfold fzN2
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact hs.basic.normal_W.2 g hg k hk
  · intro hk
    have h' := hs.basic.normal_W.2 g⁻¹ (S.inv_mem hg) (g * k * g⁻¹) hk
    have e : g⁻¹ * (g * k * g⁻¹) * (g⁻¹)⁻¹ = k := by group
    rwa [e] at h'

theorem fzc_card_R (hs : FzCSteps t L S x₁ x₂ lam rho) :
    Nat.card (fzR t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂) := by
  rw [fzc_R_eq hs]
  exact hs.card_O2

theorem fzc_R_le_V (hs : FzCSteps t L S x₁ x₂ lam rho) : fzR t x₁ x₂ ≤ l41V S t x₁ x₂ := by
  rw [fzc_R_eq hs, l41V]
  exact le_sup_left

theorem fzc_V_isFzT2 (hs : FzCSteps t L S x₁ x₂ lam rho) :
    IsFzT2 t x₁ x₂ S (l41V S t x₁ x₂) where
  le_N2 := by rw [fzc_N2_eq hs]; exact hs.V_le
  isPGroup := hs.V_pGroup
  odd_relIndex := by rw [fzc_N2_eq hs]; exact hs.V_sylow
  S_le := le_sup_right

theorem fzc_lam_not_mem_R (hs : FzCSteps t L S x₁ x₂ lam rho) : lam ∉ fzR t x₁ x₂ := by
  intro h
  have hsup : fzR t x₁ x₂ ⊔ zpowers lam = fzR t x₁ x₂ :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr h)
  have hVeq : l41V S t x₁ x₂ = fzR t x₁ x₂ := by rw [fzc_V_eq hs, hsup]
  have hcard : Nat.card (l41V S t x₁ x₂) = Nat.card (fzR t x₁ x₂) := by rw [hVeq]
  rw [hs.card_V, fzc_card_R hs] at hcard
  have hW : 0 < Nat.card (ctxW t x₁ x₂) := Nat.card_pos
  omega

end CFSG.OddStandard.SmallF3.FritzII
