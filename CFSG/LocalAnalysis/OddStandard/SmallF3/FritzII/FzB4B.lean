module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzbs_lam_not_conj
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) (g : G) :
    g * lam * g⁻¹ ≠ t * lam := by
  intro hg
  have hlamL : lam ∈ L := (S4A.generators_mem_L h.toCtx0).2.2
  have hlam2 : lam * lam = 1 := by
    rw [← pow_two, ← h.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have hlam1 : lam ≠ 1 := by
    intro h1
    have h2 := h.wreath.ord_lam
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, hcL, hc⟩ := h.invol_L lam hlamL hlam2 hlam1
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  obtain ⟨n, -, hn⟩ := fzbs_exists_swap h hz
  have hctc : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer c hcL]
    group
  apply fzbs_not_conj_Z h ((g * c)⁻¹ * (c * n)) hz
  generalize (x₁ * x₂) ^ 2 = z at hc hn
  calc (g * c)⁻¹ * (c * n) * t * ((g * c)⁻¹ * (c * n))⁻¹
      = (g * c)⁻¹ * (c * (n * t * n⁻¹) * c⁻¹) * (g * c) := by group
    _ = (g * c)⁻¹ * ((c * t * c⁻¹) * (c * z * c⁻¹)) * (g * c) := by rw [hn]; group
    _ = (g * c)⁻¹ * (g * lam * g⁻¹) * (g * c) := by rw [hctc, hc, hg]
    _ = c⁻¹ * lam * c := by group
    _ = z := by rw [← hc]; group

theorem fzbs_W_le_R (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) : ctxW t x₁ x₂ ≤ fzR t x₁ x₂ := by
  intro w hw
  obtain ⟨hg, hfg⟩ := (fzl_W_mem_iff hF w).mp hw
  refine (fzbs_R_mem_iff h hF w).mpr ⟨Subgroup.le_normalizer hw, ?_⟩
  rw [show (⟨w, Subgroup.le_normalizer hw⟩ : ↥(fzN2 t x₁ x₂)) = ⟨w, hg⟩ from
    Subtype.ext rfl, hfg]
  exact fzlK8.one_mem

theorem fzbs_Wtau_cases (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {g : G} (hg : g ∈ ctxW t x₁ x₂ ⊔ zpowers tau) :
    g ∈ ctxW t x₁ x₂ ∨ g * tau⁻¹ ∈ ctxW t x₁ x₂ := by
  obtain ⟨htauW, hcard⟩ := fzbs_card_Wtau h hK
  have hcard' : Nat.card (ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) =
      2 * Nat.card (ctxW t x₁ x₂) := by
    rw [hcard, fzbs_card_W h hK]
  rcases fzl_index_two_cosets le_sup_left hcard' (mem_sup_right (mem_zpowers tau)) htauW
    g⁻¹ (inv_mem hg) with h1 | h1
  · left
    simpa using inv_mem h1
  · right
    have h2 : g * tau ∈ ctxW t x₁ x₂ := by simpa [mul_inv_rev] using inv_mem h1
    have h3 : tau ^ 2 ∈ ctxW t x₁ x₂ := (le_sup_left : twoCore t ≤ _) h.tau_sq_mem
    rw [show g * tau⁻¹ = (g * tau) * (tau ^ 2)⁻¹ by group]
    exact mul_mem h2 (inv_mem h3)

theorem fzbs_rho_K (h : Ctx t L S x₁ x₂ lam rho tau) {k : G} (hk : k ∈ twoCore t) :
    rho * k * rho⁻¹ = k := by
  rw [← h.cent_rho] at hk
  rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 rho (Set.mem_singleton rho)]
  group

theorem fzbs_rho_W_fix (h : Ctx t L S x₁ x₂ lam rho tau) {w : G} (hw : w ∈ ctxW t x₁ x₂)
    (hfix : rho * w * rho⁻¹ = w) : w ∈ twoCore t := by
  rw [← h.cent_rho]
  refine Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  rw [Set.mem_singleton_iff.mp hg]
  calc rho * w = rho * w * rho⁻¹ * rho := by group
    _ = w * rho := by rw [hfix]

theorem fzbs_lam_K (h : Ctx t L S x₁ x₂ lam rho tau) {k : G} (hk : k ∈ twoCore t) :
    lam * k * lam⁻¹ = k := by
  rw [← S4A.twoCore_commute h.hyp k hk lam (S4A.generators_mem_L h.toCtx0).2.2]
  group

end CFSG.OddStandard.SmallF3.FritzII
