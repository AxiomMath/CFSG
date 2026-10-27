module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem O_subgroupOf_le_P (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    (ctxO t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) ≤
      (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) :=
  fun _ hx => O_le_ctxPL ha hx

private theorem subgroupOf_ctxPL_normal (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    ((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (normal_ctxPL ha).1]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => (normal_ctxPL ha).2 g hg p hp, fun hp => ?_⟩
  have h := (normal_ctxPL ha).2 g⁻¹ (inv_mem hg) (g * p * g⁻¹) hp
  rwa [show g⁻¹ * (g * p * g⁻¹) * (g⁻¹)⁻¹ = p by group] at h

private theorem ker_le_subgroupOf_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau)
    (σ : Sig4 t tau x₁ x₂) :
    σ.φ.ker ≤ (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) := by
  intro x hx
  exact O_subgroupOf_le_P ha (by rwa [σ.ker_eq] at hx)

private theorem card_P_eq (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    Nat.card (ctxPL t tau x₁ x₂) =
      Nat.card (((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).map σ.φ) *
        Nat.card (ctxO t tau x₁ x₂) := by
  let P' := (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)
  let N := P'.map σ.φ
  have hcardP' : Nat.card P' = Nat.card (ctxPL t tau x₁ x₂) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normal_ctxPL ha).1).toEquiv
  have hker : Nat.card (σ.φ.domRestrict P').ker = Nat.card (ctxO t tau x₁ x₂) := by
    rw [MonoidHom.ker_domRestrict, σ.ker_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (O_subgroupOf_le_P ha)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (O_le_LO t tau x₁ x₂)).toEquiv]
  have hrange : Nat.card (σ.φ.domRestrict P').range = Nat.card N := by
    rw [MonoidHom.domRestrict_range]
  have h := Subgroup.card_ker_mul_card_range (σ.φ.domRestrict P')
  rw [hker, hrange] at h
  rw [← hcardP']
  exact h.symm.trans (Nat.mul_comm _ _)

theorem phi_rho_three (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    σ.φ ⟨rho, rho_mem_LO ha⟩ ^ 3 = 1 ∧ σ.φ ⟨rho, rho_mem_LO ha⟩ ≠ 1 := by
  have h3 : rho ^ 3 = 1 := by
    rw [← ha.ord_rho]; exact pow_orderOf_eq_one rho
  constructor
  · have h : (⟨rho, rho_mem_LO ha⟩ : ↥(ctxLO t tau x₁ x₂)) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using h3
    rw [← map_pow, h, map_one]
  · intro h
    have hmem : ⟨rho, rho_mem_LO ha⟩ ∈ σ.φ.ker := by
      rw [MonoidHom.mem_ker]; exact h
    exact rho_not_mem_ctxPL ha (ker_le_subgroupOf_ctxPL ha σ hmem)

theorem map_ctxPL_eq_klein (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    ((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).map σ.φ = klein4 := by
  let P' := (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)
  let N := P'.map σ.φ
  have hPle : ctxPL t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1
  haveI hN : N.Normal := Subgroup.Normal.map (subgroupOf_ctxPL_normal ha) σ.φ σ.surj
  have hno_three : ∀ c ∈ N, c ^ 3 = 1 → c = 1 := by
    intro c hcN hc3
    by_contra hc1
    rw [Subgroup.mem_map] at hcN
    obtain ⟨p, hp, rfl⟩ := hcN
    obtain ⟨g, hg⟩ :=
      exists_conj_of_three hc3 hc1 (phi_rho_three ha σ).1 (phi_rho_three ha σ).2
    obtain ⟨x, hx⟩ := σ.surj g
    have heq : σ.φ (x * p * x⁻¹) = σ.φ ⟨rho, rho_mem_LO ha⟩ := by
      rw [map_mul, map_mul, map_inv, hx]
      exact hg
    have hxpx : x * p * x⁻¹ ∈ P' := (normal_ctxPL ha).2 (x : G) x.2 (p : G) hp
    have hker : (x * p * x⁻¹)⁻¹ * ⟨rho, rho_mem_LO ha⟩ ∈ σ.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    have hmem' : (x * p * x⁻¹)⁻¹ * ⟨rho, rho_mem_LO ha⟩ ∈ P' :=
      ker_le_subgroupOf_ctxPL ha σ hker
    have hrho' : (⟨rho, rho_mem_LO ha⟩ : ↥(ctxLO t tau x₁ x₂)) ∈ P' := by
      have hmul := P'.mul_mem hxpx hmem'
      rwa [show (x * p * x⁻¹) * ((x * p * x⁻¹)⁻¹ * ⟨rho, rho_mem_LO ha⟩) =
        ⟨rho, rho_mem_LO ha⟩ by group] at hmul
    exact rho_not_mem_ctxPL ha hrho'
  have hcard_ge : 4 ≤ Nat.card N := by
    have hl := ha.toCtx4L
    have hc := hl.toCtx4Q
    have hs := isSylSL34_of_Ctx4L hl
    have h6 : (ctxPL t tau x₁ x₂).relIndex (ctxLO t tau x₁ x₂) ≤ 6 :=
      relIndex_cent_le_six (fourGrp x₁ x₂) (ctxLO t tau x₁ x₂)
        (card_fourGrp hc) (fun h hh v hv => conj_V_of_mem_LO hc hs hh hv)
    have hrel : (ctxPL t tau x₁ x₂).relIndex (ctxLO t tau x₁ x₂) *
        Nat.card (ctxPL t tau x₁ x₂) = Nat.card (ctxLO t tau x₁ x₂) := by
      have h := Subgroup.relIndex_mul_card (H := ctxPL t tau x₁ x₂) (K := ctxLO t tau x₁ x₂)
      rwa [inf_eq_left.mpr hPle] at h
    have hcardP := card_P_eq ha σ
    have hineq : 3 * 2 ^ 11 ≤ 6 * (Nat.card N * 2 ^ 8) := by
      calc 3 * 2 ^ 11 = Nat.card (ctxLO t tau x₁ x₂) := (card_LO_of_sig ha σ).symm
        _ = (ctxPL t tau x₁ x₂).relIndex (ctxLO t tau x₁ x₂) *
              Nat.card (ctxPL t tau x₁ x₂) := hrel.symm
        _ ≤ 6 * Nat.card (ctxPL t tau x₁ x₂) := Nat.mul_le_mul_right _ h6
        _ = 6 * (Nat.card N * 2 ^ 8) := by rw [hcardP, hc.card_O]
    have h1 : 24 * 2 ^ 8 ≤ (6 * Nat.card N) * 2 ^ 8 := by
      calc 24 * 2 ^ 8 = 3 * 2 ^ 11 := by norm_num
        _ ≤ 6 * (Nat.card N * 2 ^ 8) := hineq
        _ = (6 * Nat.card N) * 2 ^ 8 := by ring
    have h2 : 24 ≤ 6 * Nat.card N := Nat.le_of_mul_le_mul_right h1 (by norm_num)
    have h3 : 4 * 6 ≤ Nat.card N * 6 := by
      calc 4 * 6 = 24 := by norm_num
        _ ≤ 6 * Nat.card N := h2
        _ = Nat.card N * 6 := by ring
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
  exact eq_klein4_of_normal N hno_three hcard_ge

theorem mem_ctxPL_iff (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) {g : G}
    (hg : g ∈ ctxLO t tau x₁ x₂) : g ∈ ctxPL t tau x₁ x₂ ↔ σ.φ ⟨g, hg⟩ ∈ klein4 := by
  constructor
  · intro hgP
    have hmem : (⟨g, hg⟩ : ↥(ctxLO t tau x₁ x₂)) ∈
        (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) :=
      Subgroup.mem_subgroupOf.mpr hgP
    have hmap : σ.φ ⟨g, hg⟩ ∈
        ((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).map σ.φ :=
      Subgroup.mem_map.mpr ⟨⟨g, hg⟩, hmem, rfl⟩
    simpa [map_ctxPL_eq_klein ha σ] using hmap
  · intro hk
    have hmap : σ.φ ⟨g, hg⟩ ∈
        ((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).map σ.φ := by
      rwa [map_ctxPL_eq_klein ha σ]
    rw [Subgroup.mem_map] at hmap
    obtain ⟨p, hp, hpeq⟩ := hmap
    have hker : p⁻¹ * ⟨g, hg⟩ ∈ σ.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpeq, inv_mul_cancel]
    have hmem' : p⁻¹ * ⟨g, hg⟩ ∈
        (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) :=
      ker_le_subgroupOf_ctxPL ha σ hker
    have hmul := ((ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)).mul_mem hp hmem'
    have hmem : (⟨g, hg⟩ : ↥(ctxLO t tau x₁ x₂)) ∈
        (ctxPL t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) := by
      rwa [show p * (p⁻¹ * ⟨g, hg⟩) = ⟨g, hg⟩ by group] at hmul
    exact hmem

theorem card_ctxPL_sig (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    Nat.card (ctxPL t tau x₁ x₂) = 2 ^ 10 := by
  have hc := ha.toCtx4L.toCtx4Q
  rw [card_P_eq ha σ, map_ctxPL_eq_klein ha σ, card_klein4, hc.card_O]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
