module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem mem_O_of_phi_eq_one (ha : Ctx4A t L S x₁ x₂ lam rho tau)
    (σ : Sig4 t tau x₁ x₂) {g : G} (hg : g ∈ ctxLO t tau x₁ x₂)
    (h : σ.φ ⟨g, hg⟩ = 1) : g ∈ ctxO t tau x₁ x₂ := by
  have hker : (⟨g, hg⟩ : ↥(ctxLO t tau x₁ x₂)) ∈ σ.φ.ker := MonoidHom.mem_ker.mpr h
  rw [σ.ker_eq] at hker
  exact Subgroup.mem_subgroupOf.mp hker

theorem P_quot_sig (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    (∀ p ∈ ctxPL t tau x₁ x₂, p ^ 2 ∈ ctxO t tau x₁ x₂) ∧
      ∀ p ∈ ctxPL t tau x₁ x₂, ∀ q ∈ ctxPL t tau x₁ x₂,
        p * q * p⁻¹ * q⁻¹ ∈ ctxO t tau x₁ x₂ := by
  constructor
  · intro p hp
    have hpL : p ∈ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1 hp
    have hφp : σ.φ ⟨p, hpL⟩ ∈ klein4 := (mem_ctxPL_iff ha σ hpL).mp hp
    have hsq : σ.φ ⟨p * p, mul_mem hpL hpL⟩ = 1 := by
      have h1 : (⟨p * p, mul_mem hpL hpL⟩ : ↥(ctxLO t tau x₁ x₂)) =
          ⟨p, hpL⟩ * ⟨p, hpL⟩ := Subtype.ext rfl
      rw [h1, map_mul]
      exact klein4_sq hφp
    have : p * p ∈ ctxO t tau x₁ x₂ :=
      mem_O_of_phi_eq_one ha σ (mul_mem hpL hpL) hsq
    simpa [pow_two] using this
  · intro p hp q hq
    have hpL : p ∈ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1 hp
    have hqL : q ∈ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1 hq
    have hφp : σ.φ ⟨p, hpL⟩ ∈ klein4 := (mem_ctxPL_iff ha σ hpL).mp hp
    have hφq : σ.φ ⟨q, hqL⟩ ∈ klein4 := (mem_ctxPL_iff ha σ hqL).mp hq
    have hcommL : p * q * p⁻¹ * q⁻¹ ∈ ctxLO t tau x₁ x₂ :=
      mul_mem (mul_mem (mul_mem hpL hqL) (inv_mem hpL)) (inv_mem hqL)
    have hphi : σ.φ ⟨p * q * p⁻¹ * q⁻¹, hcommL⟩ = 1 := by
      have h1 : (⟨p * q * p⁻¹ * q⁻¹, hcommL⟩ : ↥(ctxLO t tau x₁ x₂)) =
          ⟨p, hpL⟩ * ⟨q, hqL⟩ * ⟨p, hpL⟩⁻¹ * ⟨q, hqL⟩⁻¹ := Subtype.ext rfl
      rw [h1]
      simp only [map_mul, map_inv]
      have hcommφ : σ.φ ⟨p, hpL⟩ * σ.φ ⟨q, hqL⟩ = σ.φ ⟨q, hqL⟩ * σ.φ ⟨p, hpL⟩ :=
        klein4_comm hφp hφq
      rw [hcommφ]
      group
    exact mem_O_of_phi_eq_one ha σ hcommL hphi

theorem CP_rho_sig (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    ctxPL t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau} := by
  have hc := ha.toCtx4L.toCtx4Q
  ext x
  constructor
  · intro hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ ctxLO t tau x₁ x₂ := (normal_ctxPL ha).1 hxP
    have hφx : σ.φ ⟨x, hxL⟩ ∈ klein4 := (mem_ctxPL_iff ha σ hxL).mp hxP
    have hxrho : x * rho = rho * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hcomm : σ.φ ⟨x, hxL⟩ * σ.φ ⟨rho, rho_mem_LO ha⟩ =
        σ.φ ⟨rho, rho_mem_LO ha⟩ * σ.φ ⟨x, hxL⟩ := by
      have h := congrArg σ.φ (Subtype.ext hxrho :
        (⟨x, hxL⟩ * ⟨rho, rho_mem_LO ha⟩ : ↥(ctxLO t tau x₁ x₂)) =
          ⟨rho, rho_mem_LO ha⟩ * ⟨x, hxL⟩)
      simpa only [map_mul] using h
    have hxO : x ∈ ctxO t tau x₁ x₂ :=
      mem_O_of_phi_eq_one ha σ hxL
        (eq_one_of_mem_klein4_cent_three (phi_rho_three ha σ).1 (phi_rho_three ha σ).2
          hφx hcomm)
    have hxCO : x ∈ ctxCO t tau x₁ x₂ rho := by
      show x ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G)
      exact ⟨hxO, hxC⟩
    rw [hc.CO_rho] at hxCO
    exact hxCO
  · intro hx
    have htC : t ∈ ctxCO t tau x₁ x₂ rho := by
      rw [hc.CO_rho]; exact Subgroup.subset_closure (by simp)
    have htauC : tau ∈ ctxCO t tau x₁ x₂ rho := by
      rw [hc.CO_rho]; exact Subgroup.subset_closure (by simp)
    have htO : t ∈ ctxO t tau x₁ x₂ :=
      (Subgroup.mem_inf.mp (by simpa [ctxCO] using htC)).1
    have htCent : t ∈ centralizer ({rho} : Set G) :=
      (Subgroup.mem_inf.mp (by simpa [ctxCO] using htC)).2
    have htauO : tau ∈ ctxO t tau x₁ x₂ :=
      (Subgroup.mem_inf.mp (by simpa [ctxCO] using htauC)).1
    have htauCent : tau ∈ centralizer ({rho} : Set G) :=
      (Subgroup.mem_inf.mp (by simpa [ctxCO] using htauC)).2
    have hsub : ({t, tau} : Set G) ⊆
        (ctxPL t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) : Subgroup G) := by
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨O_le_ctxPL ha htO, htCent⟩
      · exact ⟨O_le_ctxPL ha htauO, htauCent⟩
    exact (Subgroup.closure_le _).mpr hsub hx

theorem X_not_normal_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    ¬ NormalIn (ctxX t tau x₁ x₂) (ctxPL t tau x₁ x₂) := by
  have hc := ha.toCtx4L.toCtx4Q
  rintro ⟨-, hnorm⟩
  have hle : ctxPL t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
    intro g hg
    rw [ctxM, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnorm g hg h hh
    · intro hh
      have hg' : g⁻¹ ∈ ctxPL t tau x₁ x₂ := inv_mem hg
      have h2 := hnorm g⁻¹ hg' (g * h * g⁻¹) hh
      rwa [show g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h by group] at h2
  have hdvd : Nat.card (ctxPL t tau x₁ x₂) ∣ Nat.card (ctxM t tau x₁ x₂) :=
    Subgroup.card_dvd_of_le hle
  rw [card_ctxPL_sig ha σ, hc.card_M] at hdvd
  norm_num at hdvd

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
