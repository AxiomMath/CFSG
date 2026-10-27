module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AtX1
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConjCoord
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConj2

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G}

structure TwistData (z : G) (ι ι₁ : Perm (Fin 10) →* G) (ε χ : Perm (Fin 8) →* ℤˣ) : Prop where
  cent : CentData (ι τ₀) ι₁
  swap : ι₁ τ₀ = z
  even_zero : ∀ σ, sign σ = 1 → (IsConj z (ι₁ σ) ↔ IsConj z (ι σ))
  even_one : ∀ σ, sign σ = 1 → (IsConj z (ι τ₀ * ι₁ σ) ↔ IsConj z (z * ι σ))
  eps : ε = 1 ∨ ε = sign
  chi : χ = 1 ∨ χ = sign
  coord : ∀ ρ : Perm (Fin 8), ρ * ρ = 1 → ∃ σ : Perm (Fin 10), σ * σ = 1 ∧
    Multiset.card σ.cycleType = Multiset.card ρ.cycleType + (if ε ρ = -1 then 1 else 0) ∧
    ι (liftS8 ρ) = (if χ ρ = 1 then 1 else ι τ₀) * ι₁ σ
  pair_one : ∀ ρ : Perm (Fin 8), ρ * ρ = 1 → pairOrder (ι τ₀) (ι (liftS8 ρ)) =
    N10 (Multiset.card ρ.cycleType + (if ε ρ = -1 then 1 else 0))
  pair_z : ∀ ρ : Perm (Fin 8), ρ * ρ = 1 → pairOrder (ι τ₀) (z * ι (liftS8 ρ)) =
    N10 (Multiset.card ρ.cycleType + (if ε ρ = -1 then 0 else 1))

variable [Finite G] {ι : Perm (Fin 10) →* G}

private theorem liftS8_mul_self_of_mul_self {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    liftS8 ρ * liftS8 ρ = 1 := by
  rw [← map_mul, hρ, map_one]

theorem exists_twistData (hC : CentData z ι) (hx : IsConj z (ι τ₀)) :
    ∃ (ι₁ : Perm (Fin 10) →* G) (ε χ : Perm (Fin 8) →* ℤˣ), TwistData z ι ι₁ ε χ := by
  obtain ⟨ι₁, hC₁, h1τ, e0, e1⟩ := exists_frame_at_x hC hx
  obtain ⟨π, κ, hS, hκ, hc1, hc2⟩ := exists_coord_homs hC₁
  have hOS : OneSided z ι (ι τ₀) π :=
    { eq := rfl
      sec := hS
      swap := fun hz => (hc1 τ₀ ⟨z, hz⟩ h1τ.symm).1 }
  obtain ⟨ε, χ, hε, hχ, hmain⟩ := twist_facts_conj hC hOS κ
  have hx2 : (ι τ₀) * (ι τ₀) = 1 := by rw [← map_mul, τ₀_mul_self, map_one]
  have hx1 : (ι τ₀) ≠ 1 := by
    intro h
    have h' : ι τ₀ = ι 1 := by rw [h, map_one]
    exact absurd (hC.inj h') (by decide)
  refine ⟨ι₁, ε, χ, hC₁, h1τ, e0, e1, hε, hχ, ?_, ?_, ?_⟩
  · intro ρ hρ
    have hρx : ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) := ι_liftS8_mem_centralizer ι ρ
    have hzρ : z * ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) :=
      z_mul_liftS8_mem_centralizer hC hOS ρ
    obtain ⟨hκc, hcyc⟩ := hmain ρ hρx hzρ
    have hcc : (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))) *
        ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      show ι (liftS8 ρ) * ι (liftS8 ρ) = 1
      rw [← map_mul, liftS8_mul_self_of_mul_self hρ, map_one]
    have hπc : π ⟨ι (liftS8 ρ), hρx⟩ * π ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
      rw [← map_mul, hcc, map_one]
    refine ⟨π ⟨ι (liftS8 ρ), hρx⟩, hπc, (hcyc hρ).1, ?_⟩
    obtain ⟨σ', hσ'⟩ :=
      hC₁.cases (ι (liftS8 ρ))
        (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))).2
    rcases hσ' with hσ' | hσ'
    · have h1 : π ⟨ι (liftS8 ρ), hρx⟩ = σ' := (hc1 σ' _ hσ').1
      have hχ1 : χ ρ = 1 := by rw [← hκc, (hc1 σ' _ hσ').2]
      rw [if_pos hχ1, one_mul]
      calc ι (liftS8 ρ)
          = ((⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))) : G) := rfl
        _ = ι₁ σ' := hσ'
        _ = ι₁ (π ⟨ι (liftS8 ρ), hρx⟩) := by rw [h1]
    · have h1 : π ⟨ι (liftS8 ρ), hρx⟩ = σ' := (hc2 σ' _ hσ').1
      have hχ1 : χ ρ ≠ 1 := by
        intro hχe
        have hc : κ (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))) = 1 := by
          rw [hκc, hχe]
        rw [(hc2 σ' _ hσ').2] at hc
        exact absurd hc (by decide)
      rw [if_neg hχ1]
      calc ι (liftS8 ρ)
          = ((⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))) : G) := rfl
        _ = (ι τ₀) * ι₁ σ' := hσ'
        _ = (ι τ₀) * ι₁ (π ⟨ι (liftS8 ρ), hρx⟩) := by rw [h1]
  · intro ρ hρ
    have hρx : ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) := ι_liftS8_mem_centralizer ι ρ
    have hzρ : z * ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) :=
      z_mul_liftS8_mem_centralizer hC hOS ρ
    obtain ⟨-, hcyc⟩ := hmain ρ hρx hzρ
    have hcc : (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G))) *
        ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      show ι (liftS8 ρ) * ι (liftS8 ρ) = 1
      rw [← map_mul, liftS8_mul_self_of_mul_self hρ, map_one]
    have hπc : π ⟨ι (liftS8 ρ), hρx⟩ * π ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
      rw [← map_mul, hcc, map_one]
    have hpair := SymSec.card_inf_centralizer hS hκ hx2 hx1
      (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({ι τ₀} : Set G)))
    rw [pairOrder, hpair, two_mul_card_centralizer_perm_ten hπc, (hcyc hρ).1]
  · intro ρ hρ
    have hρx : ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) := ι_liftS8_mem_centralizer ι ρ
    have hzρ : z * ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) :=
      z_mul_liftS8_mem_centralizer hC hOS ρ
    obtain ⟨-, hcyc⟩ := hmain ρ hρx hzρ
    have hzρ2 : (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({ι τ₀} : Set G))) *
        ⟨z * ι (liftS8 ρ), hzρ⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      show (z * ι (liftS8 ρ)) * (z * ι (liftS8 ρ)) = 1
      calc (z * ι (liftS8 ρ)) * (z * ι (liftS8 ρ))
          = z * (ι (liftS8 ρ) * z) * ι (liftS8 ρ) := by group
        _ = z * (z * ι (liftS8 ρ)) * ι (liftS8 ρ) := by rw [hC.comm (liftS8 ρ)]
        _ = (z * z) * (ι (liftS8 ρ) * ι (liftS8 ρ)) := by group
        _ = ι (liftS8 ρ) * ι (liftS8 ρ) := by rw [hC.mul_self, one_mul]
        _ = ι (liftS8 ρ * liftS8 ρ) := by rw [map_mul]
        _ = 1 := by rw [liftS8_mul_self_of_mul_self hρ, map_one]
    have hπz : π ⟨z * ι (liftS8 ρ), hzρ⟩ * π ⟨z * ι (liftS8 ρ), hzρ⟩ = 1 := by
      rw [← map_mul, hzρ2, map_one]
    have hpair := SymSec.card_inf_centralizer hS hκ hx2 hx1
      (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({ι τ₀} : Set G)))
    rw [pairOrder, hpair, two_mul_card_centralizer_perm_ten hπz, (hcyc hρ).2]

end CFSG.OddStandard.AltStdSec.SwapPartner
