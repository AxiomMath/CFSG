module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConjData
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.ConsistencyBasic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

variable {ι₁ : Perm (Fin 10) →* G} {ε χ : Perm (Fin 8) →* ℤˣ}

private theorem x1_mul_self : ι τ₀ * ι τ₀ = (1 : G) := by
  rw [← map_mul, τ₀_mul_self, map_one]

private theorem coord_one_one (D : TwistData z ι ι₁ ε χ) {ρ : Perm (Fin 8)}
    (hρ : ρ * ρ = 1) (hε : ε ρ = 1) (hχ : χ ρ = 1) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧
      Multiset.card σ.cycleType = Multiset.card ρ.cycleType ∧ ι (liftS8 ρ) = ι₁ σ := by
  obtain ⟨σ, hσ, hcard, hcoord⟩ := D.coord ρ hρ
  refine ⟨σ, hσ, ?_, ?_⟩
  · have h : Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 0 := by
      rw [hcard, hε, if_neg (by decide : ¬ ((1 : ℤˣ) = -1)), add_zero]
    simpa using h
  · have h : ι (liftS8 ρ) = ι₁ σ := by
      rw [hcoord, hχ, if_pos rfl, one_mul]
    exact h

private theorem coord_one_ne (D : TwistData z ι ι₁ ε χ) {ρ : Perm (Fin 8)}
    (hρ : ρ * ρ = 1) (hε : ε ρ = 1) (hχ : χ ρ ≠ 1) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧
      Multiset.card σ.cycleType = Multiset.card ρ.cycleType ∧
      ι (liftS8 ρ) = ι τ₀ * ι₁ σ := by
  obtain ⟨σ, hσ, hcard, hcoord⟩ := D.coord ρ hρ
  refine ⟨σ, hσ, ?_, ?_⟩
  · have h : Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 0 := by
      rw [hcard, hε, if_neg (by decide : ¬ ((1 : ℤˣ) = -1)), add_zero]
    simpa using h
  · have h : ι (liftS8 ρ) = ι τ₀ * ι₁ σ := by
      rw [hcoord, if_neg hχ]
    exact h

private theorem coord_neg_one (D : TwistData z ι ι₁ ε χ) {ρ : Perm (Fin 8)}
    (hρ : ρ * ρ = 1) (hε : ε ρ = -1) (hχ : χ ρ = 1) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧
      Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 1 ∧ ι (liftS8 ρ) = ι₁ σ := by
  obtain ⟨σ, hσ, hcard, hcoord⟩ := D.coord ρ hρ
  refine ⟨σ, hσ, ?_, ?_⟩
  · have h : Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 1 := by
      rw [hcard, hε, if_pos rfl]
    exact h
  · have h : ι (liftS8 ρ) = ι₁ σ := by
      rw [hcoord, hχ, if_pos rfl, one_mul]
    exact h

private theorem coord_neg_ne (D : TwistData z ι ι₁ ε χ) {ρ : Perm (Fin 8)}
    (hρ : ρ * ρ = 1) (hε : ε ρ = -1) (hχ : χ ρ ≠ 1) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧
      Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 1 ∧
      ι (liftS8 ρ) = ι τ₀ * ι₁ σ := by
  obtain ⟨σ, hσ, hcard, hcoord⟩ := D.coord ρ hρ
  refine ⟨σ, hσ, ?_, ?_⟩
  · have h : Multiset.card σ.cycleType = Multiset.card ρ.cycleType + 1 := by
      rw [hcard, hε, if_pos rfl]
    exact h
  · have h : ι (liftS8 ρ) = ι τ₀ * ι₁ σ := by
      rw [hcoord, if_neg hχ]
    exact h

theorem eps_eq_sign (hC : CentData z ι) (hx : IsConj z (ι τ₀)) (hP1 : IsConj z (z * ι τ₀))
    (D : TwistData z ι ι₁ ε χ) : ε = sign := by
  rcases D.eps with hε1 | hεs
  · exfalso
    have hεr : ε r₁' = 1 := by rw [hε1]; rfl
    have hP1' : IsConj z (ι τ₀ * z) := by rw [← hC.comm τ₀]; exact hP1
    have hnot : ¬ IsConj z (ι (r₁ * τ₀)) := not_isConj_ι_of_sq hC exists_sq_r₁_mul_τ₀
    by_cases hχ1 : χ r₁' = 1
    · obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_one_one D r₁'_mul_self hεr hχ1
      have hcard1 : Multiset.card σ.cycleType = 1 := by
        rw [hcard, card_cycleType_r₁']
      have hir₁ : ι r₁ = ι₁ σ := by
        have h := hcoord
        rwa [liftS8_r₁'] at h
      have hswap : σ.IsSwap := isSwap_of_card_cycleType_eq_one hσ hcard1
      have hconj : IsConj z (ι (r₁ * τ₀)) := by
        rw [map_mul, hir₁, ← D.cent.comm σ]
        exact isConj_mul_ι₁_of_isSwap D.cent D.swap hP1' hswap
      exact hnot hconj
    · obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_one_ne D r₁'_mul_self hεr hχ1
      have hcard1 : Multiset.card σ.cycleType = 1 := by
        rw [hcard, card_cycleType_r₁']
      have hir₁ : ι r₁ = ι τ₀ * ι₁ σ := by
        have h := hcoord
        rwa [liftS8_r₁'] at h
      have hswap : σ.IsSwap := isSwap_of_card_cycleType_eq_one hσ hcard1
      have hconj : IsConj z (ι (r₁ * τ₀)) := by
        have heq : ι (r₁ * τ₀) = ι₁ σ := by
          rw [map_mul, hir₁]
          calc (ι τ₀ * ι₁ σ) * ι τ₀ = ι τ₀ * (ι₁ σ * ι τ₀) := by group
            _ = ι τ₀ * (ι τ₀ * ι₁ σ) := by rw [D.cent.comm σ]
            _ = (ι τ₀ * ι τ₀) * ι₁ σ := by group
            _ = ι₁ σ := by rw [x1_mul_self, one_mul]
        rw [heq]
        exact isConj_ι₁_of_isSwap D.swap hswap
      exact hnot hconj
  · exact hεs

theorem chi_eq_sign (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (D : TwistData z ι ι₁ ε χ) (hε : ε = sign) : χ = sign := by
  rcases D.chi with hχ1 | hχs
  · exfalso
    have hεr : ε r₁' = -1 := by rw [hε, sign_r₁']
    have hχr : χ r₁' = 1 := by rw [hχ1]; rfl
    obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_neg_one D r₁'_mul_self hεr hχr
    have hcard2 : Multiset.card σ.cycleType = 2 := by
      rw [hcard, card_cycleType_r₁']
    have hir₁ : ι r₁ = ι₁ σ := by
      have h := hcoord
      rwa [liftS8_r₁'] at h
    have hsignσ : sign σ = 1 := by
      rw [CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hσ, hcard2]
      decide
    have hσr₂ : IsConj σ r₂ := (isConj_rep_of_card_cycleType hσ).2.1 hcard2
    have hr₁swap : r₁.IsSwap := ⟨0, 1, by decide, rfl⟩
    have hι₁σ : IsConj z (ι₁ σ) := by
      have h := isConj_ι_of_isSwap hC hx hr₁swap
      rwa [hir₁] at h
    have hισ : IsConj z (ι σ) := (D.even_zero σ hsignσ).1 hι₁σ
    have hιr₂ : IsConj z (ι r₂) := (isConj_ι_iff hC hσr₂).1 hισ
    exact not_isConj_ι_of_sq hC (σ := r₂) exists_sq_r₂ hιr₂
  · exact hχs

theorem isConj_z_mul_r₂ (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (D : TwistData z ι ι₁ ε χ) (hε : ε = sign) (hχ : χ = sign) : IsConj z (z * ι r₂) := by
  have hεr : ε r₁' = -1 := by rw [hε, sign_r₁']
  have hχr : χ r₁' ≠ 1 := by rw [hχ, sign_r₁']; decide
  obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_neg_ne D r₁'_mul_self hεr hχr
  have hcard2 : Multiset.card σ.cycleType = 2 := by
    rw [hcard, card_cycleType_r₁']
  have hir₁ : ι r₁ = ι τ₀ * ι₁ σ := by
    have h := hcoord
    rwa [liftS8_r₁'] at h
  have hsignσ : sign σ = 1 := by
    rw [CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hσ, hcard2]
    decide
  have hσr₂ : IsConj σ r₂ := (isConj_rep_of_card_cycleType hσ).2.1 hcard2
  have hr₁swap : r₁.IsSwap := ⟨0, 1, by decide, rfl⟩
  have hιτσ : IsConj z (ι τ₀ * ι₁ σ) := by
    have h := isConj_ι_of_isSwap hC hx hr₁swap
    rwa [hir₁] at h
  have hzισ : IsConj z (z * ι σ) := (D.even_one σ hsignσ).1 hιτσ
  exact (isConj_z_mul_ι_iff hC hσr₂).1 hzισ

theorem isConj_ι_r₃ (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (D : TwistData z ι ι₁ ε χ) (hε : ε = sign) (hχ : χ = sign) : IsConj z (ι r₃) := by
  have h2 : IsConj z (z * ι r₂) := isConj_z_mul_r₂ hC hx D hε hχ
  have hεr : ε r₂' = 1 := by rw [hε, sign_r₂']
  have hχr : χ r₂' = 1 := by rw [hχ, sign_r₂']
  obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_one_one D r₂'_mul_self hεr hχr
  have hcard2 : Multiset.card σ.cycleType = 2 := by
    rw [hcard, card_cycleType_r₂']
  have hir₂ : ι r₂ = ι₁ σ := by
    have h := hcoord
    rwa [liftS8_r₂'] at h
  have hsignσ : sign σ = 1 := by
    rw [CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hσ, hcard2]
    decide
  have hσr₂ : IsConj σ r₂ := (isConj_rep_of_card_cycleType hσ).2.1 hcard2
  have hzισ : IsConj z (z * ι σ) := (isConj_z_mul_ι_iff hC hσr₂).2 h2
  have hιτσ : IsConj z (ι τ₀ * ι₁ σ) := (D.even_one σ hsignσ).2 hzισ
  have htr : IsConj z (ι (τ₀ * r₂)) := by
    rw [map_mul, hir₂]
    exact hιτσ
  have hr₃2 : r₃ * r₃ = 1 := by
    rw [← liftS8_r₃', ← map_mul, r₃'_mul_self, map_one]
  have hcard₃ : Multiset.card r₃.cycleType = 3 := by
    rw [← liftS8_r₃', cycleType_liftS8, card_cycleType_r₃']
  have hconjrep : IsConj r₃ (τ₀ * r₂) := (isConj_rep_of_card_cycleType hr₃2).2.2.1 hcard₃
  exact (isConj_ι_iff hC hconjrep).2 htr

theorem isConj_z_mul_ρ₄ [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP1 : IsConj z (z * ι τ₀)) : IsConj z (z * ι ρ₄) := by
  obtain ⟨ι₁', ε', χ', D⟩ := exists_twistData hC hx
  have hε : ε' = sign := eps_eq_sign hC hx hP1 D
  have hχ : χ' = sign := chi_eq_sign hC hx D hε
  have h3 : IsConj z (ι r₃) := isConj_ι_r₃ hC hx D hε hχ
  have hεr : ε' r₃' = -1 := by rw [hε, sign_r₃']
  have hχr : χ' r₃' ≠ 1 := by rw [hχ, sign_r₃']; decide
  obtain ⟨σ, hσ, hcard, hcoord⟩ := coord_neg_ne D r₃'_mul_self hεr hχr
  have hcard4 : Multiset.card σ.cycleType = 4 := by
    rw [hcard, card_cycleType_r₃']
  have hir₃ : ι r₃ = ι τ₀ * ι₁' σ := by
    have h := hcoord
    rwa [liftS8_r₃'] at h
  have hsignσ : sign σ = 1 := by
    rw [CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hσ, hcard4]
    decide
  have hσρ₄ : IsConj σ ρ₄ := (isConj_rep_of_card_cycleType hσ).2.2.2.1 hcard4
  have hιτσ : IsConj z (ι τ₀ * ι₁' σ) := by
    have h := h3
    rwa [hir₃] at h
  have hzισ : IsConj z (z * ι σ) := (D.even_one σ hsignσ).1 hιτσ
  exact (isConj_z_mul_ι_iff hC hσρ₄).1 hzισ

end CFSG.OddStandard.AltStdSec.SwapPartner
