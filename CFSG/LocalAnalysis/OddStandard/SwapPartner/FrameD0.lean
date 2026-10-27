module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConj

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

@[expose] noncomputable def frameConj (ι : Perm (Fin 10) →* G) (c : Perm (Fin 10)) :
    Perm (Fin 10) →* G :=
  ι.comp (MulAut.conj c).toMonoidHom

theorem frameConj_apply (ι : Perm (Fin 10) →* G) (c σ : Perm (Fin 10)) :
    frameConj ι c σ = ι (c * σ * c⁻¹) := by
  simp only [frameConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem centData_frameConj (hC : CentData z ι) (c : Perm (Fin 10)) :
    CentData z (frameConj ι c) :=
  centData_comp_conj hC c

theorem isConj_z_frameConj_τ₀ (hC : CentData z ι) (hx : IsConj z (ι τ₀)) (c : Perm (Fin 10)) :
    IsConj z (frameConj ι c τ₀) := by
  have hτ : frameConj ι c τ₀ = ι c * ι τ₀ * (ι c)⁻¹ := by
    simp only [frameConj_apply, map_mul, map_inv]
  exact hx.trans (isConj_iff.2 ⟨ι c, hτ.symm⟩)

theorem not_isConj_z_mul_frameConj (hC : CentData z ι) (hP2 : ¬ IsConj z (z * ι τ₀))
    (c : Perm (Fin 10)) : ¬ IsConj z (z * frameConj ι c τ₀) := by
  intro h
  apply hP2
  have h1 : z * frameConj ι c τ₀ = ι c * (z * ι τ₀) * (ι c)⁻¹ := by
    simp only [frameConj_apply, map_mul, map_inv]
    calc z * (ι c * ι τ₀ * (ι c)⁻¹)
        = (z * ι c) * ι τ₀ * (ι c)⁻¹ := by group
      _ = (ι c * z) * ι τ₀ * (ι c)⁻¹ := by rw [hC.comm c]
      _ = ι c * (z * ι τ₀) * (ι c)⁻¹ := by group
  rw [h1] at h
  exact h.trans ((isConj_iff.2 ⟨ι c, rfl⟩).symm)

theorem pairOrder_frameConj (ι : Perm (Fin 10) →* G) (c : Perm (Fin 10)) :
    pairOrder (frameConj ι c τ₀) (frameConj ι c (swap 0 1)) =
      pairOrder (ι τ₀) (ι (swap 0 1)) := by
  have h1 : frameConj ι c τ₀ = ι c * ι τ₀ * (ι c)⁻¹ := by
    simp only [frameConj_apply, map_mul, map_inv]
  have h2 : frameConj ι c (swap 0 1) = ι c * ι (swap 0 1) * (ι c)⁻¹ := by
    simp only [frameConj_apply, map_mul, map_inv]
  rw [h1, h2]
  exact pairOrder_conj (ι c) (ι τ₀) (ι (swap 0 1))

@[expose] def cD₀ : Perm (Fin 10) := swap 0 8 * swap 1 9

@[expose] def cD₁ : Perm (Fin 10) := swap 2 8 * swap 3 9

theorem cD₀_mul_self : cD₀ * cD₀ = 1 := by
  decide

theorem cD₀_conj_τ₀ : cD₀ * τ₀ * cD₀⁻¹ = swap 0 1 := by
  decide

theorem cD₀_conj_swap : cD₀ * swap 0 1 * cD₀⁻¹ = τ₀ := by
  decide

theorem cD₁_conj_τ₀ : cD₁ * τ₀ * cD₁⁻¹ = swap 2 3 := by
  decide

private theorem liftS8_apply_castLE (ρ : Perm (Fin 8)) (j : Fin 8) :
    liftS8 ρ (Fin.castLE (by norm_num : 8 ≤ 10) j) =
      Fin.castLE (by norm_num : 8 ≤ 10) (ρ j) := by
  show ρ.viaEmbedding (Fin.castLEEmb (by norm_num : 8 ≤ 10))
      (Fin.castLE (by norm_num : 8 ≤ 10) j) = Fin.castLE (by norm_num : 8 ≤ 10) (ρ j)
  exact Equiv.Perm.viaEmbedding_apply ρ (Fin.castLEEmb (by norm_num : 8 ≤ 10)) j

private theorem liftS8_apply_castLE_self {ρ : Perm (Fin 8)} {j : Fin 8} (hj : ρ j = j) :
    liftS8 ρ (Fin.castLE (by norm_num : 8 ≤ 10) j) =
      Fin.castLE (by norm_num : 8 ≤ 10) j := by
  rw [liftS8_apply_castLE, hj]

private theorem liftS8_apply_zero {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0) :
    liftS8 ρ (0 : Fin 10) = 0 :=
  liftS8_apply_castLE_self (ρ := ρ) (j := (0 : Fin 8)) h0

private theorem liftS8_apply_one {ρ : Perm (Fin 8)} (h1 : ρ 1 = 1) :
    liftS8 ρ (1 : Fin 10) = 1 :=
  liftS8_apply_castLE_self (ρ := ρ) (j := (1 : Fin 8)) h1

private theorem liftS8_apply_two {ρ : Perm (Fin 8)} (h2 : ρ 2 = 2) :
    liftS8 ρ (2 : Fin 10) = 2 :=
  liftS8_apply_castLE_self (ρ := ρ) (j := (2 : Fin 8)) h2

private theorem liftS8_apply_three {ρ : Perm (Fin 8)} (h3 : ρ 3 = 3) :
    liftS8 ρ (3 : Fin 10) = 3 :=
  liftS8_apply_castLE_self (ρ := ρ) (j := (3 : Fin 8)) h3

theorem frameConj_cD₀_liftS8_of_fixed (ι : Perm (Fin 10) →* G) {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0)
    (h1 : ρ 1 = 1) : frameConj ι cD₀ (liftS8 ρ) = ι (liftS8 ρ) := by
  rw [frameConj_apply]
  congr 1
  have hdisj : Equiv.Perm.Disjoint cD₀ (liftS8 ρ) := by
    intro x
    fin_cases x
    · exact Or.inr (liftS8_apply_zero h0)
    · exact Or.inr (liftS8_apply_one h1)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inr (liftS8_apply_eight ρ)
    · exact Or.inr (liftS8_apply_nine ρ)
  rw [hdisj.commute.eq]
  group

theorem frameConj_cD₁_liftS8_of_fixed (ι : Perm (Fin 10) →* G) {ρ : Perm (Fin 8)} (h2 : ρ 2 = 2)
    (h3 : ρ 3 = 3) : frameConj ι cD₁ (liftS8 ρ) = ι (liftS8 ρ) := by
  rw [frameConj_apply]
  congr 1
  have hdisj : Equiv.Perm.Disjoint cD₁ (liftS8 ρ) := by
    intro x
    fin_cases x
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inr (liftS8_apply_two h2)
    · exact Or.inr (liftS8_apply_three h3)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inr (liftS8_apply_eight ρ)
    · exact Or.inr (liftS8_apply_nine ρ)
  rw [hdisj.commute.eq]
  group

end CFSG.OddStandard.AltStdSec.SwapPartner
