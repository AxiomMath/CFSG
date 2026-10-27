module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapRetract

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem isConj_conj_iff {H : Type} [Group H] (z c w : H) :
    IsConj z (c * w * c⁻¹) ↔ IsConj z w := by
  constructor
  · intro h
    exact h.trans (isConj_iff.2 ⟨c⁻¹, by group⟩)
  · intro h
    exact h.trans (isConj_iff.2 ⟨c, rfl⟩)

private theorem pairOrder_z_ι' (hC : CentData z ι) {σ : Perm (Fin 10)} (hσ : σ * σ = 1) :
    pairOrder z (ι σ) = N10 (Multiset.card σ.cycleType) := by
  rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ]

theorem N10_eq_one_iff {k : ℕ} (hk : k ≤ 5) : N10 k = N10 1 ↔ k = 1 := by
  interval_cases k <;> norm_num [N10, Nat.factorial]

theorem exists_frame_of_pairOrder {x y : G} {ι₀ : Perm (Fin 10) →* G} (hC : CentData x ι₀)
    (hy : y ∈ centralizer ({x} : Set G)) (hy2 : y * y = 1) (hord : pairOrder x y = N10 1) :
    ∃ (ι₁ : Perm (Fin 10) →* G) (d : Perm (Fin 10)), CentData x ι₁ ∧ ι₁ τ₀ = y ∧
      ∀ σ, sign σ = 1 → ι₁ σ = ι₀ (d * σ * d⁻¹) := by
  obtain ⟨σ₀, hσ₀ | hσ₀⟩ := hC.cases y hy
  ·
    have hsq : σ₀ * σ₀ = 1 := hC.inj (by rw [map_mul, ← hσ₀, hy2, map_one])
    have hcard : Multiset.card σ₀.cycleType = 1 :=
      (N10_eq_one_iff (card_cycleType_le_five hsq)).1 (by
        rw [← pairOrder_z_ι' hC hsq, ← hσ₀]
        exact hord)
    obtain ⟨a, b, hab, hσ₀eq⟩ := isSwap_of_card_cycleType_eq_one hsq hcard
    have hconj : IsConj τ₀ σ₀ := by
      rw [hσ₀eq, τ₀]
      exact isConj_comm.1 (Equiv.Perm.isConj_swap hab (by decide))
    obtain ⟨d, hd⟩ := isConj_iff.1 hconj
    refine ⟨ι₀.comp (MulAut.conj d).toMonoidHom, d, centData_comp_conj hC d, ?_, ?_⟩
    · change ι₀ ((MulAut.conj d) τ₀) = y
      rw [MulAut.conj_apply, hd, ← hσ₀]
    · intro σ hσ
      change ι₀ ((MulAut.conj d) σ) = ι₀ (d * σ * d⁻¹)
      rw [MulAut.conj_apply]
  ·
    have hsq : σ₀ * σ₀ = 1 := by
      apply hC.inj
      rw [map_mul, map_one]
      have hy' : (x * ι₀ σ₀) * (x * ι₀ σ₀) = 1 := by rw [← hσ₀]; exact hy2
      have hcalc : (x * ι₀ σ₀) * (x * ι₀ σ₀) = ι₀ σ₀ * ι₀ σ₀ := by
        calc (x * ι₀ σ₀) * (x * ι₀ σ₀) = x * (ι₀ σ₀ * x) * ι₀ σ₀ := by group
          _ = x * (x * ι₀ σ₀) * ι₀ σ₀ := by rw [← hC.comm σ₀]
          _ = (x * x) * (ι₀ σ₀ * ι₀ σ₀) := by group
          _ = ι₀ σ₀ * ι₀ σ₀ := by rw [hC.mul_self, one_mul]
      rw [← hcalc, hy']
    have hcard : Multiset.card σ₀.cycleType = 1 :=
      (N10_eq_one_iff (card_cycleType_le_five hsq)).1 (by
        rw [← pairOrder_z_ι' hC hsq, ← pairOrder_mul_right (p := x) (hC.comm σ₀), ← hσ₀]
        exact hord)
    obtain ⟨a, b, hab, hσ₀eq⟩ := isSwap_of_card_cycleType_eq_one hsq hcard
    have hconj : IsConj τ₀ σ₀ := by
      rw [hσ₀eq, τ₀]
      exact isConj_comm.1 (Equiv.Perm.isConj_swap hab (by decide))
    obtain ⟨d, hd⟩ := isConj_iff.1 hconj
    obtain ⟨ι', hC', h1', h2'⟩ := hC.exists_twist
    have hsign : sign σ₀ = -1 := (isSwap_of_card_cycleType_eq_one hsq hcard).sign_eq
    have hι'σ₀ : ι' σ₀ = y := by rw [h2' σ₀ hsign, ← hσ₀]
    refine ⟨ι'.comp (MulAut.conj d).toMonoidHom, d, centData_comp_conj hC' d, ?_, ?_⟩
    · change ι' ((MulAut.conj d) τ₀) = y
      rw [MulAut.conj_apply, hd, hι'σ₀]
    · intro σ hσ
      change ι' ((MulAut.conj d) σ) = ι₀ (d * σ * d⁻¹)
      rw [MulAut.conj_apply]
      exact h1' _ (by rw [map_mul, map_mul, map_inv, hσ]; group)

theorem exists_frame_at_x (hC : CentData z ι) (hx : IsConj z (ι τ₀)) :
    ∃ ι₁ : Perm (Fin 10) →* G, CentData (ι τ₀) ι₁ ∧ ι₁ τ₀ = z ∧
      (∀ σ, sign σ = 1 → (IsConj z (ι₁ σ) ↔ IsConj z (ι σ))) ∧
      (∀ σ, sign σ = 1 → (IsConj z (ι τ₀ * ι₁ σ) ↔ IsConj z (z * ι σ))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  let ι₀ : Perm (Fin 10) →* G := (MulAut.conj c).toMonoidHom.comp ι
  have hC₀ : CentData (ι τ₀) ι₀ := by
    have h := centData_conj hC c
    rwa [hc] at h
  have hzmem : z ∈ centralizer ({ι τ₀} : Set G) :=
    mem_centralizer_singleton_iff.2 (hC.comm τ₀)
  have hord : pairOrder (ι τ₀) z = N10 1 := by
    rw [pairOrder_comm (ι τ₀) z, pairOrder_z_ι' hC τ₀_mul_self,
      card_cycleType_of_isSwap isSwap_τ₀]
  obtain ⟨ι₁, d, hC₁, hι₁τ, heven⟩ :=
    exists_frame_of_pairOrder (x := ι τ₀) (y := z) hC₀ hzmem hC.mul_self hord
  have hι₀apply : ∀ w : Perm (Fin 10), ι₀ w = c * ι w * c⁻¹ := fun _ => rfl
  refine ⟨ι₁, hC₁, hι₁τ, ?_, ?_⟩
  · intro σ hσ
    have hι₁σ : ι₁ σ = c * ι (d * σ * d⁻¹) * c⁻¹ := by
      rw [heven σ hσ, hι₀apply]
    have hιd : ι (d * σ * d⁻¹) = ι d * ι σ * (ι d)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hι₁σ, isConj_conj_iff z c (ι (d * σ * d⁻¹)), hιd,
      isConj_conj_iff z (ι d) (ι σ)]
  · intro σ hσ
    have hι₁σ : ι₁ σ = c * ι (d * σ * d⁻¹) * c⁻¹ := by
      rw [heven σ hσ, hι₀apply]
    have hprod : ι τ₀ * ι₁ σ = c * (z * ι (d * σ * d⁻¹)) * c⁻¹ := by
      rw [hι₁σ, ← hc]; group
    have hzιd : z * ι (d * σ * d⁻¹) = ι d * (z * ι σ) * (ι d)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      calc z * (ι d * ι σ * (ι d)⁻¹) = (z * ι d) * ι σ * (ι d)⁻¹ := by group
        _ = (ι d * z) * ι σ * (ι d)⁻¹ := by rw [hC.comm d]
        _ = ι d * (z * ι σ) * (ι d)⁻¹ := by group
    rw [hprod, isConj_conj_iff z c (z * ι (d * σ * d⁻¹)), hzιd,
      isConj_conj_iff z (ι d) (z * ι σ)]

end CFSG.OddStandard.AltStdSec.SwapPartner
