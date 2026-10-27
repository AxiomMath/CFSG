module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCBase
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7Base

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)
open CFSG.ComponentClassification.FooteLit.Aut5A7

theorem fixed_iff_of_commute {π g : Perm (Fin 7)} (h : π * g = g * π) (x : Fin 7) :
    g (π x) = π x ↔ g x = x := by
  have h1 : g (π x) = π (g x) := by
    rw [← Perm.mul_apply, ← h, Perm.mul_apply]
  rw [h1, π.apply_eq_iff_eq]

theorem commute_of_fix {α : MulAut A7} {x : A7} (h : α x = x) :
    autPerm α * (x : Perm (Fin 7)) = (x : Perm (Fin 7)) * autPerm α := by
  have h1 := coe_apply α x
  rw [h] at h1
  calc autPerm α * (x : Perm (Fin 7)) =
        autPerm α * (x : Perm (Fin 7)) * (autPerm α)⁻¹ * autPerm α := by group
    _ = (x : Perm (Fin 7)) * autPerm α := by rw [← h1]

theorem mem_eqLocus_iff (τ : Perm (Fin 7)) (x : A7) :
    x ∈ MonoidHom.eqLocus (autPerm.symm τ).toMonoidHom (MonoidHom.id A7) ↔
      (x : Perm (Fin 7)) * τ = τ * x := by
  change autPerm.symm τ x = x ↔ _
  rw [← Subtype.coe_inj, autPerm_symm_apply]
  constructor
  · intro h
    calc (x : Perm (Fin 7)) * τ = τ * x * τ⁻¹ * τ := by rw [h]
      _ = τ * x := by group
  · intro h
    rw [← h]
    group

theorem two_mul_card_eqLocus_le {τ : Perm (Fin 7)} (hτ : Perm.sign τ = -1) :
    2 * Nat.card ↥(MonoidHom.eqLocus (autPerm.symm τ).toMonoidHom (MonoidHom.id A7)) ≤
      Nat.card (centralizer ({τ} : Set (Perm (Fin 7)))) := by
  set L := MonoidHom.eqLocus (autPerm.symm τ).toMonoidHom (MonoidHom.id A7) with hL
  set K := L.map (alternatingGroup (Fin 7)).subtype with hK
  have hKC : K ≤ centralizer ({τ} : Set (Perm (Fin 7))) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact (mem_eqLocus_iff τ a).mp ha
  have hτC : τ ∈ centralizer ({τ} : Set (Perm (Fin 7))) := mem_centralizer_singleton_iff.mpr rfl
  have hτK : τ ∉ K := by
    rintro ⟨a, -, ha⟩
    have h1 := Perm.mem_alternatingGroup.mp a.2
    rw [show (a : Perm (Fin 7)) = τ from ha, hτ] at h1
    exact absurd h1 (by decide)
  have hcard : Nat.card K = Nat.card L :=
    card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective
  obtain ⟨k, hk⟩ := card_dvd_of_le hKC
  have hpos : 0 < Nat.card (centralizer ({τ} : Set (Perm (Fin 7)))) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k
    · omega
    · rw [mul_one] at hk
      exact hτK ((eq_of_le_of_card_ge hKC hk.le) ▸ hτC)
  rw [← hcard, hk]
  nlinarith

theorem congr_eq_conj (γ β : MulAut A7) : MulAut.congr γ β = γ * β * γ⁻¹ := by
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply]

theorem fcc_a7_of_models {M₁ M₃ : Subgroup A7}
    (h₁ : FCConcl A7 (autPerm.symm (swap 4 5)) M₁)
    (h₃ : FCConcl A7 (autPerm.symm (swap 0 2 * swap 1 3 * swap 4 5)) M₃)
    (β : MulAut A7) (hβ2 : β * β = 1) (hβ : β ∉ innAut5 A7) : ∃ M, FCConcl A7 β M := by
  have hτ2 : autPerm β * autPerm β = 1 := by rw [← map_mul, hβ2, map_one]
  have key : ∀ τ₀ : Perm (Fin 7), τ₀.cycleType = (autPerm β).cycleType → ∀ M₀ : Subgroup A7,
      FCConcl A7 (autPerm.symm τ₀) M₀ → ∃ M, FCConcl A7 β M := by
    intro τ₀ hct M₀ h₀
    obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
    have h := h₀.map (autPerm.symm c)
    have hγ : MulAut.congr (autPerm.symm c) (autPerm.symm τ₀) = β := by
      apply autPerm.injective
      rw [congr_eq_conj, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hc]
    rw [hγ] at h
    exact ⟨_, h⟩
  rcases cycleType_of_odd_involution hτ2 (autPerm_sign_of_not_mem hβ) with h | h
  · exact key _ (by rw [cycleType_swap45, h]) M₁ h₁
  · exact key _ (by rw [cycleType_triple, h]) M₃ h₃

end CFSG.ComponentClassification.FooteLit.FCC
