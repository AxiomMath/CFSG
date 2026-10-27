module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FLift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace S7FFrame

variable {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem exists_family (F : S7FFrame t B E H φ) :
    ∃ u : Fin 5 → G, (∀ i, u i ∈ E) ∧ (∀ i, s7fKap t (u i) = φ (wvec i)) ∧
      ∀ h ∈ H, ∀ σ ∈ alternatingGroup (Fin 5), s7fActs φ h σ →
        ∀ i, (u (σ i))⁻¹ * (h * u i * h⁻¹) ∈ B := by
  obtain ⟨e₀, he₀, hκ₀⟩ := F.kap_surj (φ (wvec 0)) (F.mem_B_iff.mpr ⟨_, wvec_even 0, rfl⟩)
  have hσ : ∀ i : Fin 5, ∃ σ ∈ alternatingGroup (Fin 5), σ 0 = i := fun i => exists_alt_apply 0 i
  choose σ hσA hσ0 using hσ
  have hh : ∀ i : Fin 5, ∃ h ∈ H, s7fActs φ h (σ i) := fun i => F.realize (σ i)
  choose hi hiH hiσ using hh
  refine ⟨fun i => hi i * e₀ * (hi i)⁻¹, fun i => F.H_E _ (hiH i) e₀ he₀, fun i => ?_, ?_⟩
  · show s7fKap t (hi i * e₀ * (hi i)⁻¹) = φ (wvec i)
    rw [F.kap_conj_perm (hiH i) he₀ (hiσ i) (wvec_even 0) hκ₀, permVec_wvec, hσ0]
  · intro h hh τ hτA hτ i
    show (hi (τ i) * e₀ * (hi (τ i))⁻¹)⁻¹ * (h * (hi i * e₀ * (hi i)⁻¹) * h⁻¹) ∈ B
    set j := τ i with hj
    set k := (hi j)⁻¹ * h * hi i with hk
    have hkH : k ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hiH j)) hh) (hiH i)
    have hkσ : s7fActs φ k ((σ j)⁻¹ * τ * σ i) :=
      s7fActs_mul (s7fActs_mul (s7fActs_inv (hiσ j)) hτ) (hiσ i)
    have hkA : (σ j)⁻¹ * τ * σ i ∈ alternatingGroup (Fin 5) :=
      (alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).inv_mem (hσA j)) hτA)
        (hσA i)
    have hk0 : ((σ j)⁻¹ * τ * σ i) 0 = 0 := by
      simp only [Equiv.Perm.mul_apply, hσ0]
      exact Equiv.Perm.inv_eq_iff_eq.mpr (hσ0 j).symm
    have hfix := F.fixed_lift he₀ hκ₀ hkH hkσ hkA hk0
    have e : (hi j * e₀ * (hi j)⁻¹)⁻¹ * (h * (hi i * e₀ * (hi i)⁻¹) * h⁻¹) =
        hi j * (e₀⁻¹ * (k * e₀ * k⁻¹)) * (hi j)⁻¹ := by
      rw [hk]
      group
    rw [e]
    exact F.H_B (hiH j) hfix

theorem family_odd (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i))
    (heven : ∀ h ∈ H, ∀ σ ∈ alternatingGroup (Fin 5), s7fActs φ h σ →
      ∀ i, (u (σ i))⁻¹ * (h * u i * h⁻¹) ∈ B) :
    ∀ h ∈ H, ∀ σ : Equiv.Perm (Fin 5), s7fActs φ h σ → ∀ i j,
      ((u (σ i))⁻¹ * (h * u i * h⁻¹))⁻¹ * ((u (σ j))⁻¹ * (h * u j * h⁻¹)) ∈ B := by
  intro h hh σ hσ i j
  have hd : ∀ m, s7fKap t ((u (σ m))⁻¹ * (h * u m * h⁻¹)) = 1 := fun m => by
    rw [F.kap_inv_mul (hu _) (F.H_E h hh _ (hu m)),
      F.kap_conj_perm hh (hu m) hσ (wvec_even m) (hκu m), permVec_wvec, hκu, inv_mul_cancel]
  obtain ⟨τ, hτA, hτi⟩ := exists_alt_apply i j
  obtain ⟨k, hkH, hkτ⟩ := F.realize τ
  set k' := h * k * h⁻¹ with hk'
  have hk'H : k' ∈ H := H.mul_mem (H.mul_mem hh hkH) (H.inv_mem hh)
  have hk'σ : s7fActs φ k' (σ * τ * σ⁻¹) :=
    s7fActs_mul (s7fActs_mul hσ hkτ) (s7fActs_inv hσ)
  have hk'A : σ * τ * σ⁻¹ ∈ alternatingGroup (Fin 5) :=
    (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem τ hτA σ
  have hc₁ := heven k hkH τ hτA hkτ i
  rw [hτi] at hc₁
  have hc₂ := heven k' hk'H _ hk'A hk'σ (σ i)
  have hidx : (σ * τ * σ⁻¹) (σ i) = σ j := by
    simp [Equiv.Perm.mul_apply, hτi]
  rw [hidx] at hc₂
  set di := (u (σ i))⁻¹ * (h * u i * h⁻¹) with hdi
  have hdiE : di ∈ E := E.mul_mem (E.inv_mem (hu _)) (F.H_E h hh _ (hu i))
  have hconj := F.conj_A_mem hk'H hdiE (hd i)
  set c₁ := (u j)⁻¹ * (k * u i * k⁻¹) with hc₁def
  set c₂ := (u (σ j))⁻¹ * (k' * u (σ i) * k'⁻¹) with hc₂def
  have key : di⁻¹ * ((u (σ j))⁻¹ * (h * u j * h⁻¹)) =
      (di⁻¹ * c₂ * di) * (di⁻¹ * (k' * di * k'⁻¹)) * (h * c₁⁻¹ * h⁻¹) := by
    rw [hdi, hc₁def, hc₂def, hk']
    group
  rw [key]
  have h1 : di⁻¹ * c₂ * di ∈ B := by
    have e : di⁻¹ * c₂ * di = c₂ := by
      rw [mul_assoc, ← F.comm_B di hdiE c₂ hc₂]
      group
    rw [e]
    exact hc₂
  exact B.mul_mem (B.mul_mem h1 hconj) (F.H_B hh (B.inv_mem hc₁))

end S7FFrame

end CFSG.OddStandard.SmallF3.Omega
