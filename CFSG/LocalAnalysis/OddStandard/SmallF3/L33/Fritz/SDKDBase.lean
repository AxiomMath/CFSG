module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDKD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit
open CFSG.OddStandard.SmallF3.L33.KD.SD

theorem mem_R8_of_bits : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 0 → fbit8 u = 0 →
    aff8 u b ∈ R8 := by decide

theorem mul_k8_mem_R8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 0 → fbit8 u = 1 →
    aff8 u b * k8 ∈ R8 := by decide

theorem d8_k8 : d8 * k8 * d8⁻¹ = z8 * k8 := by decide

theorem d8_sq : d8 ^ 2 = 1 := by decide

theorem dbit8_eq : ∀ b : ZMod 8, dbit8 b = 0 ∨ dbit8 b = 1 := by decide

theorem fbit8_eq (u : ZMod 8) : fbit8 u = 0 ∨ fbit8 u = 1 := by
  unfold fbit8
  split_ifs <;> simp

theorem refl_of_mem_R8 {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1)
    (hz : σ ≠ z8) : ∃ e : ZMod 8, dbit8 e = 0 ∧ σ = aff8 (-1) e := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  rcases hu with rfl | rfl
  · exfalso
    revert h2 h1 hz
    revert c
    decide
  · exact ⟨2 * c, by revert c; decide, rfl⟩

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {A : SDData t L}

theorem ψX_mem_H8 {g : X} (hg : g ∈ A.T) : ψX A g ∈ H8 := by
  rw [ψX_of_mem hg]
  exact A.ψ_mem_H8 _

variable (C : A.CaseKD)

theorem k_mem_C : C.k ∈ centralizer ({t} : Set X) := A.T_le_centralizer C.k_mem

theorem d_mem_C : C.d ∈ centralizer ({t} : Set X) := A.T_le_centralizer C.d_mem

theorem ψX_k : ψX A C.k = k8 := by rw [ψX_of_mem C.k_mem, C.ψ_k]

theorem ψX_d : ψX A C.d = d8 := by rw [ψX_of_mem C.d_mem, C.ψ_d]

theorem k_inv : C.k⁻¹ = C.k := by rw [inv_eq_iff_mul_eq_one, ← pow_two, C.k_sq]

variable [Finite X]

include C in
theorem eq_one_or_eq_t_of_mem_K {g : X} (hg : g ∈ A.K) : g = 1 ∨ g = t := by
  by_contra hne
  push Not at hne
  have hsub : ({1, t, g} : Set X) ⊆ (A.K : Set X) := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact one_mem _
    · exact A.t_mem_K
    · exact hg
  have h3 : ({1, t, g} : Set X).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, t, g, (t_ne_one (A := A)).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, C.card_K] at h1
  omega

theorem commute_k {r : X} (hr : r ∈ A.R) : C.k * r = r * C.k := by
  have hc : C.k * r * C.k⁻¹ * r⁻¹ ∈ A.K ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨(ψX_eq_one_iff (mul_mem (mul_mem (mul_mem C.k_mem hr.1)
      (inv_mem C.k_mem)) (inv_mem hr.1))).mp ?_,
      mul_mem (conj_mem_L (A := A) (k_mem_C C) (A.R_le_L hr)) (inv_mem (A.R_le_L hr))⟩
    rw [ψX_comm C.k_mem hr.1, ψX_k C, k8_comm_of_mem_R8 (ψX_mem_R8 hr)]
    group
  rw [A.K_inf_L, mem_bot] at hc
  calc C.k * r = C.k * r * C.k⁻¹ * r⁻¹ * (r * C.k) := by group
    _ = r * C.k := by rw [hc, one_mul]

theorem exists_eq_of_mem_T {h : X} (hh : h ∈ A.T) {u : (ZMod 8)ˣ} {b : ZMod 8}
    (hψ : ψX A h = aff8 u b) (hb : dbit8 b = 0) :
    ∃ r ∈ A.R, ∃ a e : ℕ, a < 2 ∧ e < 2 ∧ h = r * t ^ a * C.k ^ e ∧ (fbit8 u = 1 → e = 1) := by
  have hR : ∀ {g : X}, g ∈ A.T → ψX A g ∈ R8 → ∃ r ∈ A.R, ∃ a : ℕ, a < 2 ∧ g = r * t ^ a := by
    intro g hg hψg
    obtain ⟨r, hr, hrψ⟩ := exists_mem_R_ψX_eq (A := A) hψg
    have hK : r⁻¹ * g ∈ A.K := by
      rw [← ψX_eq_one_iff (mul_mem (inv_mem hr.1) hg), ψX_mul (inv_mem hr.1) hg, ψX_inv hr.1,
        hrψ, inv_mul_cancel]
    rcases eq_one_or_eq_t_of_mem_K C hK with h1 | h1
    · refine ⟨r, hr, 0, by norm_num, ?_⟩
      calc g = r * (r⁻¹ * g) := by group
        _ = r * t ^ 0 := by rw [h1, pow_zero]
    · refine ⟨r, hr, 1, by norm_num, ?_⟩
      calc g = r * (r⁻¹ * g) := by group
        _ = r * t ^ 1 := by rw [h1, pow_one]
  rcases fbit8_eq u with hu | hu
  · obtain ⟨r, hr, a, ha, rfl⟩ := hR hh (hψ ▸ mem_R8_of_bits u b hb hu)
    exact ⟨r, hr, a, 0, ha, by norm_num, by rw [pow_zero, mul_one], fun h => by
      rw [hu] at h; exact absurd h (by decide)⟩
  · have hψk : ψX A (h * C.k) ∈ R8 := by
      rw [ψX_mul hh C.k_mem, hψ, ψX_k C]
      exact mul_k8_mem_R8 u b hb hu
    obtain ⟨r, hr, a, ha, hhk⟩ := hR (mul_mem hh C.k_mem) hψk
    refine ⟨r, hr, a, 1, ha, by norm_num, ?_, fun _ => rfl⟩
    calc h = h * C.k * C.k⁻¹ := by group
      _ = r * t ^ a * C.k ^ 1 := by rw [hhk, k_inv C, pow_one]

end CFSG.OddStandard.SmallF3.L33.KD.SDKD
