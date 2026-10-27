module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Case01

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem psi_110 : H.psi (1, 1, 0) = H.t * H.b := by simp [psi, psiN]

theorem psi_114 : H.psi (1, 1, 4) = H.t * H.b * H.a ^ 4 := by simp [psi, psiN]

theorem psi_100 : H.psi (1, 0, 0) = H.t := by simp [psi, psiN]

theorem comm_conj {ℓ : G} (hℓ : ℓ ∈ H.L) : ℓ * H.t * ℓ⁻¹ = H.t := by
  have := H.comm ℓ hℓ
  calc ℓ * H.t * ℓ⁻¹ = (ℓ * H.t) * ℓ⁻¹ := rfl
    _ = (H.t * ℓ) * ℓ⁻¹ := by rw [← this]
    _ = H.t := by group

theorem z_comm_b : H.a ^ 4 * H.b = H.b * H.a ^ 4 := by
  rw [H.a_pow_mul_b, H.a_pow 12]

@[expose] def Ohat : Set SMod := {m | m.1 = 1 ∧ SMod.inE1 m}

theorem ncard_Ohat : Ohat.ncard = 4 := by
  have : Ohat = ↑(Finset.univ.filter fun m : SMod => m.1 = 1 ∧ SMod.inE1 m) := by
    ext m; simp [Ohat]
  rw [this, Set.ncard_coe_finset]
  decide

theorem orbit_eq (h0 : ¬ IsConj H.t (H.a ^ 4)) {y : G}
    (hy : y ∈ Subgroup.normalizer (H.E1 : Set G)) (hyt : y * H.t * y⁻¹ = H.t * H.a ^ 4) :
    {x : G | ∃ m ∈ Subgroup.normalizer (H.E1 : Set G), x = m * H.t * m⁻¹} = H.psi '' Ohat := by
  have hg := H.g_mem_normalizer
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hx : m * H.t * m⁻¹ ∈ H.E1 := (Subgroup.mem_normalizer_iff.1 hm _).1 H.t_mem_E1
    obtain ⟨m', hm', hψ⟩ := hx
    refine ⟨m', ⟨?_, hm'⟩, hψ⟩
    by_contra hk
    have hk0 : m'.1 = 0 := by
      rw [Fin.ext_iff] at hk ⊢
      have := m'.1.isLt
      simp only [Fin.val_one, Fin.val_zero] at hk ⊢
      omega
    have hL : m * H.t * m⁻¹ ∈ H.L := by
      rw [← hψ, psi_def, hk0]
      simpa using mem_L_ba H m'.2.1.val m'.2.2.val
    have hconj : IsConj H.t (m * H.t * m⁻¹) := isConj_iff.2 ⟨m, rfl⟩
    have hI : m * H.t * m⁻¹ ∈ H.I :=
      ⟨hL, H.sq_of_isConj hconj, H.ne_one_of_isConj hconj⟩
    exact h0 (H.isConj_of_I hI H.z_mem_I hconj)
  · rintro ⟨m', ⟨hm1, hm'⟩, rfl⟩
    rcases SMod.orbit_cases m' hm1 hm' with rfl | rfl | rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, by simp [psi_100]⟩
    · exact ⟨y, hy, by rw [hyt, psi_tz]⟩
    · refine ⟨H.g * y, Subgroup.mul_mem _ hg hy, ?_⟩
      have h1 : H.g * y * H.t * (H.g * y)⁻¹ = H.g * (y * H.t * y⁻¹) * H.g⁻¹ := by group
      rw [h1, hyt, psi_110]
      calc H.t * H.b = (H.g * H.t * H.g⁻¹) * (H.g * H.a ^ 4 * H.g⁻¹) := by
            rw [H.comm_conj H.g_mem, H.g_z]
        _ = H.g * (H.t * H.a ^ 4) * H.g⁻¹ := by group
    · refine ⟨H.g * (H.g * y), Subgroup.mul_mem _ hg (Subgroup.mul_mem _ hg hy), ?_⟩
      have h1 : H.g * (H.g * y) * H.t * (H.g * (H.g * y))⁻¹ =
          H.g * (H.g * (y * H.t * y⁻¹) * H.g⁻¹) * H.g⁻¹ := by group
      rw [h1, hyt, psi_114]
      have h2 : H.g * (H.t * H.a ^ 4) * H.g⁻¹ = H.t * H.b := by
        calc H.g * (H.t * H.a ^ 4) * H.g⁻¹ = (H.g * H.t * H.g⁻¹) * (H.g * H.a ^ 4 * H.g⁻¹) := by
              group
          _ = H.t * H.b := by rw [H.comm_conj H.g_mem, H.g_z]
      rw [h2]
      calc H.t * H.b * H.a ^ 4 = H.t * (H.b * H.a ^ 4) := by rw [mul_assoc]
        _ = H.t * (H.a ^ 4 * H.b) := by rw [H.z_comm_b]
        _ = (H.g * H.t * H.g⁻¹) * (H.g * H.b * H.g⁻¹) := by
            rw [H.comm_conj H.g_mem, H.g_b]
        _ = H.g * (H.t * H.b) * H.g⁻¹ := by group

theorem sixtyfour_dvd_normalizer (h0 : ¬ IsConj H.t (H.a ^ 4)) {y : G}
    (hy : y ∈ Subgroup.normalizer (H.E1 : Set G)) (hyt : y * H.t * y⁻¹ = H.t * H.a ^ 4) :
    64 ∣ Nat.card (Subgroup.normalizer (H.E1 : Set G)) := by
  have hN := J1Std.card_eq_card_conjClass_mul (Subgroup.normalizer (H.E1 : Set G)) H.t
  have hO : Nat.card {x : G // ∃ m ∈ Subgroup.normalizer (H.E1 : Set G), x = m * H.t * m⁻¹} =
      4 := by
    have h : Nat.card {x : G // ∃ m ∈ Subgroup.normalizer (H.E1 : Set G),
        x = m * H.t * m⁻¹} = Set.ncard {x : G | ∃ m ∈ Subgroup.normalizer (H.E1 : Set G),
        x = m * H.t * m⁻¹} := Nat.card_coe_set_eq _
    rw [h, H.orbit_eq h0 hy hyt, Set.ncard_image_of_injective _ H.psi_injective, ncard_Ohat]
  have h16 : 16 ∣ Nat.card (centralizer ({H.t} : Set G) ⊓ Subgroup.normalizer (H.E1 : Set G) :
      Subgroup G) := by
    rw [← H.card_H0]
    exact Subgroup.card_dvd_of_le (le_inf (H.H0_le_S.trans H.S_le_centralizer)
      H.H0_le_normalizer)
  rw [hN, hO]
  obtain ⟨k, hk⟩ := h16
  rw [hk]
  exact ⟨k, by ring⟩

end Setting

end CFSG.EvenSporadicStandard.M11Std
