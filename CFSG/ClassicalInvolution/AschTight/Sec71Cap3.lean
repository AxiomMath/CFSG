module

public import CFSG.ClassicalInvolution.AschTight.Sec71Good

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem cap_case_three (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hko : Odd k)
    (hbraid : ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W,
      t * r * t = y * (r * t * r)) :
    (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} := by
  set Y₀ := Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W with hY₀
  obtain ⟨y₁, hy₁, hb⟩ := hbraid
  have hrN : r ∈ Subgroup.normalizer (Y₀ : Set G) := hd.r_mem_normalizer_Y₀ hi
  have htN : t ∈ Subgroup.normalizer (Y₀ : Set G) := hd'.t_mem_normalizer_Y₀ hk
  have hzY := U_le_Y₀ u v W hd.z_mem
  have hjY := V_le_Y₀ u v W hd'.z_mem
  have hUV := inf_eq_bot_of_ne hd hd' hzj
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  set F : Set G := {1, r, t, r * t, t * r, r * t * r} with hF
  have hFN : ∀ x ∈ F, x ∈ Subgroup.normalizer (Y₀ : Set G) := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h <;> subst x
    · exact Subgroup.one_mem _
    · exact hrN
    · exact htN
    · exact Subgroup.mul_mem _ hrN htN
    · exact Subgroup.mul_mem _ htN hrN
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) hrN
  have hr : ∀ x ∈ F, ∃ y ∈ Y₀, ∃ x' ∈ F, x * r = y * x' := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h <;> subst x
    · exact ⟨1, Y₀.one_mem, r, by simp [hF], by group⟩
    · exact ⟨z, hzY, 1, by simp [hF], by rw [hd.sq_r, mul_one]⟩
    · exact ⟨1, Y₀.one_mem, t * r, by simp [hF], by group⟩
    · exact ⟨1, Y₀.one_mem, r * t * r, by simp [hF], by group⟩
    · refine ⟨t * z * t⁻¹, conj_mem_of_mem_normalizer htN hzY, t, by simp [hF], ?_⟩
      rw [← hd.sq_r]
      group
    · refine ⟨r * t * z * (r * t)⁻¹, conj_mem_of_mem_normalizer (Subgroup.mul_mem _ hrN htN) hzY,
        r * t, by simp [hF], ?_⟩
      rw [← hd.sq_r]
      group
  have ht : ∀ x ∈ F, ∃ y ∈ Y₀, ∃ x' ∈ F, x * t = y * x' := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h <;> subst x
    · exact ⟨1, Y₀.one_mem, t, by simp [hF], by group⟩
    · exact ⟨1, Y₀.one_mem, r * t, by simp [hF], by group⟩
    · exact ⟨j, hjY, 1, by simp [hF], by rw [hd'.sq_r, mul_one]⟩
    · refine ⟨r * j * r⁻¹, conj_mem_of_mem_normalizer hrN hjY, r, by simp [hF], ?_⟩
      rw [← hd'.sq_r]
      group
    · exact ⟨y₁, hy₁, r * t * r, by simp [hF], hb⟩
    · refine ⟨y₁⁻¹ * (t * r * j * (t * r)⁻¹), Y₀.mul_mem (Y₀.inv_mem hy₁)
        (conj_mem_of_mem_normalizer (Subgroup.mul_mem _ htN hrN) hjY), t * r, by simp [hF], ?_⟩
      have h' : r * t * r = y₁⁻¹ * (t * r * t) := by rw [hb]; group
      rw [h', ← hd'.sq_r]
      group
  refine inf_eq_of_table (F := F) hW2 hWc hd.u_memW hd'.u_memW
    (hd.U_le_R (Subgroup.mem_zpowers u)) (hd'.U_le_R (Subgroup.mem_zpowers v)) (by simp [hF])
    (step_of_table le_sup_right (U_le_Y₀ u v W) (V_le_Y₀ u v W) hFN hd.cover hd'.cover hr ht) ?_
  intro x hx hu hv
  simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h | h <;> subst x
  · rfl
  · exact absurd hu (not_comm_of_inv hd.conj_u hd.u_sq_ne)
  · exact absurd hv (not_comm_of_inv hd'.conj_u hd'.u_sq_ne)
  ·
    have hconj : r * t * v * (r * t)⁻¹ = (v * u ^ i)⁻¹ := by
      calc r * t * v * (r * t)⁻¹ = r * (t * v * t⁻¹) * r⁻¹ := by group
        _ = (r * v * r⁻¹)⁻¹ := by rw [hd'.conj_u]; group
        _ = (v * u ^ i)⁻¹ := by rw [hi]
    have hv' : r * t * v * (r * t)⁻¹ = v := by rw [hv]; group
    have e : v * u ^ i = v⁻¹ := inv_eq_iff_eq_inv.mp (hconj.symm.trans hv')
    have h2 : u ^ i * (v * v) = 1 := by
      calc u ^ i * (v * v) = (u ^ i * v) * v := by group
        _ = (v * u ^ i) * v := by rw [(huv.zpow_left i).eq]
        _ = 1 := by rw [e]; group
    have hu1 := eq_one_of_mul_eq_one hUV (Subgroup.zpow_mem_zpowers u i)
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)) h2
    rw [hu1, one_mul] at h2
    exact absurd h2 hd'.u_sq_ne
  ·
    have hconj : t * r * u * (t * r)⁻¹ = (u * v ^ k)⁻¹ := by
      calc t * r * u * (t * r)⁻¹ = t * (r * u * r⁻¹) * t⁻¹ := by group
        _ = (t * u * t⁻¹)⁻¹ := by rw [hd.conj_u]; group
        _ = (u * v ^ k)⁻¹ := by rw [hk]
    have hu' : t * r * u * (t * r)⁻¹ = u := by rw [hu]; group
    have e : u * v ^ k = u⁻¹ := inv_eq_iff_eq_inv.mp (hconj.symm.trans hu')
    have h2 : (u * u) * v ^ k = 1 := by
      calc (u * u) * v ^ k = u * (u * v ^ k) := by group
        _ = 1 := by rw [e]; group
    exact absurd (eq_one_of_mul_eq_one hUV
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u))
      (Subgroup.zpow_mem_zpowers v k) h2) hd.u_sq_ne
  ·
    have hconj : r * t * r * u * (r * t * r)⁻¹ = (u⁻¹ * (v * u ^ i) ^ k)⁻¹ := by
      calc r * t * r * u * (r * t * r)⁻¹ = r * (t * (r * u * r⁻¹) * t⁻¹) * r⁻¹ := by group
        _ = r * (t * u * t⁻¹)⁻¹ * r⁻¹ := by rw [hd.conj_u]; group
        _ = (r * u * r⁻¹ * (r * v * r⁻¹) ^ k)⁻¹ := by rw [hk, conj_zpow]; group
        _ = (u⁻¹ * (v * u ^ i) ^ k)⁻¹ := by rw [hd.conj_u, hi]
    have hu' : r * t * r * u * (r * t * r)⁻¹ = u := by rw [hu]; group
    have e : (v * u ^ i) ^ k = 1 := by
      have h1 : u⁻¹ * (v * u ^ i) ^ k = u⁻¹ := inv_eq_iff_eq_inv.mp (hconj.symm.trans hu')
      calc (v * u ^ i) ^ k = u * (u⁻¹ * (v * u ^ i) ^ k) := by group
        _ = 1 := by rw [h1]; group
    rw [((huv.zpow_left i).symm).mul_zpow, ← zpow_mul,
      ((huv.zpow_left (i * k)).zpow_right k).eq.symm] at e
    have hu1 := eq_one_of_mul_eq_one hUV (Subgroup.zpow_mem_zpowers u _)
      (Subgroup.zpow_mem_zpowers v k) e
    rw [hu1, one_mul, zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd] at e
    obtain ⟨n, hn⟩ := hd'.orderOf_eq
    have h4 := hd'.four_le
    have h2v : (2 : ℤ) ∣ (orderOf v : ℤ) := by
      rw [hn]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · rw [h0, pow_zero] at hn
          omega
        · omega⟩
      exact ⟨2 ^ n', by push_cast; ring⟩
    exact absurd (even_iff_two_dvd.mpr (h2v.trans e)) (Int.not_even_iff_odd.mpr hko)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
