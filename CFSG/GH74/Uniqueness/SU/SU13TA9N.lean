module

public import CFSG.GH74.Uniqueness.SU.SU13TA9NSyl

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem ew_mem_NE : ew ∈ NE :=
  mem_NE_of_conj (by rw [ew_mul_ea]; exact eb_mem_Ebar) (by rw [ew_mul_eb]; exact ec_mem_Ebar)
    (by rw [ew_mul_ec]; exact ea_mem_Ebar)

theorem ex_mem_NE : ex ∈ NE :=
  mem_NE_of_conj (by rw [ex_mul_ea]; exact Ebar.inv_mem eb_mem_Ebar)
    (by rw [ex_mul_eb]; exact Ebar.inv_mem ea_mem_Ebar)
    (by rw [ex_mul_ec]; exact Ebar.inv_mem ec_mem_Ebar)

namespace IsE

variable {E : Subgroup H}

theorem normalizer_eq_comap (hπ : TwoCover π) (hE : IsE π E) :
    normalizer (E : Set H) = NE.comap π := by
  rw [hπ.normalizer_eq_comap_of_isPGroup_three hE.1, hE.2]
  rfl

theorem mem_normalizer_iff (hπ : TwoCover π) (hE : IsE π E) {g : H} :
    g ∈ normalizer (E : Set H) ↔ π g ∈ NE := by
  rw [normalizer_eq_comap hπ hE]
  rfl

theorem card_normalizer (hπ : TwoCover π) (hE : IsE π E) :
    Nat.card (normalizer (E : Set H)) = 1296 := by
  rw [normalizer_eq_comap hπ hE, hπ.card_comap, card_NE]

theorem noOdd (hπ : TwoCover π) (hE : IsE π E) {N : Subgroup H} (hN : N ≤ normalizer (E : Set H))
    (hnorm : ∀ g ∈ normalizer (E : Set H), ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ E := by
  have hKN : N.map π ≤ NE := by
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff hπ hE).mp (hN hn)
  have hKnorm : ∀ g ∈ NE, ∀ k ∈ N.map π, g * k * g⁻¹ ∈ N.map π := by
    rintro g hg _ ⟨n, hn, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ.surj g
    have hγN : γ ∈ normalizer (E : Set H) := by
      rw [mem_normalizer_iff hπ hE, hγ]
      exact hg
    exact ⟨γ * n * γ⁻¹, hnorm γ hγN n hn, by rw [map_mul, map_mul, map_inv, hγ]⟩
  have hKodd : Odd (Nat.card (N.map π)) := Odd.of_dvd_nat hodd (Subgroup.card_map_dvd (H := N) π)
  have hle := le_Ebar_of_normal_odd hKN hKnorm hKodd
  intro n hn
  have hodd_n : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
  exact (hE.mem_iff hπ hodd_n).mpr (hle (Subgroup.mem_map_of_mem π hn))

theorem irred (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {P : Subgroup H} (hPE : P ≤ E)
    (hs₁ : c.s₁ ∈ P) (hinv : ∀ g ∈ normalizer (E : Set H), ∀ p ∈ P, g * p * g⁻¹ ∈ P) : P = E := by
  obtain ⟨w, hw⟩ := hπ.surj ew
  have hwN : w ∈ normalizer (E : Set H) := by
    rw [mem_normalizer_iff hπ hE, hw]
    exact ew_mem_NE
  refine le_antisymm hPE (fun y hy => ?_)
  have hu1 := hinv w hwN _ hs₁
  have hu2 := hinv w hwN _ hu1
  have hπu1 : π (w * c.s₁ * w⁻¹) = ea := by
    rw [map_mul, map_mul, map_inv, hw, c.π_s₁, ew_mul_ec]
  have hπu2 : π (w * (w * c.s₁ * w⁻¹) * w⁻¹) = eb := by
    rw [map_mul, map_mul, map_inv, hw, hπu1, ew_mul_ea]
  obtain ⟨i, j, k, hk⟩ := mem_Ebar_iff_toE.mp (hE.map_mem hy)
  have hmem : (w * c.s₁ * w⁻¹) ^ (i : ℕ) * (w * (w * c.s₁ * w⁻¹) * w⁻¹) ^ (j : ℕ) *
      c.s₁ ^ (k : ℕ) ∈ P :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hu1 _) (Subgroup.pow_mem _ hu2 _))
      (Subgroup.pow_mem _ hs₁ _)
  have hπ' : π ((w * c.s₁ * w⁻¹) ^ (i : ℕ) * (w * (w * c.s₁ * w⁻¹) * w⁻¹) ^ (j : ℕ) *
      c.s₁ ^ (k : ℕ)) = π y := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hπu1, hπu2, c.π_s₁, hk, toE_eq]
  have hodd : Odd (orderOf ((w * c.s₁ * w⁻¹) ^ (i : ℕ) * (w * (w * c.s₁ * w⁻¹) * w⁻¹) ^ (j : ℕ) *
      c.s₁ ^ (k : ℕ))) := hE.odd_orderOf (hPE hmem)
  have := hπ.eq_of_odd_orderOf_of_map_eq hodd (hE.odd_orderOf hy) hπ'
  rw [← this]
  exact hmem

theorem x_mul_t (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    c.x * c.t * c.x⁻¹ = c.t * z := by
  have h := c.tx_sq hπ hz hz1
  have hxx : c.x⁻¹ = c.x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact c.x_sq)
  have htt : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact c.t_sq)
  rw [hxx]
  calc c.x * c.t * c.x = c.t⁻¹ * ((c.t * c.x) ^ 2) := by
        rw [pow_two]; group
    _ = c.t * z := by rw [h, htt]

theorem invClass (hπ : TwoCover π) (c : Cfg π) (hE : IsE π E) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) {u : H} (hu : u ∈ normalizer (E : Set H)) (hord : orderOf u = 2) (huz : u ≠ z) :
    ∃ g ∈ normalizer (E : Set H), g * c.t * g⁻¹ = u := by
  have hzc : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
  have huk : u ∉ π.ker := fun h => huz (hπ.eq_of_mem_ker_ne_one' h hz hu1 hz1)
  have hct := hπ.cycleType_of_orderOf_eq_two (by norm_num) (by norm_num) hord huk
  have hsupp : ((π u : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 8 := by
    rw [← Perm.sum_cycleType, hct]
    rfl
  have hsq : π u * π u = 1 := by
    rw [← map_mul, ← pow_two]
    have : u ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
    rw [this, map_one]
  have huNE : π u ∈ NE := (mem_normalizer_iff hπ hE).mp hu
  obtain ⟨g1, hg1, hconj⟩ := exists_conj_et huNE hsq hsupp
  obtain ⟨g₀, hg₀⟩ := hπ.surj g1
  have hg₀N : g₀ ∈ normalizer (E : Set H) := by
    rw [mem_normalizer_iff hπ hE, hg₀]
    exact hg1
  have hk : (g₀ * u * g₀⁻¹) * c.t⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hg₀, c.π_t]
    rw [hconj]
    group
  have hxN : c.x ∈ normalizer (E : Set H) := by
    rw [mem_normalizer_iff hπ hE, c.π_x]
    exact ex_mem_NE
  have hcases : (g₀ * u * g₀⁻¹) * c.t⁻¹ = 1 ∨ (g₀ * u * g₀⁻¹) * c.t⁻¹ = z := by
    by_cases h1 : (g₀ * u * g₀⁻¹) * c.t⁻¹ = 1
    · exact Or.inl h1
    · exact Or.inr (hπ.eq_of_mem_ker_ne_one' hk hz h1 hz1)
  rcases hcases with h | h
  · have : g₀ * u * g₀⁻¹ = c.t := by
      have := congrArg (fun y => y * c.t) h
      simpa using this
    refine ⟨g₀⁻¹, Subgroup.inv_mem _ hg₀N, ?_⟩
    rw [← this]
    group
  · have h2 : g₀ * u * g₀⁻¹ = c.x * c.t * c.x⁻¹ := by
      rw [x_mul_t hπ c hz hz1]
      have := congrArg (fun y => y * c.t) h
      simp only [inv_mul_cancel_right] at this
      rw [this, hzc c.t]
    refine ⟨g₀⁻¹ * c.x, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀N) hxN, ?_⟩
    calc g₀⁻¹ * c.x * c.t * (g₀⁻¹ * c.x)⁻¹ = g₀⁻¹ * (c.x * c.t * c.x⁻¹) * g₀ := by group
      _ = u := by rw [← h2]; group

@[expose] def S2h (π : H →* alternatingGroup (Fin 9)) : Subgroup H := Sbar.comap π

theorem card_S2h (hπ : TwoCover π) : Nat.card (S2h π) = 16 := by
  rw [S2h, hπ.card_comap, card_Sbar]

theorem S2h_le_normalizer (hπ : TwoCover π) (hE : IsE π E) : S2h π ≤ normalizer (E : Set H) := by
  intro g hg
  rw [mem_normalizer_iff hπ hE]
  exact Sbar_le_NE hg

theorem isSylowIn_S2h (hπ : TwoCover π) (hE : IsE π E) :
    IsSylowIn (normalizer (E : Set H)) (S2h π) := by
  have := hπ.finite'
  refine isSylowIn_iff_card.mpr ⟨S2h_le_normalizer hπ hE, 4, 81, ?_, by decide, ?_⟩
  · rw [card_S2h hπ]; norm_num
  · rw [card_normalizer hπ hE]; norm_num

theorem z_mem_S2h {z : H} (hz : z ∈ π.ker) : z ∈ S2h π := by
  show π z ∈ Sbar
  rw [MonoidHom.mem_ker.mp hz]
  exact Sbar.one_mem

theorem S2h_cen (hπ : TwoCover π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) {y : H}
    (hy : y ∈ S2h π) (hord : orderOf y = 2) (hc : ∀ s ∈ S2h π, s * y = y * s) : y = z := by
  have hπy : π y ∈ Sbar := hy
  have hcen : ∀ s ∈ Sbar, s * π y = π y * s := by
    intro s hs
    obtain ⟨s', hs'⟩ := hπ.surj s
    have h1 := congrArg π (hc s' (by show π s' ∈ Sbar; rw [hs']; exact hs))
    rwa [map_mul, map_mul, hs'] at h1
  rcases Sbar_center hπy hcen with h | h
  · have hy1 : y ≠ 1 := fun h' => by rw [h', orderOf_one] at hord; omega
    exact hπ.eq_of_mem_ker_ne_one' h hz hy1 hz1
  · exfalso
    have hct : ((π y : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2} := by
      rw [h]
      exact cycleType_swap_mul_swap_of_nodup (x := 1) (y := 2) (z := 4) (t := 5) (by decide)
    have := hπ.orderOf_eq_four_of_cycleType_two_two (by norm_num) hct
    omega

end IsE

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
