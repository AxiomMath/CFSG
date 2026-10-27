module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Local

variable {G : Type} [Group G] [Finite G]

theorem involution_mem_of_isPGroup {J U : Subgroup G} {j : G} (hj : IsUniqueInvolution J j)
    (hUJ : U ≤ J) (hU2 : IsPGroup 2 U) (hcard : 2 ≤ Nat.card U) :
    j ∈ U ∧ ∀ x ∈ U, orderOf x = 2 → x = j := by
  have huniq : ∀ x ∈ U, orderOf x = 2 → x = j := by
    intro x hx hx2
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx2
      omega
    exact (hj.unique x (hUJ hx) hxx).resolve_left hx1
  refine ⟨?_, huniq⟩
  have hdvd : 2 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hw2 : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  rw [← huniq (w : G) w.2 hw2]
  exact w.2

theorem le_normalizer_of_sylow_centralizes {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {M J : Subgroup G} (hM : M ∈ Ω) (hJ : J ∈ Ω) (hJM : J ≠ M) {j : G}
    (hj : IsUniqueInvolution J j) {R : Subgroup G} (hR : IsSylow2In R M)
    (hRc : ∀ x ∈ R, j * x = x * j) : R ≤ Subgroup.normalizer (J : Set G) := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hM hR
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset).exists_not_commute
  have hnc : ∃ a ∈ R, a ∉ Subgroup.centralizer (M : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hxy₀ ((Subgroup.mem_centralizer_iff.mp (hcon x₀ hx₀)) y₀ (hR.1 hy₀)).symm
  have hN5 : ∀ v ∈ R, v ∉ Subgroup.centralizer (M : Set G) →
      v ∈ Subgroup.normalizer (J : Set G) := by
    intro v hv hvc
    refine hΩ.omega5 J hJ M hM hJM j hj v (hR.1 hv) ?_ ?_ (hRc v hv).symm
    · intro hall
      exact hvc (Subgroup.mem_centralizer_iff.mpr fun w hw => (hall w hw).symm)
    · exact hR.2.1.to_le (Subgroup.zpowers_le.mpr hv)
  intro v hv
  by_cases hvc : v ∈ Subgroup.centralizer (M : Set G)
  · obtain ⟨a, ha, hac⟩ := hnc
    have haN := hN5 a ha hac
    have hva : v * a ∉ Subgroup.centralizer (M : Set G) := by
      intro hva
      apply hac
      have h1 := (Subgroup.centralizer (M : Set G)).mul_mem
        ((Subgroup.centralizer (M : Set G)).inv_mem hvc) hva
      simpa using h1
    have hvaN := hN5 (v * a) (R.mul_mem hv ha) hva
    have h2 := (Subgroup.normalizer (J : Set G)).mul_mem hvaN
      ((Subgroup.normalizer (J : Set G)).inv_mem haN)
    simpa using h2
  · exact hN5 v hv hvc

theorem mem_omegaNbr_of_sylow_centralizes {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {M J : Subgroup G} (hM : M ∈ Ω) (hJ : J ∈ Ω) (hJM : J ≠ M) {j : G}
    (hj : IsUniqueInvolution J j) {R : Subgroup G} (hR : IsSylow2In R M)
    (hRc : ∀ x ∈ R, j * x = x * j) : J ∈ omegaNbr Ω M := by
  have hMJ : M ∈ omegaNbr Ω J :=
    ⟨hM, Ne.symm hJM, R, mem_RSet_of_isSylow2In hM hR, hR.1,
      le_normalizer_of_sylow_centralizes hΩ hM hJ hJM hj hR hRc⟩
  exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hM hMJ

end Local

section ZStar

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem exists_commuting_conj_ne_a7 (hnab : ∃ a b : F, a * b ≠ b * a) {t : F} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) : ∃ g : F, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  by_contra hcon
  have hiso : ∀ g : F, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon ⟨g, hne, hg⟩
  have := Fintype.ofFinite F
  obtain ⟨N, hN, hodd, hc⟩ := CFSG.ZStar.glauberman_zStar F t ht1 ht2 hiso
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · apply ht1
    have hZ : Subgroup.center F = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h' | h'
      · exact h'
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top a) b).symm
    have htc : t ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hc y
      rw [h, Subgroup.mem_bot] at h1
      have h2 : y * t * y⁻¹ = t := by
        calc y * t * y⁻¹ = y * t * y⁻¹ * t⁻¹ * t := by group
          _ = t := by rw [h1]; group
      calc y * t = (y * t * y⁻¹) * y := by group
        _ = t * y := by rw [h2]
    rw [hZ, Subgroup.mem_bot] at htc
    exact htc
  · rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card F := by
      have ht : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
      exact ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end ZStar

end CFSG.ClassicalInvolution.Hat2A7S
