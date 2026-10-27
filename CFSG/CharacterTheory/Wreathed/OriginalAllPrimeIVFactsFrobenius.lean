module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsMap
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsTorus

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

namespace IsWModel

variable {σ : Setting G} {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
  {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

theorem mem_C_of_mem_centralizer_D (hW : IsWModel σ φ) {w : G}
    (hw : w ∈ Subgroup.centralizer (σ.D : Set G)) : w ∈ σ.N ∧ w ∈ σ.C := by
  have hwN : w ∈ σ.N := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hw σ.x hW.x_mem_D).symm
  exact ⟨hwN, (TIFacts.mem_C_iff σ hwN).mpr
    (Subgroup.mem_centralizer_iff.mp hw σ.x₂ hW.x₂_mem_D).symm⟩

omit [Fintype F] in
theorem odd_orderOf_map {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (g : σ.N) {k : ℕ}
    (hk : (g : G) ^ r ^ k = 1) : Odd (orderOf (φ g)) := by
  have hg : g ^ r ^ k = 1 := Subtype.ext (by simpa using hk)
  have h1 : orderOf (φ g) ∣ r ^ k :=
    (orderOf_map_dvd φ g).trans (orderOf_dvd_of_pow_eq_one hg)
  have hodd : Odd (r ^ k) := (hr.eq_two_or_odd'.resolve_left hr2).pow
  exact hodd.of_dvd_nat h1

theorem frobenius_section [Finite G] (hW : IsWModel σ φ) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w ∈ Subgroup.centralizer (σ.D : Set G),
      (∃ n : ℕ, w ^ p ^ n = 1) → w ∉ σ.L → w ^ p ∈ σ.ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧
        ∃ K₀ : Subgroup G, σ.ON ≤ K₀ ∧ K₀ ≤ σ.N ∧ σ.ON.relIndex K₀ = s ∧
          w ∈ Subgroup.normalizer (K₀ : Set G) ∧ (∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON) ∧
          ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON := by
  intro r hr hr2 w hwD ⟨n, hn⟩ hwL hwr
  obtain ⟨hwN, hwC⟩ := hW.mem_C_of_mem_centralizer_D hwD
  obtain ⟨W, hW'⟩ := exists_oddTorus F
  obtain ⟨w₁, hw₁W, τ, hτ⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' (hW.map_mem_modelC ⟨w, hwN⟩ hwC)
    (odd_orderOf_map hr hr2 ⟨w, hwN⟩ hn)
  have hw₁T : w₁ ∈ torus F := ((hW' w₁).mp hw₁W).1
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hwL
    rw [hW.mem_L_iff ⟨w, hwN⟩, hτ, map_one, mul_one, iota_apply]
    exact ⟨_, rfl⟩
  have hτr : orderOf (τ : F ≃+* F) = r := by
    have h1 : φ (⟨w, hwN⟩ ^ r) = 1 := by
      rw [← hW.mem_ON_iff]
      simpa using hwr
    rw [map_pow, hτ] at h1
    have h2 := congrArg SemidirectProduct.rightHom h1
    rw [map_pow, map_mul, map_one, iota_apply, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, one_mul] at h2
    rw [Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hτ1
    · exact h
  obtain ⟨d, hdD, hdN, -, -, X, hdX, hX⟩ := hW.exists_swap_iota
  have hwX : w₁ * fieldSL F τ X * w₁⁻¹ = X := by
    have h1 : (⟨w, hwN⟩ : σ.N) * ⟨d, hdN⟩ = ⟨d, hdN⟩ * ⟨w, hwN⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hwD d hdD).symm
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hτ, hdX] at h2
    have h3 : (iota b m hm heven Sigma hSigma w₁ * SemidirectProduct.inr τ) *
        iota b m hm heven Sigma hSigma X *
        (iota b m hm heven Sigma hSigma w₁ * SemidirectProduct.inr τ)⁻¹ =
        iota b m hm heven Sigma hSigma X := by rw [h2, mul_inv_cancel_right]
    rw [conj_iota] at h3
    exact iota_injective b m hm heven Sigma hSigma h3
  obtain ⟨s, hs, hs2, hsr, w₀, hw₀W, hord, hnorm, hfpf⟩ :=
    exists_fixedPointFree hW.p_prime hW.p_odd hW.one_le_f hW.card hW.two_part hW.sigma_odd hW'
      (τ : F ≃+* F) τ.2 hr hr2 hτr
  have hKT : ∀ k ∈ Subgroup.zpowers w₀, k ∈ torus F := fun k hk =>
    ((hW' k).mp (Subgroup.zpowers_le.mpr hw₀W hk)).1
  set κ := kappa X hW.two_ne_zero hX with hκ
  set Kb : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
    (Subgroup.zpowers w₀).map ((iota b m hm heven Sigma hSigma).comp κ.toMonoidHom) with hKb
  have hIκ : Function.Injective ((iota b m hm heven Sigma hSigma).comp κ.toMonoidHom) :=
    (iota_injective b m hm heven Sigma hSigma).comp κ.injective
  set K₀ : Subgroup G := (Kb.comap φ).map σ.N.subtype with hK₀
  have hmemK₀ : ∀ {g : G}, g ∈ K₀ ↔ ∃ hg : g ∈ σ.N, φ ⟨g, hg⟩ ∈ Kb := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hg'⟩
      exact ⟨⟨g, hg⟩, hg', rfl⟩
  have hK₀N : K₀ ≤ σ.N := Subgroup.map_subtype_le _
  refine ⟨s, hs, hs2, hsr, K₀, ?_, hK₀N, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    have hgN : g ∈ σ.N := TIFacts.ON_le_N σ hg
    refine hmemK₀.mpr ⟨hgN, ?_⟩
    rw [(hW.mem_ON_iff ⟨g, hgN⟩).mp hg]
    exact Kb.one_mem
  ·
    set ψ : K₀ →* SemilinearExtension F b m hm heven Sigma hSigma :=
      φ.comp (Subgroup.inclusion hK₀N) with hψ
    have hker : ψ.ker = σ.ON.subgroupOf K₀ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
        ← hW.mem_ON_iff]
      rfl
    have hrange : ψ.range = Kb := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        obtain ⟨hxN, hx⟩ := hmemK₀.mp x.2
        exact hx
      · intro y hy
        obtain ⟨g, rfl⟩ := hW.model.surjective y
        exact ⟨⟨g, hmemK₀.mpr ⟨g.2, hy⟩⟩, rfl⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, hKb,
      Subgroup.card_map_of_injective hIκ, Nat.card_zpowers, hord]
  ·
    apply mem_normalizer_of_conj_mem
    intro g hg
    obtain ⟨hgN, k, hk, hgk⟩ := hmemK₀.mp hg
    refine hmemK₀.mpr ⟨σ.N.mul_mem (σ.N.mul_mem hwN hgN) (σ.N.inv_mem hwN), ?_⟩
    have h1 : φ ⟨w * g * w⁻¹, σ.N.mul_mem (σ.N.mul_mem hwN hgN) (σ.N.inv_mem hwN)⟩ =
        φ (⟨w, hwN⟩ * ⟨g, hgN⟩ * (⟨w, hwN⟩ : σ.N)⁻¹) := rfl
    rw [h1, map_mul, map_mul, map_inv, hτ, ← hgk, MonoidHom.comp_apply, conj_iota,
      MulEquiv.coe_toMonoidHom, mul_fieldSL_kappa X hW.two_ne_zero hX τ hw₁T hwX (hKT k hk)]
    exact ⟨fieldSL F τ k, hnorm k hk, rfl⟩
  ·
    intro g hg
    obtain ⟨hgN, k, hk, hgk⟩ := hmemK₀.mp hg
    have hx₂N := hW.model.x₂_mem
    have h1 : φ (⟨σ.x₂, hx₂N⟩ * ⟨g, hgN⟩ * (⟨σ.x₂, hx₂N⟩ : σ.N)⁻¹ * ⟨g, hgN⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hW.model.map_x₂, ← hgk, MonoidHom.comp_apply,
        modelY_conj_iota, MulEquiv.coe_toMonoidHom,
        weyl_conj_kappa_of_mem_torus X hW.two_ne_zero hX (hKT k hk), map_inv, inv_mul_cancel]
    have h2 := (hW.mem_ON_iff _).mpr h1
    simpa using h2
  ·
    intro g hg hc
    obtain ⟨hgN, k, hk, hgk⟩ := hmemK₀.mp hg
    have h1 : φ (⟨w, hwN⟩ * ⟨g, hgN⟩ * (⟨w, hwN⟩ : σ.N)⁻¹ * (⟨g, hgN⟩ : σ.N)⁻¹) = 1 := by
      rw [← hW.mem_ON_iff]
      simpa using hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hτ, ← hgk, MonoidHom.comp_apply,
      conj_iota, MulEquiv.coe_toMonoidHom,
      mul_fieldSL_kappa X hW.two_ne_zero hX τ hw₁T hwX (hKT k hk), mul_inv_eq_one] at h1
    have h2 : fieldSL F τ k = k := κ.injective (iota_injective b m hm heven Sigma hSigma h1)
    have hk1 : k = 1 := hfpf k hk h2
    apply (hW.mem_ON_iff ⟨g, hgN⟩).mpr
    rw [← hgk, hk1, map_one]

end IsWModel

end CFSG.Wreathed.OriginalAllPrime.IVFacts
