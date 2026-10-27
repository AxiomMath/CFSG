module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CycPGL

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Cyc

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

omit [Field F] [Finite F] in
theorem card_mod_four {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ (2 * f)) :
    Nat.card F % 4 = 1 := by
  obtain ⟨t, ht⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  rw [hF, show p ^ (2 * f) = (p ^ f) ^ 2 by ring, ht]
  ring_nf
  omega

omit [Field F] [Finite F] in
theorem isOddPrimePower_of_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ (2 * f)) : IsOddPrimePower (Nat.card F) :=
  ⟨p, 2 * f, hp, hp.odd_of_ne_two hp2, by omega, hF⟩

@[expose] noncomputable def pairStab (ζ : F) : Subgroup (F ≃+* F) where
  carrier := {ψ | ψ ζ = ζ ∨ ψ ζ = ζ⁻¹}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, RingAut.mul_apply] at ha hb ⊢
    rcases hb with hb | hb <;> rw [hb]
    · exact ha
    · rw [map_inv₀]
      rcases ha with ha | ha <;> rw [ha]
      · exact Or.inr rfl
      · exact Or.inl (inv_inv ζ)
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with ha | ha
    · left
      change a.symm ζ = ζ
      rw [RingEquiv.symm_apply_eq, ha]
    · right
      change a.symm ζ = ζ⁻¹
      rw [RingEquiv.symm_apply_eq, map_inv₀, ha, inv_inv]

theorem two_pow_mul_le_of_comm {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ (2 * f)) {x : PGammaL2 F} {h : PGL2 F} {k j : ℕ} (hk : 2 ≤ k)
    (hh : orderOf h = 2 ^ k) (hxh : x * SemidirectProduct.inl h = SemidirectProduct.inl h * x)
    (hj : Nat.card (zpowers x.right) = 2 ^ j) :
    2 ^ k * 2 ^ j ≤ 2 ^ padicValNat 2 (p ^ (2 * f) - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of_card hp hp2 hf hF
  obtain ⟨n, ζ, hnζ, hζ⟩ := exists_conj_eq_torus hodd (card_mod_four hp hp2 hF) hk hh
  set σ := x.right with hσ
  set g := x.left with hg
  have h1 : g * pgl2FieldAut F σ h = h * g := by
    have := congrArg SemidirectProduct.left hxh
    simpa [SemidirectProduct.mul_left, hσ, hg] using this
  set g' := n * g * (pgl2FieldAut F σ n)⁻¹ with hg'
  have h2 : g' * pGammaL2FullSplitTorus F (Units.map σ.toRingHom ζ) * g'⁻¹ =
      pGammaL2FullSplitTorus F ζ := by
    rw [← pGammaL2FullSplitTorus_map_field, ← hnζ, map_mul, map_mul, map_inv, hg']
    calc n * g * ((pgl2FieldAut F σ) n)⁻¹ *
          ((pgl2FieldAut F σ) n * (pgl2FieldAut F σ) h * ((pgl2FieldAut F σ) n)⁻¹) *
          (n * g * ((pgl2FieldAut F σ) n)⁻¹)⁻¹ = n * (g * (pgl2FieldAut F σ) h) * g⁻¹ * n⁻¹ := by
          group
      _ = n * h * n⁻¹ := by rw [h1]; group
  have h3 : σ (ζ : F) = ζ ∨ σ (ζ : F) = (ζ : F)⁻¹ := by
    rcases eq_or_eq_inv_of_conj h2 with h4 | h4
    · left
      have := congrArg Units.val h4
      simpa using this
    · right
      have := congrArg Units.val h4
      simpa using this
  obtain ⟨d, hd, ψ, hψ, hψc⟩ := exists_frob_pow_mem hp (by omega) hF (zpowers σ)
  rw [hj] at hd
  have hσS : σ ∈ pairStab (ζ : F) := h3
  have hψS : ψ ∈ pairStab (ζ : F) := (zpowers_le.mpr hσS) hψ
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, zero_mul] at hd; omega
    · exact h0
  have hpd : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.one_lt
  have hkey : 2 ^ k ∣ p ^ d - 1 ∨ 2 ^ k ∣ p ^ d + 1 := by
    rw [← hζ]
    rcases (hψS : ψ (ζ : F) = ζ ∨ ψ (ζ : F) = (ζ : F)⁻¹) with h5 | h5 <;> rw [hψc] at h5
    · left
      apply orderOf_dvd_of_pow_eq_one
      have h6 : ζ ^ p ^ d = ζ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h5)
      have h7 : ζ ^ (p ^ d - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hpd.le, h6, one_mul]
      exact mul_right_cancel h7
    · right
      apply orderOf_dvd_of_pow_eq_one
      have h6 : ζ ^ p ^ d = ζ⁻¹ := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]; exact h5)
      rw [pow_succ, h6, inv_mul_cancel]
  obtain ⟨hb1, hb2⟩ := two_pow_mul_le hp hp2 hf hd
  rcases hkey with hk1 | hk1
  · have hle : k ≤ padicValNat 2 (p ^ d - 1) := (padicValNat_dvd_iff_le (by omega)).mp hk1
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hle)).trans hb1
  · have hle : k ≤ padicValNat 2 (p ^ d + 1) := (padicValNat_dvd_iff_le (by omega)).mp hk1
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hle)).trans hb2

omit [Finite F] in
theorem isCyclic_ringAut_and_card {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ (2 * f)) :
    IsCyclic (F ≃+* F) ∧ Nat.card (F ≃+* F) = 2 * f := by
  obtain ⟨φ, -, -, hzp, hcard, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hF
  exact ⟨⟨⟨φ, fun x => by
    have : x ∈ zpowers φ := by rw [hzp]; exact mem_top x
    exact this⟩⟩, hcard⟩

theorem card_le_of_abelian {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ (2 * f)) {B : Subgroup (PGammaL2 F)} (hB2 : IsPGroup 2 B)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 2 ^ padicValNat 2 (p ^ (2 * f) - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of_card hp hp2 hf hF
  have hF4 := card_mod_four hp hp2 hF
  obtain ⟨hcyc, hcardAut⟩ := isCyclic_ringAut_and_card hp hf hF
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  set π : PGammaL2 F →* (F ≃+* F) := SemidirectProduct.rightHom with hπ
  set B₀ : Subgroup (PGL2 F) := B.comap SemidirectProduct.inl with hB₀
  set R : Subgroup (F ≃+* F) := B.map π with hR
  have hcardB : Nat.card B = Nat.card B₀ * Nat.card R := by
    have h1 := relIndex_mul_card π.ker B
    have h2 : π.ker.relIndex B = Nat.card R := by
      rw [relIndex, show π.ker.subgroupOf B = (π.comp B.subtype).ker from rfl, index_ker,
        MonoidHom.range_comp, range_subtype]
    have h3 : Nat.card (π.ker ⊓ B : Subgroup (PGammaL2 F)) = Nat.card B₀ := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom, ← map_comap_eq,
        card_map_of_injective SemidirectProduct.inl_injective]
    rw [← h1, h2, h3, mul_comm]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hB2.map π)
  have hRdvd : 2 ^ j ∣ 2 * f := hj ▸ hcardAut ▸ card_subgroup_dvd_card R
  have h4R := four_mul_le hp hp2 hf hRdvd
  have hB₀2 : IsPGroup 2 B₀ := hB2.comap_of_injective _ SemidirectProduct.inl_injective
  have hB₀ab : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a := fun a ha b hb =>
    SemidirectProduct.inl_injective (by rw [map_mul, map_mul]; exact hB _ ha _ hb)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB₀2
  rw [hcardB, hk, hj]
  by_cases hB₀c : IsCyclic B₀
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · calc 2 ^ k * 2 ^ j ≤ 4 * 2 ^ j := Nat.mul_le_mul_right _ (by
            interval_cases k <;> norm_num)
        _ ≤ _ := h4R
    · obtain ⟨h₀, hh₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B₀).mp hB₀c
      have hh₀B₀ : h₀ ∈ B₀ := hh₀ ▸ mem_zpowers h₀
      have hord : orderOf h₀ = 2 ^ k := by rw [← Nat.card_zpowers, hh₀, hk]
      obtain ⟨τ, hτ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).mp inferInstance
      obtain ⟨x, hxB, hxτ⟩ : τ ∈ R := hτ ▸ mem_zpowers τ
      have hxj : Nat.card (zpowers x.right) = 2 ^ j := by
        rw [← SemidirectProduct.rightHom_eq_right]
        change Nat.card (zpowers (π x)) = 2 ^ j
        rw [hxτ, hτ, hj]
      exact two_pow_mul_le_of_comm hp hp2 hf hF hk2 hord (hB x hxB _ hh₀B₀) hxj
  · have h4 := card_le_four_of_not_isCyclic hodd hF4 hB₀2 hB₀ab hB₀c
    rw [hk] at h4
    exact (Nat.mul_le_mul_right _ h4).trans h4R

end L2Cyc

end CFSG.ComponentClassification.CatFactsL4U4
