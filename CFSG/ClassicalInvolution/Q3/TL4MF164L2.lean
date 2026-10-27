module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat
public import CFSG.ClassicalInvolution.Q3.TL4MF164Ex4
public import CFSG.ClassicalInvolution.Q3.TL4MF164M11

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.GorensteinWalter

theorem sq_eq_one_of_pow_four {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (h4f : ¬ 4 ∣ f) (σ : K ≃+* K) (hσ : σ ^ 4 = 1) : σ ^ 2 = 1 := by
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hcard
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hAut]; omega)
  have h1 : orderOf σ ∣ f := hAut ▸ orderOf_dvd_natCard σ
  have h2 : orderOf σ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hσ
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk2 : k ≤ 1 := by
    by_contra h
    exact h4f (by rw [show k = 2 by omega] at hk'; rw [hk'] at h1; exact h1)
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hk']; exact Nat.pow_dvd_pow 2 hk2)

theorem false_of_datum {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf1 : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (h4f : 4 ∣ f) (hm : EdgelessMember3 R S z)
    {ι : X →* PGammaL2 F} (hιinj : Function.Injective ι)
    (hιN : ∀ w : PSL2 F, ∃ y : X, ι y = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL w))
    {x c : PGL2 F} (hιz : ι z = SemidirectProduct.inl x)
    (hc : c ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hs0x : (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F) =
      SemidirectProduct.inl c * SemidirectProduct.inl x * (SemidirectProduct.inl c)⁻¹) :
    False := by
  set ψ : X →* PGammaL2 F := (MulAut.conj (SemidirectProduct.inl c)).toMonoidHom.comp ι with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj _).injective.comp hιinj
  have hψa : ∀ y, ψ y = SemidirectProduct.inl c * ι y * (SemidirectProduct.inl c)⁻¹ :=
    fun y => rfl
  have hψz : ψ z = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
    rw [hψa, hιz, hs0x]
  obtain ⟨eS⟩ := hm.cls.1
  refine false_of_four_dvd hp hp2 hf1 hF h4f (P := (Subgroup.centralizer {z}).map ψ)
    (Q := R.map ψ) (S := ((S : Subgroup R).map R.subtype).map ψ)
    (Subgroup.map_mono hm.datum.cent) ?_ ?_ ?_ ?_ (Subgroup.map_mono (Subgroup.map_subtype_le _))
    ((Subgroup.equivMapOfInjective _ ψ hψinj).symm.trans
      ((Subgroup.equivMapOfInjective _ R.subtype R.subtype_injective).symm.trans eS))
    (by rw [← hψz]; exact ⟨z, hm.datum.mem, rfl⟩)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨r, hr, rfl⟩
    refine ⟨a * r * a⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 (hm.datum.le_normalizer ha) r).1 hr
  · rintro _ ⟨a, ha, rfl⟩
    rw [← hψz, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ha]
  · obtain ⟨n₁, hn₁⟩ := weylPGL_mem_range (K := F)
    obtain ⟨c₁, rfl⟩ := hc
    obtain ⟨n₀, hn₀⟩ := hιN (c₁⁻¹ * n₁ * c₁)
    have hψn₀ : ψ n₀ = SemidirectProduct.inl (weylPGL F) := by
      rw [hψa, hn₀]
      have h1 : Matrix.ProjectiveSpecialLinearGroup.toPGL (c₁⁻¹ * n₁ * c₁) =
          (Matrix.ProjectiveSpecialLinearGroup.toPGL c₁)⁻¹ * weylPGL F *
            Matrix.ProjectiveSpecialLinearGroup.toPGL c₁ := by
        rw [map_mul, map_mul, map_inv, hn₁]
      rw [h1, map_mul, map_mul, map_inv]
      group
    refine ⟨n₀, Subgroup.mem_centralizer_singleton_iff.2 ?_, hψn₀⟩
    apply hψinj
    rw [map_mul, map_mul, hψn₀, hψz, ← map_mul, ← map_mul, weylPGL_commute_s0]
  · rintro _ ⟨r, hr, rfl⟩ h8
    rw [← map_pow] at h8 ⊢
    have h8' : r ^ 8 = 1 := hψinj (by rw [h8, map_one])
    rw [pow_four_of_pow_eight eS hr h8', map_one]

theorem model164L2_proved : Model164L2 := by
  intro X _ _ R S z hm _ hs hidx p f hp hp2 hfe hL U hUR hUc hU4 β γ hγU hβ hβ2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_fstar_equiv_psl2 hs hL
  set N := genFittingFStar X with hNdef
  have : N.Normal := genFittingFStar_normal X
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF, h, pow_zero] at h1
      omega
    · exact h
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  have hcard : 3 < Nat.card F := by
    obtain ⟨k, hk⟩ := hfe
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    rw [hF, hk, ← two_mul, pow_mul]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ (p ^ 2) := Nat.pow_le_pow_left h3 2
      _ ≤ (p ^ 2) ^ k := Nat.le_self_pow (by omega) _
  have hsurj := pGammaL2ToMulAutPSL2_surjective F hF hK hcard
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hc : Subgroup.center (PSL2 F) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.symm.injective
      rw [map_mul, map_mul, h]
    have hnt : Nontrivial (PSL2 F) := inferInstance
    rw [psl2_center_eq_bot F] at hc
    exact bot_ne_top hc
  have hC : Subgroup.centralizer (N : Set X) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  set ι := normalPSL2ToPGammaL2 N F hK hcard e hsurj with hιdef
  have hιinj : Function.Injective ι := normalPSL2ToPGammaL2_injective N F hK hcard e hC hsurj
  set Φ := autToPGammaL2 hC hK hcard e hsurj with hΦdef
  have hΦinj : Function.Injective Φ := autToPGammaL2_injective hC hK hcard e hsurj
  obtain ⟨s, hs'⟩ := hUc.exists_generator
  have hs4 : orderOf (s : X) = 4 := orderOf_gen_eq_four hs' hU4
  have hsz : (s : X) ^ 2 = z := sq_eq_of_cyclic_four hm.datum hUR hs4
  have hzN : z ∈ N := hsz ▸ sq_mem_of_index_le_two hidx (s : X)
  have hγ4 : γ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, ← hβ, hβ2]
  set x := Matrix.ProjectiveSpecialLinearGroup.toPGL (e ⟨z, hzN⟩) with hxdef
  have hιz : ι z = SemidirectProduct.inl x :=
    normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj ⟨z, hzN⟩
  have hz2 : z * z = 1 := by rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hm.datum.order]
  have hx1 : x ≠ 1 := fun h => by
    have h1 : ι z = 1 := by rw [hιz, h, map_one]
    have h2 : z = 1 := hιinj (by rw [h1, map_one])
    have h3 := hm.datum.order
    rw [h2, orderOf_one] at h3
    omega
  have hx2 : x * x = 1 := by
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    rw [map_mul, ← hιz, ← map_mul, hz2, map_one, map_one]
  obtain ⟨i, hi⟩ : ∃ i : F, i * i = -1 := by
    have := Fintype.ofFinite F
    have h4 : Fintype.card F % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hF]
      obtain ⟨k, hk⟩ := hfe
      obtain ⟨m, hm'⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
      rw [hk, show p ^ (k + k) = (p ^ k) ^ 2 by ring, hm',
        show (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 by ring]
      omega
    obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨i, hi.symm⟩
  obtain ⟨c, hc, hcx⟩ := exists_conj_s0 hK hcard hi ⟨_, rfl⟩ hx1 hx2
  have hΦγx : Φ γ * SemidirectProduct.inl x = SemidirectProduct.inl x * Φ γ := by
    have h1 : Φ γ * ι z * (Φ γ)⁻¹ = ι z := by
      rw [autToPGammaL2_conj, ← hsz, map_pow, hγU s s.2]
    rw [hιz] at h1
    calc Φ γ * SemidirectProduct.inl x
        = (Φ γ * SemidirectProduct.inl x * (Φ γ)⁻¹) * Φ γ := by group
      _ = SemidirectProduct.inl x * Φ γ := by rw [h1]
  have hs0x : (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F) =
      SemidirectProduct.inl c * SemidirectProduct.inl x * (SemidirectProduct.inl c)⁻¹ := by
    rw [← hcx, map_mul, map_mul, map_inv]
  set g : PGammaL2 F := SemidirectProduct.inl c * Φ γ * (SemidirectProduct.inl c)⁻¹ with hg
  have hgs : g * SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) * g := by
    rw [hs0x, hg]
    calc _ = SemidirectProduct.inl c * (Φ γ * SemidirectProduct.inl x) *
          (SemidirectProduct.inl c)⁻¹ := by group
      _ = SemidirectProduct.inl c * (SemidirectProduct.inl x * Φ γ) *
          (SemidirectProduct.inl c)⁻¹ := by rw [hΦγx]
      _ = _ := by group
  have hg4 : g ^ 4 = 1 := by
    rw [hg, conj_pow, ← map_pow, hγ4, map_one, mul_one, mul_inv_cancel]
  have hunconj : ∀ y : PGammaL2 F, (SemidirectProduct.inl c : PGammaL2 F) * (Φ γ) ^ 2 *
      (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inl c * y * (SemidirectProduct.inl c)⁻¹ →
      (Φ γ) ^ 2 = y := fun y h => by
    calc (Φ γ) ^ 2 = (SemidirectProduct.inl c)⁻¹ * (SemidirectProduct.inl c * (Φ γ) ^ 2 *
          (SemidirectProduct.inl c)⁻¹) * SemidirectProduct.inl c := by group
      _ = y := by rw [h]; group
  by_cases h4f : 4 ∣ f
  · exfalso
    exact false_of_datum hp hp2 hf1 hF h4f hm hιinj (fun w => ⟨(e.symm w : X), by
      rw [hιdef, normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj,
        MulEquiv.apply_symm_apply]⟩) hιz hc hs0x
  rcases sq_eq_of_commute_s0 hK (sq_eq_one_of_pow_four hp hf1 hF h4f) hgs hg4 with h | h
  · left
    apply hΦinj
    rw [map_one, hβ, map_mul, ← sq]
    rw [hg, conj_pow] at h
    exact hunconj 1 (by rw [h]; group)
  · right
    apply hΦinj
    rw [hβ, map_mul, ← sq, autToPGammaL2_mulAutConj, hιz]
    rw [hg, conj_pow, hs0x] at h
    exact hunconj _ h

end CFSG.ClassicalInvolution.Q3.TL4.MF164
