module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L2UnbA
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Unb

open CFSG GorensteinWalter Subgroup AutL2Facts CFSG.ComponentClassification.GrSLit

theorem ringAut_eq_one {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (σ : F ≃+* F) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (le_refl 1) (by rw [hF, pow_one])
  have : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact Subsingleton.elim _ _

theorem isKleinFour_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) [hY : IsKleinFour Y] :
    IsKleinFour X :=
  ⟨by rw [Nat.card_congr e.toEquiv]; exact hY.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hY.exponent_two⟩

theorem factorization_card_five {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (h5 : Nat.card F = 5) :
    (Nat.card (PSL2 F)).factorization 2 = 2 := by
  rw [psl2_card_formula F hodd, h5, show 5 * (5 ^ 2 - 1) / 2 = 2 ^ 2 * 15 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_card_seven {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (h7 : Nat.card F = 7) :
    (Nat.card (PSL2 F)).factorization 2 = 3 := by
  rw [psl2_card_formula F hodd, h7, show 7 * (7 ^ 2 - 1) / 2 = 2 ^ 3 * 21 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem inner_of_fix_sylow
    {K : Type} [Group K] [Finite K] (hK : IsL2Type 5 K ∨ IsL2Type 7 K) (S : Sylow 2 K)
    {φ : MulAut K} (hφS : ∀ s ∈ (S : Subgroup K), φ s = s) (hφ2 : φ * φ = 1) :
    ∃ k ∈ (S : Subgroup K), k * k = 1 ∧ φ = MulAut.conj k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, hqK⟩ : ∃ q : ℕ, (q = 5 ∨ q = 7) ∧ Blueprint.LieModel K .PSL 2 q 1 := by
    rcases hK with h | h
    · exact ⟨5, Or.inl rfl, h⟩
    · exact ⟨7, Or.inr rfl, h⟩
  obtain ⟨hp, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hqK
  rw [pow_one] at hF
  have hp2 : q ≠ 2 := by rcases hq with rfl | rfl <;> norm_num
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 (le_refl 1)
    (by rw [hF, pow_one])
  set x := autEquiv e φ with hx
  have hxr : x.right = 1 := ringAut_eq_one hp hF _
  set T' := sylowMap e S with hT'
  have hxT : ∀ t ∈ (T' : Subgroup (PSL2 F)), x * incl F t = incl F t * x := by
    intro t ht
    rw [coe_sylowMap] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact (apply_eq_iff_commute e φ s).1 (hφS s hs)
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, hφ2, map_one]
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ (T' : Subgroup (PSL2 F)), x = incl F t := by
    rcases hq with rfl | rfl
    ·
      have hcardT : Nat.card T' = 4 := by
        rw [Sylow.card_eq_multiplicity, factorization_card_five hodd hF]; norm_num
      obtain ⟨m, -, ⟨ψ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd T'
      have hm : m = 1 := by
        have h1 := Nat.card_congr ψ.toEquiv
        rw [hcardT, DihedralGroup.nat_card] at h1
        have : 2 ^ m = 2 ^ 1 := by omega
        exact Nat.pow_right_injective (le_refl 2) this
      subst hm
      set V := (T' : Subgroup (PSL2 F)).map
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hV
      have hVT : (T' : Subgroup (PSL2 F)) ≃* V :=
        (T' : Subgroup (PSL2 F)).equivMapOfInjective _
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      have hD : IsKleinFour (DihedralGroup (2 ^ 1)) := by rw [pow_one]; infer_instance
      have : IsKleinFour (T' : Subgroup (PSL2 F)) := isKleinFour_of_equiv ψ
      have hVK : IsKleinFour V := isKleinFour_of_equiv hVT.symm
      have hC := pgl2_kleinFour_centralizer_eq_self F hodd V hVK
      have hxV : x.left ∈ V := by
        rw [← hC, mem_centralizer_iff]
        rintro _ ⟨t, ht, rfl⟩
        have h1 := congrArg SemidirectProduct.left (hxT t ht)
        simp only [SemidirectProduct.mul_left, incl_apply, SemidirectProduct.left_inl,
          SemidirectProduct.right_inl, map_one, MulAut.one_apply, hxr] at h1
        exact h1.symm
      obtain ⟨t, ht, htx⟩ := hxV
      refine ⟨t, ht, ?_⟩
      rw [incl_apply, htx]
      exact SemidirectProduct.ext (by simp) (by simp [hxr])
    · have hcardT : Nat.card T' = 8 := by
        rw [Sylow.card_eq_multiplicity, factorization_card_seven hodd hF]; norm_num
      obtain ⟨t, ht, htx⟩ := mem_center_of_right_eq_one hodd T' (by rw [hcardT]) x hxr
        (k := 1) (by rw [pow_one, sq, hx2]) hxT
      exact ⟨t, ht.1, htx.symm⟩
  refine ⟨e.symm t, ?_, ?_, ?_⟩
  · rw [coe_sylowMap] at htT
    obtain ⟨s, hs, rfl⟩ := htT
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hs
  · have h1 : incl F (t * t) = 1 := by rw [map_mul, ← hxt, hx2]
    have htt : t * t = 1 := incl_injective F (by rw [h1, map_one])
    rw [← map_mul, htt, map_one]
  · apply (autEquiv e).injective
    rw [autEquiv_conj, MulEquiv.apply_symm_apply, ← hxt]

theorem eq_one_of_odd_comm
    {K : Type} [Group K] [Finite K] (hK : IsL2Type 5 K ∨ IsL2Type 7 K) (S : Sylow 2 K)
    {φ : MulAut K} (hφS : ∀ s ∈ (S : Subgroup K), φ s = s) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    {ψ : MulAut K} (hψ : Odd (orderOf ψ)) (hψφ : ψ * φ = φ * ψ) : ψ = 1 := by
  obtain ⟨k, -, hk2, rfl⟩ := inner_of_fix_sylow hK S hφS hφ2
  have hk1 : k ≠ 1 := by rintro rfl; exact hφ1 (map_one _)
  have h16 := pow_sixteen_of_comm_conj hK hk2 hk1 hψφ
  have hdvd : orderOf ψ ∣ 2 ^ 4 := orderOf_dvd_of_pow_eq_one (by simpa using h16)
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases j with _ | j
  · rw [pow_zero] at hj'
    exact orderOf_eq_one_iff.1 hj'
  · exfalso
    rw [hj', Nat.odd_iff, pow_succ, Nat.mul_mod_left] at hψ
    exact absurd hψ (by norm_num)

end L2Unb

end CFSG.ComponentClassification.CatFactsL4U4
