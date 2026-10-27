module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearBorel

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

section Arithmetic

theorem eq_one_of_pow_odd_of_card_two_pow {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hG : Nat.card G = 2 ^ a) {x : G} {t : ℕ} (ht : Odd t) (hx : x ^ t = 1) : x = 1 := by
  have h1 : orderOf x ∣ t := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ 2 ^ a := hG ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime t (2 ^ a) := Nat.Coprime.pow_right a (Odd.coprime_two_right ht)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem natCast_eq_one_of_pow_odd {k t s : ℕ} (ht : Odd t)
    (hs : (s : ZMod (2 ^ k)) ^ t = 1) : (s : ZMod (2 ^ k)) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact Subsingleton.elim _ _
  · set U := Units.ofPowEqOne _ t hs (Odd.pos ht).ne' with hUdef
    have hcard : Nat.card (ZMod (2 ^ k))ˣ = 2 ^ (k - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two hk]
      simp
    have hU1 : U ^ t = 1 := Units.pow_ofPowEqOne _ _
    rw [← Units.val_ofPowEqOne _ t hs (Odd.pos ht).ne', ← hUdef,
      eq_one_of_pow_odd_of_card_two_pow hcard ht hU1, Units.val_one]

end Arithmetic

section Fixed

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem unitsField_mul_apply (σ τ : F ≃+* F) (c : Fˣ) :
    CentralSL2.unitsField (σ * τ) c = CentralSL2.unitsField σ (CentralSL2.unitsField τ c) :=
  Units.ext (by simp only [CentralSL2.unitsField_apply, RingAut.mul_apply])

theorem comp_unitsField_eq_of_two_power (η : Fˣ →* ℂˣ) {k : ℕ} (hη : orderOf η = 2 ^ k)
    (σ : F ≃+* F) (hσ : Odd (orderOf σ)) : η.comp (CentralSL2.unitsField σ) = η := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨s, hs⟩ : ∃ s : ℕ, g₀ ^ s = CentralSL2.unitsField σ g₀ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg₀ _))
  have hiter : ∀ j : ℕ, CentralSL2.unitsField (σ ^ j) g₀ = g₀ ^ (s ^ j) := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, pow_one]
      exact Units.ext rfl
    | succ j ih =>
      rw [pow_succ, unitsField_mul_apply, ← hs, map_pow, ih, ← pow_mul, pow_succ]
  have ht := hiter (orderOf σ)
  rw [pow_orderOf_eq_one] at ht
  have hone : CentralSL2.unitsField (1 : F ≃+* F) g₀ = g₀ := Units.ext rfl
  rw [hone] at ht
  have hmod : s ^ orderOf σ ≡ 1 [MOD orderOf g₀] := by
    have := (pow_eq_pow_iff_modEq (x := g₀) (n := s ^ orderOf σ) (m := 1)).mp
      (by rw [pow_one]; exact ht.symm)
    exact this
  let : Fintype F := Fintype.ofFinite F
  have hfin : Finite (Fˣ →* ℂˣ) := CentralSL2.finite_units_hom F
  have hcardX : Nat.card (Fˣ →* ℂˣ) = Nat.card Fˣ := by
    obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
    exact Nat.card_congr e.toEquiv
  have hdvd : 2 ^ k ∣ orderOf g₀ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, ← hcardX, ← hη]
    exact orderOf_dvd_natCard η
  have hmod2 : s ^ orderOf σ ≡ 1 [MOD 2 ^ k] := Nat.ModEq.of_dvd hdvd hmod
  have hs1 : (s : ZMod (2 ^ k)) = 1 := by
    apply natCast_eq_one_of_pow_odd hσ
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hmod2
  have hs1' : s ≡ 1 [MOD 2 ^ k] := by
    rw [← ZMod.natCast_eq_natCast_iff, hs1, Nat.cast_one]
  have hηg : η g₀ ^ (2 ^ k) = 1 := by
    rw [← MonoidHom.pow_apply, ← hη, pow_orderOf_eq_one, MonoidHom.one_apply]
  have hηs : η (CentralSL2.unitsField σ g₀) = η g₀ := by
    rw [← hs, map_pow]
    have h := (pow_eq_pow_iff_modEq (x := η g₀) (n := s) (m := 1)).mpr
      (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hηg) hs1')
    rwa [pow_one] at h
  refine MonoidHom.ext fun c => ?_
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, g₀ ^ j = c :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg₀ c))
  rw [MonoidHom.comp_apply, map_pow, map_pow, hηs, map_pow]

theorem parameterStabilizer_eq_top_of_two_power {b : Fˣ} {m : ℕ}
    {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma)) (P : CentralSL2.PrincipalSeriesParameter F b m) {k : ℕ}
    (hk : orderOf P.1.1 = 2 ^ k) : CentralSL2.parameterStabilizer hSigma P = ⊤ := by
  have : Finite Sigma := inferInstance
  ext σ
  simp only [Subgroup.mem_top, iff_true]
  rw [CentralSL2.mem_parameterStabilizer_iff]
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  refine comp_unitsField_eq_of_two_power P.1.1 hk _ ?_
  rw [Subgroup.orderOf_coe, orderOf_inv]
  exact hd.of_dvd_nat (orderOf_dvd_natCard σ)

end Fixed

end CFSG.Wreathed
