module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Base

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

section Tau

@[expose] def u62lbTorusTau (ω : Kˣ) (k m : Fin 6) : Fin 6 → Kˣ :=
  fun x => if x = k then ω else if x = m then ω⁻¹ else 1

theorem u62lbTorusTau_fst (ω : Kˣ) {k m : Fin 6} : u62lbTorusTau ω k m k = ω := by
  simp [u62lbTorusTau]

theorem u62lbTorusTau_snd (ω : Kˣ) {k m : Fin 6} (hkm : k ≠ m) : u62lbTorusTau ω k m m = ω⁻¹ := by
  simp [u62lbTorusTau, hkm.symm]

theorem u62lbTorusTau_of_ne (ω : Kˣ) {k m x : Fin 6} (hk : x ≠ k) (hm : x ≠ m) :
    u62lbTorusTau ω k m x = 1 := by
  simp [u62lbTorusTau, hk, hm]

theorem u62lbTorusTau_prod (ω : Kˣ) {k m : Fin 6} (hkm : k ≠ m) :
    ∏ x, u62lbTorusTau ω k m x = 1 := by
  rw [Finset.prod_eq_mul k m hkm (fun x _ hx => u62lbTorusTau_of_ne ω hx.1 hx.2)
    (fun h => absurd (Finset.mem_univ k) h) (fun h => absurd (Finset.mem_univ m) h),
    u62lbTorusTau_fst, u62lbTorusTau_snd ω hkm, mul_inv_cancel]

theorem u62lbTorusTau_sum (ω : Kˣ) {k m : Fin 6} (hkm : k ≠ m) (f : K → K) :
    ∑ x, f (u62lbTorusTau ω k m x : K) = f ω + f (ω : K)⁻¹ + 4 * f 1 := by
  have h1 : ∑ x, (f (u62lbTorusTau ω k m x : K) - f 1) = (f ω - f 1) + (f (ω : K)⁻¹ - f 1) := by
    rw [Finset.sum_eq_add k m hkm (fun x _ hx => by rw [u62lbTorusTau_of_ne ω hx.1 hx.2]; simp)
      (fun h => absurd (Finset.mem_univ k) h) (fun h => absurd (Finset.mem_univ m) h),
      u62lbTorusTau_fst, u62lbTorusTau_snd ω hkm, Units.val_inv_eq_inv_val]
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linear_combination h1

end Tau

section Field4

theorem u62lb_torus_add_inv (h2 : (2 : K) = 0) {u : K} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) :
    u + u⁻¹ = 1 := by
  have hne : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hsum : u ^ 2 + u + 1 = 0 := by
    have : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu3
    exact (mul_eq_zero.mp this).resolve_left hne
  have hinv : u⁻¹ = u ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hu3)
  rw [hinv]
  linear_combination hsum - h2

theorem u62lb_torus_ringEquiv_eq_one (h : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : ω ≠ 1)
    {φ : K ≃+* K} (hφ : φ (ω : K) = ω) : φ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card (u62lb_card_units h) hω (g' := Units.mk0 x hx))
    have hxn : x = (ω : K) ^ n := by
      have := congrArg (fun u : Kˣ => (u : K)) hn
      simpa using this.symm
    rw [hxn, map_zpow₀, hφ]
    rfl

end Field4

section Entries

theorem u62lb_torus_entries (ω : Kˣ) (hω : ω ≠ 1) (φ : K ≃+* K) (A : Matrix (Fin 6) (Fin 6) K)
    (hrel : ∀ k m : Fin 6, k ≠ m → ∀ x y : Fin 6,
      (u62lbTorusTau ω k m x : K) * A x y = A x y * φ (u62lbTorusTau ω k m y : K)) :
    (∀ x y, x ≠ y → A x y = 0) ∧ (∀ x, A x x ≠ 0 → φ (ω : K) = ω) := by
  have hω1 : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr fun e => hω (Units.ext e)
  have hm : ∀ x y : Fin 6, ∃ m : Fin 6, m ≠ x ∧ m ≠ y := by decide
  constructor
  · intro x y hxy
    obtain ⟨m, hmx, hmy⟩ := hm x y
    have e := hrel x m hmx.symm x y
    rw [u62lbTorusTau_fst, u62lbTorusTau_of_ne ω hxy.symm hmy.symm, Units.val_one, map_one,
      mul_one] at e
    have : ((ω : K) - 1) * A x y = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left hω1
  · intro x hx
    obtain ⟨m, hmx, -⟩ := hm x x
    have e := hrel x m hmx.symm x x
    rw [u62lbTorusTau_fst] at e
    exact mul_left_cancel₀ hx (by rw [← e, mul_comm])

end Entries

section Glue

theorem u62lb_torus_gl_aux {G : Type*} [Group G] (a D F s : G) (hs : s * a = a * s)
    (h : (a * F * a⁻¹)⁻¹ * D = s) : D * a = a * F * s ∧ a⁻¹ * D * a = F * s := by
  have e1 : D = (a * F * a⁻¹) * s := inv_mul_eq_iff_eq_mul.mp h
  have e2 : D * a = a * F * s :=
    calc D * a = (a * F * a⁻¹) * s * a := congrArg (· * a) e1
      _ = a * F * (a⁻¹ * (s * a)) := by simp only [mul_assoc]
      _ = a * F * (a⁻¹ * (a * s)) := by rw [hs]
      _ = a * F * s := by rw [inv_mul_cancel_left]
  refine ⟨e2, ?_⟩
  rw [mul_assoc, e2]
  group

variable (h : UnitaryFieldData 2 1 K)

theorem u62lb_torus_act_mk (A : primeFormUnitary h (idGram K 6)) (φ : K ≃+* K)
    (s : gramSU h (idGram K 6)) :
    ∃ s' : gramSU h (idGram K 6),
      (s' : GL (Fin 6) K) = (A : GL (Fin 6) K) * glAut φ (s : GL (Fin 6) K) * (A : GL (Fin 6) K)⁻¹ ∧
      (primeFormConjHom h (idGram K 6) A * primeFormFieldHom h isPrimeFormGram_idGram φ :
        MulAut (primeFormP h (idGram K 6))) (s : primeFormP h (idGram K 6)) =
          (s' : primeFormP h (idGram K 6)) := by
  refine ⟨⟨_, conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h isPrimeFormGram_idGram φ s.2)⟩, rfl, ?_⟩
  rw [MulAut.mul_apply]
  change primeFormConjHom h _ A (primeFormFieldAut h isPrimeFormGram_idGram φ
    (s : primeFormP h _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem u62lb_torus_fix_data (A : primeFormUnitary h (idGram K 6)) (φ : K ≃+* K)
    (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1)
    (hfix : (primeFormConjHom h (idGram K 6) A * primeFormFieldHom h isPrimeFormGram_idGram φ :
      MulAut (primeFormP h (idGram K 6))) (diagP h μ hμ) = diagP h μ hμ) :
    ∃ c : Kˣ, (∀ x y, (μ x : K) * (A : GL (Fin 6) K) x y =
        (A : GL (Fin 6) K) x y * (φ (μ y : K) * c)) ∧
      ∑ x, (μ x : K) = (∑ x, φ (μ x : K)) * c := by
  obtain ⟨s', hs'1, hs'2⟩ := u62lb_torus_act_mk h A φ (dmatS h μ hμ)
  have h1 : (s' : primeFormP h (idGram K 6)) = (dmatS h μ hμ : primeFormP h (idGram K 6)) := by
    rw [← hs'2]
    exact hfix
  obtain ⟨c, hc⟩ := (mem_normOneScalars_iff h (s'⁻¹ * dmatS h μ hμ)).mp
    (QuotientGroup.eq.mp h1)
  have hs'1' : (s' : GL (Fin 6) K) =
      (A : GL (Fin 6) K) * glAut φ (dmat μ : GL (Fin 6) K) * (A : GL (Fin 6) K)⁻¹ := hs'1
  have hc' : ((A : GL (Fin 6) K) * glAut φ (dmat μ : GL (Fin 6) K) * (A : GL (Fin 6) K)⁻¹)⁻¹ *
      dmat μ = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← hs'1']
    exact hc
  obtain ⟨e2, e4⟩ := u62lb_torus_gl_aux (A : GL (Fin 6) K) (dmat μ)
    (glAut φ (dmat μ : GL (Fin 6) K)) (Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (Matrix.GeneralLinearGroup.scalar_commute c _) hc'
  refine ⟨c, fun x y => ?_, ?_⟩
  · have e3 := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) e2
    simp only [Units.val_mul, coe_dmat, coe_glAut, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, diagonal_map (map_zero φ), diagonal_mul_diagonal,
      Matrix.mul_assoc] at e3
    have e5 := congrFun (congrFun e3 x) y
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e5
    exact e5
  · have e3 := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K).trace) e4
    simp only [Units.val_mul, coe_dmat, coe_glAut, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, diagonal_map (map_zero φ), diagonal_mul_diagonal,
      Matrix.trace_units_conj', Matrix.trace_diagonal] at e3
    rw [e3, Finset.sum_mul]

end Glue

section Main

theorem u62lb_torus_tau_scalar (h : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : ω ≠ 1) (φ : K ≃+* K)
    {k m : Fin 6} (hkm : k ≠ m) {c : Kˣ}
    (htr : ∑ x, (u62lbTorusTau ω k m x : K) = (∑ x, φ (u62lbTorusTau ω k m x : K)) * c) :
    (c : K) = 1 := by
  have h2 := u62lb_two_eq_zero h
  have h4 : (4 : K) = 0 := by linear_combination 2 * h2
  have hω3 : (ω : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) (u62lb_units_pow_three h ω)
  have hω1 : (ω : K) ≠ 1 := fun e => hω (Units.ext e)
  have a1 := u62lb_torus_add_inv h2 hω3 hω1
  have hφ3 : φ (ω : K) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hφ1 : φ (ω : K) ≠ 1 := fun e => hω1 (φ.injective (e.trans (map_one φ).symm))
  have a2 := u62lb_torus_add_inv h2 hφ3 hφ1
  have s1 : ∑ x, (u62lbTorusTau ω k m x : K) = 1 := by
    have e := u62lbTorusTau_sum ω hkm id
    simp only [id] at e
    linear_combination e + a1 + h4
  have s2 : ∑ x, φ (u62lbTorusTau ω k m x : K) = 1 := by
    have e := u62lbTorusTau_sum ω hkm φ
    rw [map_inv₀, map_one] at e
    linear_combination e + a2 + h4
  rw [s1, s2, one_mul] at htr
  exact htr.symm

theorem u62lb_torus_pow_three_of_ne (h : UnitaryFieldData 2 1 K) {x : K} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  simpa using congrArg (fun u : Kˣ => (u : K)) (u62lb_units_pow_three h (Units.mk0 x hx))

theorem u62lb_torus_rigid {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (g : MulAut (primeFormP h (idGram K 6))) (hg : Nat.Coprime 3 (orderOf g))
    (hfix : ∀ (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1), g (diagP h μ hμ) = diagP h μ hμ) :
    g = 1 := by
  have hC : IsPrimeFormGram (1 : GL (Fin 6) K) := isPrimeFormGram_idGram
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC (by norm_num) (by omega) g
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    haveI : Finite Kˣ := Nat.finite_of_card_ne_zero (by rw [u62lb_card_units h]; norm_num)
    haveI : Nontrivial Kˣ :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [u62lb_card_units h]; norm_num)
    exact exists_ne 1
  have hrel : ∀ k m : Fin 6, k ≠ m → ∀ x y : Fin 6,
      (u62lbTorusTau ω k m x : K) * (A : GL (Fin 6) K) x y =
        (A : GL (Fin 6) K) x y * φ (u62lbTorusTau ω k m y : K) := by
    intro k m hkm x y
    have hfix' := hfix (u62lbTorusTau ω k m) (u62lbTorusTau_prod ω hkm)
    rw [hA] at hfix'
    obtain ⟨c, hent, htr⟩ := u62lb_torus_fix_data h A φ _ _ hfix'
    have hc1 := u62lb_torus_tau_scalar h hω φ hkm htr
    have := hent x y
    rwa [hc1, mul_one] at this
  obtain ⟨hdiag, hφ⟩ := u62lb_torus_entries ω hω φ _ hrel
  have hdiag_ne : ∀ x, (A : GL (Fin 6) K) x x ≠ 0 := by
    intro x hx
    have e := congrFun (congrFun (Units.mul_inv (A : GL (Fin 6) K)) x) x
    rw [Matrix.mul_apply, Finset.sum_eq_single x
      (fun y _ hy => by rw [hdiag x y hy.symm, zero_mul])
      (fun hx' => absurd (Finset.mem_univ x) hx')] at e
    rw [hx, zero_mul, Matrix.one_apply_eq] at e
    exact zero_ne_one e
  have hφ1 : φ = 1 := u62lb_torus_ringEquiv_eq_one h hω (hφ 0 (hdiag_ne 0))
  have hgA : g = primeFormConjHom h (idGram K 6) A := by rw [hA, hφ1, map_one, mul_one]
  have hA3' : (A : GL (Fin 6) K) ^ 3 = 1 := by
    have hd : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        diagonal fun x => (A : GL (Fin 6) K) x x := by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq]
      · rw [hdiag x y hxy, diagonal_apply_ne _ hxy]
    apply Units.ext
    calc (((A : GL (Fin 6) K) ^ 3 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        = ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 := Units.val_pow_eq_pow_val _ _
      _ = diagonal fun x => ((A : GL (Fin 6) K) x x) ^ 3 := by
        conv_lhs => rw [hd, diagonal_pow]
        rfl
      _ = 1 := by
        rw [← diagonal_one]
        congr 1
        funext x
        exact u62lb_torus_pow_three_of_ne h (hdiag_ne x)
  have hA3 : A ^ 3 = 1 := Subtype.ext hA3'
  have hg3 : g ^ 3 = 1 := by rw [hgA, ← map_pow, hA3, map_one]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hg.symm (orderOf_dvd_of_pow_eq_one hg3))

end Main

end CFSG.HardMathSupport.Dickson.Bal207

end
