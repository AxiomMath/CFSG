module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes

public section


namespace CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary
section Factor
variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {QW : QuadraticForm K W} {p : ℕ} {β : W ≃ₗ[K] W}
theorem OddOrderIsometry.exists_norm_model3 (hx : OddOrderIsometry QW p β)
    (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K + 1) {h : K[X]}
    (hh : h ∈ primaryFactors β.toLinearMap) (hne1 : h ≠ X - 1) :
    finrank K (AdjoinRoot h) = 2 ∧
    ∃ (m : ℕ) (ι : (Fin m → AdjoinRoot h) →ₗ[K] W),
      Function.Injective ι ∧ LinearMap.range ι = primaryComponent β.toLinearMap h ∧
      (∀ a, algebraMap K (AdjoinRoot h) (QW (ι a)) = ∑ i, a i * a i ^ Nat.card K) ∧
      ∀ a, β (ι a) = ι (AdjoinRoot.root h • a) := by
  classical
  have hself := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne1
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hlamp
    exact zero_ne_one hlamp
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have hord : orderOf (AdjoinRoot.root h) = p := orderOf_eq_prime hlamp hlam1
  have hlq : AdjoinRoot.root h ^ (Nat.card K + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hpq)
  have hlqinv : AdjoinRoot.root h ^ Nat.card K = (AdjoinRoot.root h)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hlq)
  obtain ⟨d, hdeg, -, -, -, -, hroot, ι, hinj, hrange, hQι, hxι⟩ :=
    hx.selfDualModel (hp.odd_of_ne_two (by omega)) hh hne1 hself.symm
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hd1 : d = 1 := by
    let := Fintype.ofFinite K
    have hfr : frobPow K (AdjoinRoot h) d = frobPow K (AdjoinRoot h) 1 := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply AdjoinRoot.algHom_ext
      show frobPow K (AdjoinRoot h) d (AdjoinRoot.root h) =
        frobPow K (AdjoinRoot h) 1 (AdjoinRoot.root h)
      rw [frobPow_apply, frobPow_apply, hroot, pow_one, hlqinv]
    have hdpos : 0 < d := by
      have := Module.finrank_pos (R := K) (M := AdjoinRoot h)
      omega
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    set fr := FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot h) with hfr_def
    have h1 : fr ^ d' = 1 := by
      have h2 : fr ^ (d' + 1) = fr ^ 1 := hfr
      rw [pow_succ, pow_one] at h2
      exact mul_right_cancel (h2.trans (one_mul fr).symm)
    have h3 : orderOf fr ∣ d' := orderOf_dvd_of_pow_eq_one h1
    rw [hfr_def, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hd] at h3
    have h4 : d' = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  subst hd1
  refine ⟨by simpa using hd, _, ι, hinj, hrange, fun a => ?_, hxι⟩
  obtain ⟨hmem, hq⟩ := hQι a
  rw [hq, algebraMap_trace_fixedSubfield K (AdjoinRoot h) hd ⟨_, hmem⟩]
  simp
theorem OddOrderIsometry.exists_factor_planes3 (hx : OddOrderIsometry QW p β)
    (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K + 1) {h : K[X]}
    (hh : h ∈ primaryFactors β.toLinearMap) (hne1 : h ≠ X - 1)
    {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) :
    ∃ (m : ℕ) (φ : Fin m → E →ₗ[K] W) (s : ZMod p), s ≠ 0 ∧
      (∀ i, Function.Injective (φ i)) ∧
      (∀ i z, algebraMap K E (QW (φ i z)) = z * z ^ Nat.card K) ∧
      (∀ i j, i ≠ j → ∀ z w, polar QW (φ i z) (φ j w) = 0) ∧
      (∀ i z, β (φ i z) = φ i (ζ ^ s.val * z)) ∧
      (⨆ i, LinearMap.range (φ i)) = primaryComponent β.toLinearMap h := by
  classical
  obtain ⟨hdim, m, ι, hinj, hrange, hnorm, hact⟩ := hx.exists_norm_model3 hp hpne hK4 hpq hh hne1
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  obtain ⟨τ, s, hs0, hτ⟩ :=
    exists_algEquiv_root_pow hp hmon (hx.dvd_X_pow_sub_one hh) hne1 hdim hE hζ
  let φ : Fin m → E →ₗ[K] W := fun i =>
    (ι ∘ₗ LinearMap.single K (fun _ : Fin m => AdjoinRoot h) i) ∘ₗ τ.symm.toLinearMap
  have hφ : ∀ i z, φ i z = ι (Pi.single i (τ.symm z)) := fun i z => rfl
  have hq0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  refine ⟨m, φ, s, hs0, fun i z w hzw => ?_, fun i z => ?_, fun i j hij z w => ?_,
    fun i z => ?_, ?_⟩
  · rw [hφ, hφ] at hzw
    exact τ.symm.injective (Pi.single_injective i (hinj hzw))
  · rw [hφ]
    have h1 := hnorm (Pi.single i (τ.symm z))
    have h2 : ∑ j, (Pi.single i (τ.symm z) : Fin m → AdjoinRoot h) j *
        (Pi.single i (τ.symm z) : Fin m → AdjoinRoot h) j ^ Nat.card K =
        τ.symm z * τ.symm z ^ Nat.card K := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Pi.single_eq_of_ne hji, zero_pow hq0, mul_zero]
      · simp
    rw [h2] at h1
    have h3 := congrArg τ h1
    rw [AlgEquiv.commutes, map_mul, map_pow, AlgEquiv.apply_symm_apply] at h3
    exact h3
  · rw [hφ, hφ]
    set a : Fin m → AdjoinRoot h := Pi.single i (τ.symm z) with ha
    set b : Fin m → AdjoinRoot h := Pi.single j (τ.symm w) with hb
    have hab : ∀ k, a k = 0 ∨ b k = 0 := fun k => by
      by_cases hki : k = i
      · right
        rw [hb, Pi.single_eq_of_ne (hki ▸ hij)]
      · left
        rw [ha, Pi.single_eq_of_ne hki]
    have key : QW (ι a + ι b) = QW (ι a) + QW (ι b) := by
      apply (algebraMap K (AdjoinRoot h)).injective
      rw [← map_add ι, hnorm (a + b), map_add (algebraMap K (AdjoinRoot h)), hnorm a, hnorm b,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hab k with h0 | h0
      · simp [Pi.add_apply, h0]
      · simp [Pi.add_apply, h0]
    rw [QuadraticMap.polar, key]
    ring
  · rw [hφ, hact, hφ]
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji
      have : τ.symm (ζ ^ s.val * z) = AdjoinRoot.root h * τ.symm z := by
        apply τ.injective
        rw [AlgEquiv.apply_symm_apply, map_mul, hτ, AlgEquiv.apply_symm_apply]
      simp [this]
    · simp [Pi.single_eq_of_ne hji]
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      rintro _ ⟨z, rfl⟩
      rw [← hrange, hφ]
      exact ⟨_, rfl⟩
    · rw [← hrange]
      rintro _ ⟨a, rfl⟩
      have ha : a = ∑ i, Pi.single i (a i) := (Finset.univ_sum_single a).symm
      rw [ha, map_sum]
      refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨τ (a i), ?_⟩
      rw [hφ, AlgEquiv.symm_apply_apply]
theorem OddOrderIsometry.exists_plane_family3 (hx : OddOrderIsometry QW p β)
    (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ w, β w = w → w = 0) {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2)
    {ζ : E} (hζ : orderOf ζ = p) :
    ∃ (ι : Type) (_ : Fintype ι) (φ : ι → E →ₗ[K] W) (s : ι → ZMod p),
      (∀ i, s i ≠ 0) ∧ (∀ i, Function.Injective (φ i)) ∧
      (∀ i z, algebraMap K E (QW (φ i z)) = z * z ^ Nat.card K) ∧
      (∀ i j, i ≠ j → ∀ z w, polar QW (φ i z) (φ j w) = 0) ∧
      (∀ i z, β (φ i z) = φ i (ζ ^ (s i).val * z)) ∧
      (⨆ i, LinearMap.range (φ i)) = ⊤ ∧
      (∀ i z, (∀ w, polar QW (φ i z) (φ i w) = 0) → z = 0) := by
  classical
  have hne1 : ∀ h ∈ primaryFactors β.toLinearMap, h ≠ X - 1 := by
    intro h hh heq
    subst heq
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hw' : w ∈ fixedSpace β := by
      rw [fixedSpace_eq_primaryComponent]
      exact hw
    exact hw0 (hfix w (mem_fixedSpace.mp hw'))
  have hself : ∀ h ∈ primaryFactors β.toLinearMap, reciprocalPolynomial h = h := fun h hh =>
    hx.reciprocal_eq_of_dvd_card_succ hp hpq hh (hne1 h hh)
  choose! m φ s hs0 hinj hnorm horth hact hspan using fun (h : K[X])
    (hh : h ∈ primaryFactors β.toLinearMap) =>
    hx.exists_factor_planes3 hp hpne hK4 hpq hh (hne1 h hh) hE hζ
  have hmem : ∀ (h : K[X]) (hh : h ∈ primaryFactors β.toLinearMap) (i : Fin (m h)) (z : E),
      φ h i z ∈ primaryComponent β.toLinearMap h := fun h hh i z =>
    (hspan h hh) ▸ Submodule.mem_iSup_of_mem i ⟨z, rfl⟩
  have horth' : ∀ x y : (Σ h : primaryFactors β.toLinearMap, Fin (m h)), x ≠ y → ∀ z w,
      polar QW (φ x.1 x.2 z) (φ y.1 y.2 w) = 0 := by
    intro x y hxy z w
    obtain ⟨⟨h₁, hh₁⟩, i₁⟩ := x
    obtain ⟨⟨h₂, hh₂⟩, i₂⟩ := y
    by_cases hh12 : h₁ = h₂
    · subst hh12
      have hi : i₁ ≠ i₂ := fun hi => hxy (by rw [hi])
      exact horth h₁ hh₁ i₁ i₂ hi z w
    · exact hx.polar_primaryComponent_eq_zero hh₁ hh₂
        (by rw [hself h₁ hh₁]; exact fun h => hh12 h.symm) (hmem h₁ hh₁ i₁ z) (hmem h₂ hh₂ i₂ w)
  have htop : (⨆ x : (Σ h : primaryFactors β.toLinearMap, Fin (m h)),
      LinearMap.range (φ x.1 x.2)) = ⊤ := by
    rw [iSup_sigma]
    have htop := (isInternal_primaryComponent hx.squarefree_minpoly).submodule_iSup_eq_top
    rw [← htop]
    refine iSup_congr fun h => ?_
    exact hspan h h.2
  refine ⟨Σ h : primaryFactors β.toLinearMap, Fin (m h), inferInstance,
    fun x => φ x.1 x.2, fun x => s x.1, fun x => hs0 x.1 x.1.2, fun x => hinj x.1 x.1.2 x.2,
    fun x z => hnorm x.1 x.1.2 x.2 z, horth', fun x z => hact x.1 x.1.2 x.2 z, htop,
    fun x z hz => ?_⟩
  have hu : ∀ v : W, polar QW (φ x.1 x.2 z) v = 0 := by
    have hle : (⊤ : Submodule K W) ≤ LinearMap.ker (polarBilin QW (φ x.1 x.2 z)) := by
      rw [← htop]
      refine iSup_le fun y => ?_
      rintro _ ⟨w, rfl⟩
      show polarBilin QW (φ x.1 x.2 z) (φ y.1 y.2 w) = 0
      rw [polarBilin_apply_apply]
      by_cases hxy : x = y
      · subst hxy
        exact hz w
      · exact horth' x y hxy z w
    intro v
    have := hle (Submodule.mem_top (x := v))
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at this
  exact hinj x.1 x.1.2 x.2 (by rw [hx.regular _ hu, map_zero])
end Factor
section Quad
variable {K : Type} [Field K] [Finite K]
theorem exists_quadratic_extension3 {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K)
    (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E), finrank K E = 2 ∧ ∃ ζ : E, orderOf ζ = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  have : NeZero (p : K) := ⟨hpK⟩
  have hΦdeg : (cyclotomic p K).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hΦne : ¬ IsUnit (cyclotomic p K) := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨h, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hΦne (cyclotomic_ne_zero p K)
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hΦroot : aeval (AdjoinRoot.root h) (cyclotomic p K) = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.mpr hdvd
  have hlp : AdjoinRoot.root h ^ p = 1 := by
    have h1 : aeval (AdjoinRoot.root h) (X ^ p - 1 : K[X]) = 0 := by
      obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one p K
      rw [hc, map_mul, hΦroot, zero_mul]
    simpa [sub_eq_zero] using h1
  have hl1 : AdjoinRoot.root h ≠ 1 := by
    intro h1
    rw [h1] at hΦroot
    have h2 : algebraMap K (AdjoinRoot h) (p : K) = 0 := by
      rw [← eval_one_cyclotomic_prime (R := K) (p := p), ← eval₂_at_one]
      rw [aeval_def] at hΦroot
      exact hΦroot
    exact hpK ((algebraMap K (AdjoinRoot h)).injective (by rw [h2, map_zero]))
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hlp
    exact zero_ne_one hlp
  have hord : orderOf (AdjoinRoot.root h) = p := orderOf_eq_prime hlp hl1
  have hlq : AdjoinRoot.root h ^ (Nat.card K + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hpq)
  have hlqinv : AdjoinRoot.root h ^ Nat.card K = (AdjoinRoot.root h)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hlq)
  have hl2 : AdjoinRoot.root h ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  refine ⟨AdjoinRoot h, inferInstance, inferInstance, ?_, AdjoinRoot.root h, hord⟩
  let := Fintype.ofFinite K
  set fr := FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot h) with hfr
  have hfp : ∀ n : ℕ, frobPow K (AdjoinRoot h) n = fr ^ n := fun n => rfl
  have hfr1 : fr ≠ 1 := by
    intro h1
    have h3 : fr (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
      have := frobPow_apply K (AdjoinRoot h) 1 (AdjoinRoot.root h)
      rw [hfp, pow_one, pow_one, hlqinv] at this
      exact this
    rw [h1, AlgEquiv.one_apply] at h3
    apply hl2
    have h4 : AdjoinRoot.root h * AdjoinRoot.root h = 1 := by
      calc AdjoinRoot.root h * AdjoinRoot.root h = AdjoinRoot.root h * (AdjoinRoot.root h)⁻¹ := by
            rw [← h3]
        _ = 1 := mul_inv_cancel₀ hlam0
    rw [pow_two]
    exact h4
  have hfr2 : fr ^ 2 = 1 := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    show (fr ^ 2) (AdjoinRoot.root h) = (1 : AdjoinRoot h ≃ₐ[K] AdjoinRoot h) (AdjoinRoot.root h)
    have h5 := frobPow_apply K (AdjoinRoot h) 2 (AdjoinRoot.root h)
    rw [hfp] at h5
    rw [h5, AlgEquiv.one_apply, pow_two, pow_mul, hlqinv, inv_pow, hlqinv, inv_inv]
  have hord2 : orderOf fr = 2 := orderOf_eq_prime hfr2 hfr1
  rw [hfr, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic] at hord2
  exact hord2
end Quad
end CFSG.RankThree.PartOne.KCOrthogonal