module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Unitary

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K} [CharP K 2]

@[expose] noncomputable def jEmb (E : QuadExt F K σ) (n : ℕ) :
    (Fin n → K) →ₗ[F] (Fin n ⊕ Fin n → K) where
  toFun x := fun v => match v with
    | .inl i => x i
    | .inr i => σ (x i)
  map_add' x y := by
    ext v
    cases v <;> simp
  map_smul' c x := by
    ext v
    cases v with
    | inl i => simp
    | inr i => simp only [Pi.smul_apply, Algebra.smul_def, map_mul, E.fix, RingHom.id_apply]

omit [CharP K 2] in
@[simp] theorem jEmb_apply_inl (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) (i : Fin n) :
    jEmb E n x (Sum.inl i) = x i := rfl

omit [CharP K 2] in
@[simp] theorem jEmb_apply_inr (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) (i : Fin n) :
    jEmb E n x (Sum.inr i) = σ (x i) := rfl

omit [CharP K 2] in
theorem jEmb_injective (E : QuadExt F K σ) (n : ℕ) : Function.Injective (jEmb (F := F) E n) := by
  intro x y h
  funext i
  have := congrFun h (Sum.inl i)
  simpa using this

omit [CharP K 2] in
theorem dFlip_jEmb (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    dFlip σ (jEmb E n x) = jEmb E n x := by
  ext v
  cases v with
  | inl i => simp [E.isUnitary.invol]
  | inr i => simp

omit [CharP K 2] in
theorem mem_range_jEmb_iff (E : QuadExt F K σ) (n : ℕ) (v : Fin n ⊕ Fin n → K) :
    v ∈ LinearMap.range (jEmb (F := F) E n) ↔ dFlip σ v = v := by
  constructor
  · rintro ⟨x, rfl⟩
    exact dFlip_jEmb E n x
  · intro hv
    refine ⟨fun i => v (Sum.inl i), ?_⟩
    ext w
    cases w with
    | inl i => rfl
    | inr i =>
      have h := congrFun hv (Sum.inl i)
      simp only [dFlip_apply_inl] at h
      simp only [jEmb_apply_inr]
      rw [← h, E.isUnitary.invol]

omit [CharP K 2] in
theorem quadPlus_jEmb (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    quadPlus n K (jEmb E n x) = algebraMap F K (Qn E n x) := by
  rw [quadPlus_apply, algebraMap_Qn]
  exact Finset.sum_congr rfl fun i _ => rfl

omit [CharP K 2] in
theorem polar_jEmb (E : QuadExt F K σ) (n : ℕ) (x y : Fin n → K) :
    polar (quadPlus n K) (jEmb E n x) (jEmb E n y) =
      algebraMap F K (polar (Qn E n) x y) := by
  rw [polar_quadPlus, algebraMap_polar_Qn, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jEmb_apply_inl, jEmb_apply_inr, map_mul, E.isUnitary.invol]
  ring

noncomputable def bcTheta (E : QuadExt F K σ) : K := Classical.choose E.isUnitary.exists_ne

omit [CharP K 2] in
theorem bcTheta_not_fixed (E : QuadExt F K σ) : σ (bcTheta E) ≠ bcTheta E :=
  Classical.choose_spec E.isUnitary.exists_ne

noncomputable def bcSigmaTheta (E : QuadExt F K σ) : K := σ (bcTheta E)

noncomputable def bcDelta (E : QuadExt F K σ) : K := bcTheta E + bcSigmaTheta E

omit [CharP K 2] in
theorem sigma_bcDelta (E : QuadExt F K σ) : σ (bcDelta E) = bcDelta E := by
  simp only [bcDelta, bcSigmaTheta, map_add, E.isUnitary.invol]
  rw [add_comm]

theorem bcDelta_ne_zero (E : QuadExt F K σ) : bcDelta E ≠ 0 := by
  intro h
  apply bcTheta_not_fixed E
  have h' : bcTheta E = bcSigmaTheta E := by
    have h2 : bcTheta E = - bcSigmaTheta E := (add_eq_zero_iff_eq_neg.mp h)
    rwa [CharTwo.neg_eq] at h2
  exact h'.symm

theorem exists_eq_algebraMap_add_algebraMap_mul (E : QuadExt F K σ) (c : K) :
    ∃ a b : F, c = algebraMap F K a + algebraMap F K b * bcTheta E := by
  have hδ : bcDelta E ≠ 0 := bcDelta_ne_zero E
  obtain ⟨d, hd⟩ : ∃ d : F, algebraMap F K d = bcDelta E :=
    E.exists_of_fix (bcDelta E) (sigma_bcDelta E)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hδ hd.symm
  obtain ⟨e, he⟩ : ∃ e : F, algebraMap F K e = c + σ c :=
    E.exists_of_fix (c + σ c) (by rw [map_add, E.isUnitary.invol, add_comm])
  have hβ : algebraMap F K (e / d) * bcDelta E = c + σ c := by
    rw [map_div₀, he, hd, div_mul_cancel₀ _ hδ]
  have hσc : σ c = c + algebraMap F K (e / d) * bcDelta E := by
    rw [hβ, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hδs : bcDelta E + σ (bcTheta E) = bcTheta E := by
    rw [show bcDelta E = bcTheta E + bcSigmaTheta E from rfl,
      show bcSigmaTheta E = σ (bcTheta E) from rfl, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hfix : σ (c + algebraMap F K (e / d) * bcTheta E) =
      c + algebraMap F K (e / d) * bcTheta E := by
    rw [map_add, map_mul, E.fix, hσc, add_assoc, ← mul_add, hδs]
  obtain ⟨a, ha⟩ := E.exists_of_fix (c + algebraMap F K (e / d) * bcTheta E) hfix
  refine ⟨a, e / d, ?_⟩
  rw [ha, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem exists_eq_sum_smul_single (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    ∃ a b : Fin n → F, x = ∑ i : Fin n,
      (a i • (Pi.single i (1 : K) : Fin n → K) +
        b i • (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
  choose a b hab using fun i => exists_eq_algebraMap_add_algebraMap_mul (E := E) (x i)
  have hterm : ∀ (i j : Fin n),
      (a i • (Pi.single i (1 : K) : Fin n → K) +
        b i • (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) j =
      if j = i then algebraMap F K (a i) + algebraMap F K (b i) * bcTheta E else 0 := by
    intro i j
    by_cases h : j = i
    · subst h
      simp [Pi.single_eq_same, Algebra.smul_def]
    · simp [h]
  refine ⟨a, b, ?_⟩
  ext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [hterm j j, if_pos rfl]
    exact hab j
  · intro i _ hij
    rw [hterm i j, if_neg (Ne.symm hij)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem bcDelta_smul_stdE (E : QuadExt F K σ) (n : ℕ) (i : Fin n) :
    bcDelta E • stdE (K := K) i =
      bcSigmaTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
        jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K)) := by
  ext v
  cases v with
  | inl j =>
    by_cases h : j = i
    · subst h
      simp [stdE, Pi.single_eq_same, Algebra.smul_def, bcDelta, bcSigmaTheta, add_comm]
    · have hne' : i ≠ j := Ne.symm h
      simp only [stdE_inl, if_neg h, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        jEmb_apply_inl, Pi.single_eq_of_ne' hne', mul_zero, add_zero]
  | inr j =>
    by_cases h : j = i
    · subst h
      simp [stdE, Pi.single_eq_same, Algebra.smul_def, bcSigmaTheta, CharTwo.add_self_eq_zero]
    · have hne' : i ≠ j := Ne.symm h
      simp only [stdE_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jEmb_apply_inr,
        Pi.single_eq_of_ne' hne', mul_zero, map_zero, add_zero]

theorem bcDelta_smul_stdF (E : QuadExt F K σ) (n : ℕ) (i : Fin n) :
    bcDelta E • stdF (K := K) i =
      bcTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
        jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K)) := by
  ext v
  cases v with
  | inl j =>
    by_cases h : j = i
    · subst h
      simp [stdF, Pi.single_eq_same, Algebra.smul_def, CharTwo.add_self_eq_zero]
    · have hne' : i ≠ j := Ne.symm h
      simp only [stdF_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jEmb_apply_inl,
        Pi.single_eq_of_ne' hne', mul_zero, add_zero]
  | inr j =>
    by_cases h : j = i
    · subst h
      simp [stdF, Pi.single_eq_same, Algebra.smul_def, bcDelta, bcSigmaTheta]
    · have hne' : i ≠ j := Ne.symm h
      simp only [stdF_inr, if_neg h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jEmb_apply_inr,
        Pi.single_eq_of_ne' hne', mul_zero, map_zero, add_zero]

theorem stdE_mem_span_range_jEmb (E : QuadExt F K σ) (n : ℕ) (i : Fin n) :
    stdE (K := K) i ∈ Submodule.span K (Set.range (jEmb (F := F) E n)) := by
  have hδ : bcDelta E ≠ 0 := bcDelta_ne_zero E
  have hX : bcSigmaTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
      jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K)) ∈
      Submodule.span K (Set.range (jEmb (F := F) E n)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
      (Submodule.subset_span (Set.mem_range_self _))
  have hmem :=
    Submodule.smul_mem (Submodule.span K (Set.range (jEmb (F := F) E n))) (bcDelta E)⁻¹ hX
  have heq : stdE (K := K) i =
      (bcDelta E)⁻¹ • (bcSigmaTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
        jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    rw [← bcDelta_smul_stdE E n i, inv_smul_smul₀ hδ]
  rwa [heq]

theorem stdF_mem_span_range_jEmb (E : QuadExt F K σ) (n : ℕ) (i : Fin n) :
    stdF (K := K) i ∈ Submodule.span K (Set.range (jEmb (F := F) E n)) := by
  have hδ : bcDelta E ≠ 0 := bcDelta_ne_zero E
  have hX : bcTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
      jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K)) ∈
      Submodule.span K (Set.range (jEmb (F := F) E n)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
      (Submodule.subset_span (Set.mem_range_self _))
  have hmem :=
    Submodule.smul_mem (Submodule.span K (Set.range (jEmb (F := F) E n))) (bcDelta E)⁻¹ hX
  have heq : stdF (K := K) i =
      (bcDelta E)⁻¹ • (bcTheta E • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
        jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    rw [← bcDelta_smul_stdF E n i, inv_smul_smul₀ hδ]
  rwa [heq]

omit [CharP K 2] in
theorem eq_sum_smul_std (n : ℕ) (v : Fin n ⊕ Fin n → K) :
    v = ∑ i : Fin n, (v (Sum.inl i) • stdE (K := K) i + v (Sum.inr i) • stdF (K := K) i) := by
  ext w
  cases w with
  | inl j =>
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [stdE, stdF]
    · intro i _ hij
      simp [stdE, stdF, hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  | inr j =>
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [stdE, stdF]
    · intro i _ hij
      simp [stdE, stdF, hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

theorem span_range_jEmb (E : QuadExt F K σ) (n : ℕ) :
    Submodule.span K (Set.range (jEmb (F := F) E n)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [eq_sum_smul_std n v]
  exact Submodule.sum_mem _ fun i _ => Submodule.add_mem _
    (Submodule.smul_mem _ _ (stdE_mem_span_range_jEmb E n i))
    (Submodule.smul_mem _ _ (stdF_mem_span_range_jEmb E n i))

noncomputable def bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
  (bcDelta E)⁻¹ • ∑ i : Fin n,
    ((LinearMap.toSpanSingleton K (Fin n ⊕ Fin n → K)
          (jEmb E n (g (Pi.single i (1 : K) : Fin n → K)))).comp
        (bcSigmaTheta E • (LinearMap.proj (Sum.inl i) : (Fin n ⊕ Fin n → K) →ₗ[K] K) +
          bcTheta E • (LinearMap.proj (Sum.inr i) : (Fin n ⊕ Fin n → K) →ₗ[K] K)) +
      (LinearMap.toSpanSingleton K (Fin n ⊕ Fin n → K)
          (jEmb E n (g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))))).comp
        ((LinearMap.proj (Sum.inl i) : (Fin n ⊕ Fin n → K) →ₗ[K] K) +
          (LinearMap.proj (Sum.inr i) : (Fin n ⊕ Fin n → K) →ₗ[K] K)))

omit [CharP K 2] in
theorem bcLin_apply (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    bcLin E n g v = (bcDelta E)⁻¹ • ∑ i : Fin n,
      ((bcSigmaTheta E • v (Sum.inl i) + bcTheta E • v (Sum.inr i)) •
          jEmb E n (g (Pi.single i (1 : K) : Fin n → K)) +
        ((v (Sum.inl i) + v (Sum.inr i)) •
          jEmb E n (g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))))) := by
  simp only [bcLin, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]

theorem bcLin_jEmb_single (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (i : Fin n) :
    bcLin E n g (jEmb E n (Pi.single i (1 : K) : Fin n → K)) =
      jEmb E n (g (Pi.single i (1 : K) : Fin n → K)) := by
  have hδ : bcDelta E ≠ 0 := bcDelta_ne_zero E
  rw [bcLin_apply]
  simp only [jEmb_apply_inl, jEmb_apply_inr]
  have hterm : ∀ k : Fin n,
      (bcSigmaTheta E • (Pi.single i (1 : K) : Fin n → K) k +
          bcTheta E • σ ((Pi.single i (1 : K) : Fin n → K) k)) •
          jEmb E n (g (Pi.single k (1 : K) : Fin n → K)) +
        (((Pi.single i (1 : K) : Fin n → K) k + σ ((Pi.single i (1 : K) : Fin n → K) k)) •
          jEmb E n (g (bcTheta E • (Pi.single k (1 : K) : Fin n → K)))) =
      if k = i then bcDelta E • jEmb E n (g (Pi.single k (1 : K) : Fin n → K)) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl]
      simp only [Pi.single_eq_same, map_one, smul_eq_mul, mul_one, CharTwo.add_self_eq_zero,
        zero_smul, add_zero]
      rw [show bcSigmaTheta E + bcTheta E = bcDelta E by rw [add_comm]; rfl]
    · rw [if_neg hk]
      simp [Pi.single_eq_of_ne' (Ne.symm hk)]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_eq_single i]
  · rw [if_pos rfl, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  · intro k _ hki
    rw [if_neg hki]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem bcLin_jEmb_bcTheta_single (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (i : Fin n) :
    bcLin E n g (jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) =
      jEmb E n (g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
  have hδ : bcDelta E ≠ 0 := bcDelta_ne_zero E
  rw [bcLin_apply]
  simp only [jEmb_apply_inl, jEmb_apply_inr]
  have hterm : ∀ k : Fin n,
      (bcSigmaTheta E • (bcTheta E • (Pi.single i (1 : K) : Fin n → K)) k +
          bcTheta E • σ ((bcTheta E • (Pi.single i (1 : K) : Fin n → K)) k)) •
          jEmb E n (g (Pi.single k (1 : K) : Fin n → K)) +
        (((bcTheta E • (Pi.single i (1 : K) : Fin n → K)) k +
            σ ((bcTheta E • (Pi.single i (1 : K) : Fin n → K)) k)) •
          jEmb E n (g (bcTheta E • (Pi.single k (1 : K) : Fin n → K)))) =
      if k = i then
        bcDelta E • jEmb E n (g (bcTheta E • (Pi.single k (1 : K) : Fin n → K))) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl]
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one, bcSigmaTheta]
      rw [show σ (bcTheta E) * bcTheta E + bcTheta E * σ (bcTheta E) = 0 from by
            rw [mul_comm (σ (bcTheta E)) (bcTheta E), CharTwo.add_self_eq_zero],
        show bcTheta E + σ (bcTheta E) = bcDelta E from rfl, zero_smul, zero_add]
    · rw [if_neg hk]
      simp [Pi.single_eq_of_ne' (Ne.symm hk)]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_eq_single i]
  · rw [if_pos rfl, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  · intro k _ hki
    rw [if_neg hki]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem bcLin_jEmb (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (x : Fin n → K) :
    bcLin E n g (jEmb E n x) = jEmb E n (g x) := by
  obtain ⟨a, b, hx⟩ := exists_eq_sum_smul_single (E := E) n x
  have hjx : jEmb E n x = ∑ i : Fin n,
      (a i • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
        b i • jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    rw [hx, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, map_smul, map_smul]
  have hgx : g x = ∑ i : Fin n,
      (a i • g (Pi.single i (1 : K) : Fin n → K) +
        b i • g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    rw [hx, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, map_smul, map_smul]
  rw [hjx, map_sum, hgx, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : bcLin E n g (a i • jEmb E n (Pi.single i (1 : K) : Fin n → K) +
      b i • jEmb E n (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) =
      a i • jEmb E n (g (Pi.single i (1 : K) : Fin n → K)) +
        b i • jEmb E n (g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    conv_lhs => rw [LinearMap.map_add, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, bcLin_jEmb_single, bcLin_jEmb_bcTheta_single]
  have h2 : jEmb E n (a i • g (Pi.single i (1 : K) : Fin n → K) +
      b i • g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) =
      a i • jEmb E n (g (Pi.single i (1 : K) : Fin n → K)) +
        b i • jEmb E n (g (bcTheta E • (Pi.single i (1 : K) : Fin n → K))) := by
    conv_lhs => rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  rw [h1, h2]

theorem eq_of_eqOn_range_jEmb (E : QuadExt F K σ) (n : ℕ)
    {f g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (h : ∀ x : Fin n → K, f (jEmb E n x) = g (jEmb E n x)) : f = g := by
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ Submodule.span K (Set.range (jEmb (F := F) E n)) := by
    rw [span_range_jEmb]
    exact Submodule.mem_top
  refine Submodule.span_induction (s := Set.range (jEmb (F := F) E n))
    (p := fun w _ => f w = g w) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, rfl⟩
    exact h x
  · simp
  · intro u w _ _ hu hw
    rw [map_add, map_add, hu, hw]
  · intro c u _ hu
    rw [map_smul, map_smul, hu]

theorem bcLin_id (E : QuadExt F K σ) (n : ℕ) :
    bcLin E n (LinearMap.id : (Fin n → K) →ₗ[F] (Fin n → K)) = LinearMap.id := by
  refine eq_of_eqOn_range_jEmb E n fun x => ?_
  rw [bcLin_jEmb]
  rfl

theorem bcLin_comp (E : QuadExt F K σ) (n : ℕ)
    (g h : (Fin n → K) →ₗ[F] (Fin n → K)) :
    bcLin E n (g.comp h) = (bcLin E n g).comp (bcLin E n h) := by
  refine eq_of_eqOn_range_jEmb E n fun x => ?_
  rw [LinearMap.comp_apply, bcLin_jEmb, bcLin_jEmb, bcLin_jEmb]
  rfl

theorem bcLin_dFlip (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    bcLin E n g (dFlip σ v) = dFlip σ (bcLin E n g v) := by
  let W : Submodule K (Fin n ⊕ Fin n → K) :=
    { carrier := {v | bcLin E n g (dFlip σ v) = dFlip σ (bcLin E n g v)}
      zero_mem' := by
        rw [Set.mem_setOf_eq, map_zero]
        have h0 : dFlip σ (0 : Fin n ⊕ Fin n → K) = 0 := by
          ext x
          cases x <;> simp [dFlip]
        rw [h0, map_zero]
      add_mem' := by
        intro u v hu hv
        rw [Set.mem_setOf_eq] at hu hv ⊢
        rw [dFlip_add, map_add, hu, hv, ← dFlip_add, map_add]
      smul_mem' := by
        intro c u hu
        rw [Set.mem_setOf_eq] at hu ⊢
        rw [dFlip_smul, map_smul, hu, ← dFlip_smul, ← map_smul] }
  have htop : W = ⊤ := by
    rw [eq_top_iff, ← span_range_jEmb E n]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨x, rfl⟩
    show bcLin E n g (dFlip σ (jEmb E n x)) = dFlip σ (bcLin E n g (jEmb E n x))
    rw [dFlip_jEmb, bcLin_jEmb, dFlip_jEmb]
  have hv : v ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hv

noncomputable def bc (E : QuadExt F K σ) (n : ℕ) :
    ((Fin n → K) ≃ₗ[F] (Fin n → K)) →* ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) where
  toFun g :=
    LinearEquiv.ofLinearMap (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))
      (bcLin E n (g.symm : (Fin n → K) →ₗ[F] (Fin n → K)))
      (by
        rw [← bcLin_comp]
        have h : ((g : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)).comp
            ((g.symm : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) =
            LinearMap.id := by
          ext v
          simp
        rw [h, bcLin_id])
      (by
        rw [← bcLin_comp]
        have h : ((g.symm : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)).comp
            ((g : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) =
            LinearMap.id := by
          ext v
          simp
        rw [h, bcLin_id])
  map_one' := by
    apply LinearEquiv.ext
    intro v
    show bcLin E n (((1 : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
      (Fin n → K) →ₗ[F] (Fin n → K))) v = v
    rw [show ((1 : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) =
      LinearMap.id from rfl, bcLin_id]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    show bcLin E n (((g * h : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
      (Fin n → K) →ₗ[F] (Fin n → K))) v =
      bcLin E n ((g : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K))
        (bcLin E n ((h : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) v)
    rw [show (((g * h : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
        (Fin n → K) →ₗ[F] (Fin n → K))) =
        ((g : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)).comp
          ((h : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) from rfl]
    rw [bcLin_comp, LinearMap.comp_apply]

theorem bc_apply_jEmb (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) (x : Fin n → K) :
    bc E n g (jEmb E n x) = jEmb E n (g x) :=
  bcLin_jEmb E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) x

theorem bc_dFlip (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    bc E n g (dFlip σ v) = dFlip σ (bc E n g v) :=
  bcLin_dFlip E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v

theorem bc_injective (E : QuadExt F K σ) (n : ℕ) : Function.Injective (bc E n) := by
  intro g h hgh
  have h' : ∀ x : Fin n → K, jEmb E n (g x) = jEmb E n (h x) := by
    intro x
    rw [← bc_apply_jEmb, ← bc_apply_jEmb]
    exact congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) => e (jEmb E n x)) hgh
  exact LinearEquiv.ext fun x => jEmb_injective E n (h' x)

theorem polar_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (hg : ∀ x, Qn E n (g x) = Qn E n x)
    (u v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (bcLin E n g u) (bcLin E n g v) = polar (quadPlus n K) u v := by
  have hbase : ∀ x y : Fin n → K,
      polar (quadPlus n K) (bcLin E n g (jEmb E n x)) (bcLin E n g (jEmb E n y)) =
        polar (quadPlus n K) (jEmb E n x) (jEmb E n y) := by
    intro x y
    rw [bcLin_jEmb, bcLin_jEmb, polar_jEmb, polar_jEmb]
    congr 1
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hg, hg, hg]
  have h₁ : ∀ u ∈ Submodule.span K (Set.range (jEmb (F := F) E n)), ∀ y : Fin n → K,
      polar (quadPlus n K) (bcLin E n g u) (bcLin E n g (jEmb E n y)) =
        polar (quadPlus n K) u (jEmb E n y) := by
    intro u hu
    refine Submodule.span_induction
      (p := fun u _ => ∀ y : Fin n → K,
        polar (quadPlus n K) (bcLin E n g u) (bcLin E n g (jEmb E n y)) =
          polar (quadPlus n K) u (jEmb E n y)) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨x, rfl⟩ y
      exact hbase x y
    · intro y
      simp
    · intro u w _ _ hu hw y
      rw [LinearMap.map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, hu y, hw y]
    · intro c u _ hu y
      rw [LinearMap.map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, hu y]
  have h₂ : ∀ u ∈ Submodule.span K (Set.range (jEmb (F := F) E n)),
      ∀ v ∈ Submodule.span K (Set.range (jEmb (F := F) E n)),
      polar (quadPlus n K) (bcLin E n g u) (bcLin E n g v) = polar (quadPlus n K) u v := by
    intro u hu v hv
    refine Submodule.span_induction
      (p := fun v _ => polar (quadPlus n K) (bcLin E n g u) (bcLin E n g v) =
        polar (quadPlus n K) u v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨y, rfl⟩
      exact h₁ u hu y
    · simp
    · intro v w _ _ hv hw
      rw [LinearMap.map_add, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, hv, hw]
    · intro c v _ hv
      rw [LinearMap.map_smul, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hv]
  exact h₂ u (by rw [span_range_jEmb]; exact Submodule.mem_top) v
    (by rw [span_range_jEmb]; exact Submodule.mem_top)
theorem bc_mem_orthogonalGroup_iff (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    bc E n g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
  constructor
  · intro hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (jEmb E n x)
    rw [bc_apply_jEmb, quadPlus_jEmb, quadPlus_jEmb] at h
    exact (algebraMap F K).injective h
  · intro hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    have hgm : ∀ x : Fin n → K,
        Qn E n ((g : (Fin n → K) →ₗ[F] (Fin n → K)) x) = Qn E n x := fun x =>
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x
    have hpol := polar_bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) hgm
    have hQ : ∀ v, quadPlus n K (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v) =
        quadPlus n K v := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range (jEmb (F := F) E n)) := by
        rw [span_range_jEmb]
        exact Submodule.mem_top
      refine Submodule.span_induction
        (p := fun v _ => quadPlus n K (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v) =
          quadPlus n K v) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨x, rfl⟩
        rw [bcLin_jEmb, quadPlus_jEmb, quadPlus_jEmb, hgm x]
      · simp
      · intro u w _ _ hu hw
        rw [LinearMap.map_add, QuadraticMap.map_add (quadPlus n K),
          QuadraticMap.map_add (quadPlus n K), hu, hw, hpol u w]
      · intro c u _ hu
        rw [LinearMap.map_smul, QuadraticMap.map_smul, hu, QuadraticMap.map_smul]
    intro v
    exact hQ v

theorem flipHerm_bc (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ (bc E n g u) (bc E n g v) = flipHerm σ u v := by
  have hmem : bc E n g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    (bc_mem_orthogonalGroup_iff E n g).mpr hg
  rw [flipHerm, flipHerm, ← bc_dFlip,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmem]

theorem exists_bc_eq (E : QuadExt F K σ) (n : ℕ)
    (h : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (hh : ∀ v, h (dFlip σ v) = dFlip σ (h v)) :
    ∃ g : (Fin n → K) ≃ₗ[F] (Fin n → K), bc E n g = h := by
  let hL : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) := h.toLinearMap
  let gLin : (Fin n → K) →ₗ[F] (Fin n → K) :=
    { toFun := fun x i => hL (jEmb E n x) (Sum.inl i)
      map_add' := by
        intro x y
        funext i
        rw [show jEmb E n (x + y) = jEmb E n x + jEmb E n y from
          map_add (jEmb E n) x y, LinearMap.map_add]
        rfl
      map_smul' := by
        intro c x
        funext i
        rw [show jEmb E n (c • x) = c • jEmb E n x from LinearMap.map_smul (jEmb E n) c x,
          LinearMap.map_smul_of_tower hL]
        rfl }
  have hgLin_jEmb : ∀ x : Fin n → K, jEmb E n (gLin x) = hL (jEmb E n x) := by
    intro x
    have hfix : dFlip σ (hL (jEmb E n x)) = hL (jEmb E n x) := by
      rw [← show hL (dFlip σ (jEmb E n x)) = dFlip σ (hL (jEmb E n x)) from hh (jEmb E n x),
        dFlip_jEmb]
    obtain ⟨y, hy⟩ := (mem_range_jEmb_iff E n (hL (jEmb E n x))).mpr hfix
    have hy' : y = gLin x := by
      funext i
      have h := congrFun hy (Sum.inl i)
      rw [jEmb_apply_inl] at h
      exact h
    rw [← hy', hy]
  have hgLin_inj : Function.Injective gLin := by
    intro x y hxy
    apply jEmb_injective E n
    apply h.injective
    change hL (jEmb E n x) = hL (jEmb E n y)
    rw [← hgLin_jEmb x, ← hgLin_jEmb y, hxy]
  have hgLin_surj : Function.Surjective gLin := by
    intro y
    let v : Fin n ⊕ Fin n → K := h.symm (jEmb E n y)
    have hv : hL v = jEmb E n y := by
      exact h.apply_symm_apply (jEmb E n y)
    have hfix : dFlip σ v = v := by
      apply h.injective
      change hL (dFlip σ v) = hL v
      rw [show hL (dFlip σ v) = dFlip σ (hL v) from hh v, hv, dFlip_jEmb]
    obtain ⟨x, hx⟩ := (mem_range_jEmb_iff E n v).mpr hfix
    refine ⟨x, ?_⟩
    funext i
    have h1 : gLin x i = hL (jEmb E n x) (Sum.inl i) := rfl
    rw [h1, hx, hv, jEmb_apply_inl]
  let g : (Fin n → K) ≃ₗ[F] (Fin n → K) := LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩
  have hbc : bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) = hL := by
    refine eq_of_eqOn_range_jEmb E n fun x => ?_
    rw [bcLin_jEmb]
    exact hgLin_jEmb x
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  show bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v = hL v
  rw [hbc]

noncomputable def blockDiag (σ : K ≃+* K) (n : ℕ) (S : Matrix (Fin n) (Fin n) K) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
  LinearMap.pi fun x => match x with
    | .inl i => (LinearMap.proj i).comp ((Matrix.mulVecLin S).comp
        (LinearMap.pi fun j => LinearMap.proj (Sum.inl j)))
    | .inr i => (LinearMap.proj i).comp ((Matrix.mulVecLin (S.map σ)).comp
        (LinearMap.pi fun j => LinearMap.proj (Sum.inr j)))

omit [CharP K 2] in
theorem blockDiag_inl (n : ℕ) (S : Matrix (Fin n) (Fin n) K)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    blockDiag σ n S v (Sum.inl i) = S.mulVec (fun j => v (Sum.inl j)) i := by
  have h : (LinearMap.pi fun j => LinearMap.proj (Sum.inl j) :
      (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n → K)) v = fun j => v (Sum.inl j) := by
    funext j
    rw [LinearMap.pi_apply, LinearMap.proj_apply]
  simpa [blockDiag] using congrArg (fun w => S.mulVec w i) h

omit [CharP K 2] in
theorem blockDiag_inr (n : ℕ) (S : Matrix (Fin n) (Fin n) K)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    blockDiag σ n S v (Sum.inr i) = (S.map σ).mulVec (fun j => v (Sum.inr j)) i := by
  have h : (LinearMap.pi fun j => LinearMap.proj (Sum.inr j) :
      (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n → K)) v = fun j => v (Sum.inr j) := by
    funext j
    rw [LinearMap.pi_apply, LinearMap.proj_apply]
  simpa [blockDiag] using congrArg (fun w => (S.map σ).mulVec w i) h
theorem bcLin_suEndN (E : QuadExt F K σ) (n : ℕ) (s : SUid σ n) :
    bcLin E n (suEndN (F := F) σ n s : (Fin n → K) →ₗ[F] (Fin n → K)) =
      blockDiag σ n ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine eq_of_eqOn_range_jEmb E n fun x => ?_
  ext j
  cases j with
  | inl i =>
    rw [bcLin_jEmb, blockDiag_inl]
    change (suEndN (F := F) σ n s : (Fin n → K) ≃ₗ[F] (Fin n → K)) x i = _
    rw [suEndN_apply (F := F) σ n s x, CFSG.ClassicalGroups.Unitary.smul_def,
      show (fun j => jEmb E n x (Sum.inl j)) = x from by funext j; rw [jEmb_apply_inl]]
  | inr i =>
    rw [bcLin_jEmb, blockDiag_inr]
    change σ ((suEndN (F := F) σ n s : (Fin n → K) ≃ₗ[F] (Fin n → K)) x i) = _
    rw [suEndN_apply (F := F) σ n s x, CFSG.ClassicalGroups.Unitary.smul_def,
      show (fun j => jEmb E n x (Sum.inr j)) = fun j => σ (x j) from by
        funext j; rw [jEmb_apply_inr]]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem bc_suEndN (E : QuadExt F K σ) (n : ℕ) (s : SUid σ n) (v : Fin n ⊕ Fin n → K) :
    (∀ i : Fin n, bc E n (suEndN (F := F) σ n s) v (Sum.inl i) =
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
          (fun j => v (Sum.inl j)) i) ∧
      (∀ i : Fin n, bc E n (suEndN (F := F) σ n s) v (Sum.inr i) =
        ((((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map σ).mulVec
          (fun j => v (Sum.inr j)) i) := by
  have hbc : ∀ w : Fin n ⊕ Fin n → K, bc E n (suEndN (F := F) σ n s) w =
      blockDiag σ n ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w := by
    intro w
    show bcLin E n (suEndN (F := F) σ n s : (Fin n → K) →ₗ[F] (Fin n → K)) w =
      blockDiag σ n ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w
    rw [bcLin_suEndN]
  constructor
  · intro i
    rw [hbc, blockDiag_inl]
  · intro i
    rw [hbc, blockDiag_inr]

noncomputable def swapAt (n : ℕ) (k : Fin n) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
  LinearMap.pi fun x => match x with
    | .inl i => if i = k then LinearMap.proj (Sum.inr i) else LinearMap.proj (Sum.inl i)
    | .inr i => if i = k then LinearMap.proj (Sum.inl i) else LinearMap.proj (Sum.inr i)

omit [CharP K 2] in
theorem swapAt_inl (n : ℕ) (k : Fin n) (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    swapAt n k v (Sum.inl i) = if i = k then v (Sum.inr i) else v (Sum.inl i) := by
  simp only [swapAt, LinearMap.pi_apply]
  split_ifs <;> rfl

omit [CharP K 2] in
theorem swapAt_inr (n : ℕ) (k : Fin n) (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    swapAt n k v (Sum.inr i) = if i = k then v (Sum.inl i) else v (Sum.inr i) := by
  simp only [swapAt, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem bcLin_tauAt (E : QuadExt F K σ) (n : ℕ) (k : Fin n) :
    bcLin E n ((tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) : (Fin n → K) →ₗ[F] (Fin n → K)) =
      swapAt n k := by
  refine eq_of_eqOn_range_jEmb E n fun x => ?_
  ext j
  cases j with
  | inl i =>
    rw [bcLin_jEmb, swapAt_inl]
    change (tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) x i =
      if i = k then jEmb E n x (Sum.inr i) else jEmb E n x (Sum.inl i)
    rw [tauAt_apply]
    by_cases h : i = k
    · rw [if_pos h, if_pos h, jEmb_apply_inr]
    · rw [if_neg h, if_neg h, jEmb_apply_inl]
  | inr i =>
    rw [bcLin_jEmb, swapAt_inr]
    change σ ((tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) x i) =
      if i = k then jEmb E n x (Sum.inl i) else jEmb E n x (Sum.inr i)
    rw [tauAt_apply]
    by_cases h : i = k
    · rw [if_pos h, if_pos h, jEmb_apply_inl, E.isUnitary.invol]
    · rw [if_neg h, if_neg h, jEmb_apply_inr]

theorem bc_tauAt (E : QuadExt F K σ) (n : ℕ) (k : Fin n) (v : Fin n ⊕ Fin n → K) :
    (∀ i : Fin n, bc E n (tauAt E k) v (Sum.inl i) =
        if i = k then v (Sum.inr i) else v (Sum.inl i)) ∧
      (∀ i : Fin n, bc E n (tauAt E k) v (Sum.inr i) =
        if i = k then v (Sum.inl i) else v (Sum.inr i)) := by
  have hbc : bcLin E n ((tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
      (Fin n → K) →ₗ[F] (Fin n → K)) = swapAt n k := bcLin_tauAt E n k
  constructor
  · intro i
    change bcLin E n ((tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
      (Fin n → K) →ₗ[F] (Fin n → K)) v (Sum.inl i) = _
    rw [hbc, swapAt_inl]
  · intro i
    change bcLin E n ((tauAt E k : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
      (Fin n → K) →ₗ[F] (Fin n → K)) v (Sum.inr i) = _
    rw [hbc, swapAt_inr]

end CFSG.ClassicalInvolution.PhanDn
