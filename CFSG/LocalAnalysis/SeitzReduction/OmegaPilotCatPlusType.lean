module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldGalois
public import CFSG.LocalAnalysis.SteinbergCEAnisotropicNormIsometry
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap Module
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.GroupTheory.WeirSylow (IsPlusType)

theorem quadratic_eq_zero_of_mem_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) {ι : Type*} (x : ι → M) (hQ : ∀ i, Q (x i) = 0)
    (hP : ∀ i j, polar Q (x i) (x j) = 0) {v : M} (hv : v ∈ Submodule.span R (Set.range x)) :
    Q v = 0 := by
  set S := Submodule.span R (Set.range x)
  have h1 : ∀ y ∈ S, ∀ j, polar Q y (x j) = 0 := by
    intro y hy j
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hP i j
    | zero => exact polar_zero_left _ _
    | add y z _ _ hy hz => rw [polar_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [polar_smul_left, hy, smul_zero]
  have h2 : ∀ y ∈ S, ∀ z ∈ S, polar Q y z = 0 := by
    intro y hy z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h1 y hy j
    | zero => exact polar_zero_right _ _
    | add z w _ _ hz hw => rw [polar_add_right, hz, hw, add_zero]
    | smul a z _ hz => rw [polar_smul_right, hz, smul_zero]
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hQ i
  | zero => exact map_zero Q
  | add y z hy' hz' hy hz => rw [QuadraticMap.map_add Q y z, hy, hz, h2 y hy' z hz', add_zero, add_zero]
  | smul a y _ hy => rw [QuadraticMap.map_smul, hy, smul_zero]

theorem exists_root_of_finrank_two {k E : Type*} [Field k] [Fintype k] [CharP k 2] [Field E]
    [Algebra k E] (hE : finrank k E = 2) {β γ : k} (hirr : ∀ s : k, s ^ 2 + β * s + γ ≠ 0) :
    ∃ r : E, r ^ 2 + algebraMap k E β * r + algebraMap k E γ = 0 := by
  have hγ : γ ≠ 0 := fun h => hirr 0 (by simp [h])
  obtain ⟨δ, hδ⟩ := isSquare_of_charTwo' γ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hγ (by simpa using hδ)
  have hQ : ∀ x y : k, x ^ 2 + β / δ * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    by_cases hy : y = 0
    · subst hy
      simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at h
      exact ⟨pow_eq_zero_iff (by norm_num) |>.mp h, rfl⟩
    · exfalso
      refine hirr (δ * x / y) ?_
      have e : (δ * x / y) ^ 2 + β * (δ * x / y) + γ =
          δ ^ 2 / y ^ 2 * (x ^ 2 + β / δ * x * y + y ^ 2) := by
        rw [hδ]
        field_simp
      rw [e, h, mul_zero]
  obtain ⟨ζ, hζ⟩ := LocalAnalysis.exists_root_quadratic hE hQ
  refine ⟨algebraMap k E δ * ζ, ?_⟩
  have hD : algebraMap k E δ ≠ 0 := (map_ne_zero (algebraMap k E)).mpr hδ0
  have e : (algebraMap k E δ * ζ) ^ 2 + algebraMap k E β * (algebraMap k E δ * ζ) +
      algebraMap k E γ = algebraMap k E δ ^ 2 *
        (ζ ^ 2 + algebraMap k E (β / δ) * ζ + 1) := by
    rw [map_div₀, hδ, map_mul]
    field_simp
  rw [e, hζ, mul_zero]

section PlusType

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isPlusType_of_semilinear_involution {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 1 ≤ n) (hdim : finrank K V = 2 * n) {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {T : V →ₛₗ[(σ : K →+* K)] V} (hTT : ∀ v, T (T v) = v) (hTQ : ∀ v, Q (T v) = σ (Q v)) :
    IsPlusType Q := by
  classical
  have hσσ' : ∀ a, σ (σ a) = a := fun a => by
    change (σ * σ) a = a
    rw [hσσ]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ :=
    even_quadratic_semilinear_involution_descent hσσ hσ1 hQ hTT hTQ
  obtain ⟨hfeven, hk, -⟩ := card_descentField hf hK hσσ hσ1
  have hf2 : 1 ≤ f / 2 := by
    obtain ⟨j, hj⟩ := hfeven
    omega
  have : CharP (descentField σ) 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf2 hk
  have : Finite (descentField σ) := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : FiniteDimensional (descentField σ) (fixSpace T) := finite_fixSpace
  have hB := fun {ι : Type} (b : Basis ι (descentField σ) (fixSpace T)) =>
    linearIndependent_fixSpace hσσ' hc b
  have hdimW : finrank (descentField σ) (fixSpace T) = 2 * n := by rw [hfin, hdim]
  have hpolar : ∀ w w' : fixSpace T,
      polar Q (w : V) (w' : V) = ((polar (descentForm hTQ) w w' : descentField σ) : K) :=
    fun w w' => (coe_polar_descentForm hTQ w w').symm
  have hpolar₀ : ∀ w w' : fixSpace T, polar (descentForm hTQ) w w' =
      descentForm hTQ (w + w') - descentForm hTQ w - descentForm hTQ w' := fun _ _ => rfl
  have hval : ∀ w : fixSpace T, Q (w : V) = ((descentForm hTQ w : descentField σ) : K) :=
    fun w => (coe_descentForm hTQ w).symm
  rcases (finite_even_regular_quadratic_normal_forms (descentForm hTQ) hQ₀).2.2.1 n hn hdimW with
    ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  ·
    set S := Submodule.span (descentField σ) (Set.range fun i => b (.inl i)) with hS
    have hvan : ∀ w ∈ S, descentForm hTQ w = 0 := by
      intro w hw
      obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
      simpa using hb x 0
    have hmem : ∀ i, b (.inl i) ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
    set e : Fin n → V := fun i => ((b (.inl i) : fixSpace T) : V) with he
    have hQe : ∀ i, Q (e i) = 0 := fun i => by
      rw [he, hval, hvan _ (hmem i), ZeroMemClass.coe_zero]
    have hPe : ∀ i j, polar Q (e i) (e j) = 0 := fun i j => by
      rw [he, hpolar, hpolar₀, hvan _ (hmem i), hvan _ (hmem j),
        hvan _ (add_mem (hmem i) (hmem j)), sub_zero, sub_zero, ZeroMemClass.coe_zero]
    have hli : LinearIndependent K e := (hB b).comp Sum.inl Sum.inl_injective
    refine ⟨Submodule.span K (Set.range e), ?_,
      fun v hv => quadratic_eq_zero_of_mem_span Q e hQe hPe hv⟩
    rw [finrank_span_eq_card hli, Fintype.card_fin, hdim]
  ·
    set S := Submodule.span (descentField σ) (Set.range fun i => b (.inl i)) with hS
    set u₀ := b (.inr (.inr 0)) with hu₀
    set w₀ := b (.inr (.inr 1)) with hw₀
    have hform : ∀ w ∈ S, ∀ s t : descentField σ,
        descentForm hTQ (w + s • u₀ + t • w₀) = s ^ 2 + β * s * t + γ * t ^ 2 := by
      intro w hw s t
      obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
      simpa using hb x 0 s t
    have hS0 : ∀ w ∈ S, descentForm hTQ w = 0 := fun w hw => by
      simpa using hform w hw 0 0
    have hu : descentForm hTQ u₀ = 1 := by simpa using hform 0 (zero_mem _) 1 0
    have hwv : descentForm hTQ w₀ = γ := by simpa using hform 0 (zero_mem _) 0 1
    have huw : descentForm hTQ (u₀ + w₀) = 1 + β + γ := by
      simpa using hform 0 (zero_mem _) 1 1
    have hSu : ∀ w ∈ S, descentForm hTQ (w + u₀) = 1 := fun w hw => by
      simpa using hform w hw 1 0
    have hSw : ∀ w ∈ S, descentForm hTQ (w + w₀) = γ := fun w hw => by
      simpa using hform w hw 0 1
    have hpSS : ∀ w ∈ S, ∀ w' ∈ S, polar (descentForm hTQ) w w' = 0 := fun w hw w' hw' => by
      rw [hpolar₀, hS0 _ (add_mem hw hw'), hS0 _ hw, hS0 _ hw', sub_zero, sub_zero]
    have hpSu : ∀ w ∈ S, polar (descentForm hTQ) w u₀ = 0 := fun w hw => by
      rw [hpolar₀, hSu w hw, hS0 w hw, hu, sub_zero, sub_self]
    have hpSw : ∀ w ∈ S, polar (descentForm hTQ) w w₀ = 0 := fun w hw => by
      rw [hpolar₀, hSw w hw, hS0 w hw, hwv, sub_zero, sub_self]
    have hpuw : polar (descentForm hTQ) u₀ w₀ = β := by
      rw [hpolar₀, huw, hu, hwv]
      ring
    have hE : finrank (descentField σ) K = 2 := by
      have : Module.Finite (descentField σ) K := Module.finite_iff_finite.mpr inferInstance
      have h1 := Module.natCard_eq_pow_finrank (K := descentField σ) (V := K)
      rw [hK, hk, ← pow_mul] at h1
      have h2 := Nat.pow_right_injective (le_refl 2) h1
      obtain ⟨j, hj⟩ := hfeven
      have hj2 : f / 2 = j := by omega
      rw [hj2] at h2
      have h3 : j * finrank (descentField σ) K = j * 2 := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) h3
    have : Fintype (descentField σ) := Fintype.ofFinite _
    obtain ⟨r, hr⟩ := exists_root_of_finrank_two (k := descentField σ) (E := K) hE hroot
    change r ^ 2 + (β : K) * r + (γ : K) = 0 at hr
    have hmem : ∀ i, b (.inl i) ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
    set e : Fin (n - 1) → V := fun i => ((b (.inl i) : fixSpace T) : V) with he
    set u : V := ((u₀ : fixSpace T) : V) with hu'
    set w : V := ((w₀ : fixSpace T) : V) with hw'
    set z : V := r • u + w with hz
    have hQe : ∀ i, Q (e i) = 0 := fun i => by
      rw [he, hval, hS0 _ (hmem i), ZeroMemClass.coe_zero]
    have hPee : ∀ i j, polar Q (e i) (e j) = 0 := fun i j => by
      rw [he, hpolar, hpSS _ (hmem i) _ (hmem j), ZeroMemClass.coe_zero]
    have hQu : Q u = 1 := by rw [hu', hval, hu, OneMemClass.coe_one]
    have hQw : Q w = γ := by rw [hw', hval, hwv]
    have hPeu : ∀ i, polar Q (e i) u = 0 := fun i => by
      rw [he, hu', hpolar, hpSu _ (hmem i), ZeroMemClass.coe_zero]
    have hPew : ∀ i, polar Q (e i) w = 0 := fun i => by
      rw [he, hw', hpolar, hpSw _ (hmem i), ZeroMemClass.coe_zero]
    have hPuw : polar Q u w = β := by rw [hu', hw', hpolar, hpuw]
    have hQz : Q z = 0 := by
      rw [hz, QuadraticMap.map_add Q (r • u) w, QuadraticMap.map_smul, polar_smul_left, hQu, hQw,
        hPuw, smul_eq_mul, smul_eq_mul]
      linear_combination hr
    have hPez : ∀ i, polar Q (e i) z = 0 := fun i => by
      rw [hz, polar_add_right, polar_smul_right, hPeu, hPew, smul_zero, add_zero]
    have hPzz : polar Q z z = 0 := by rw [polar_self, hQz, smul_zero]
    set x : Fin (n - 1) ⊕ Unit → V := Sum.elim e (fun _ => z) with hx
    have hQx : ∀ j, Q (x j) = 0 := by
      rintro (i | ⟨⟩)
      · exact hQe i
      · exact hQz
    have hPx : ∀ j j', polar Q (x j) (x j') = 0 := by
      rintro (i | ⟨⟩) (j | ⟨⟩)
      · exact hPee i j
      · exact hPez i
      · rw [polar_comm]
        exact hPez j
      · exact hPzz
    set φ : Fin (n - 1) ⊕ Fin 2 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 :=
      Sum.elim Sum.inl (fun j => Sum.inr (Sum.inr j)) with hφdef
    have hφ : Function.Injective φ := by
      rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (Sum.inl_injective h)
      · exact (Sum.inl_ne_inr h).elim
      · exact (Sum.inr_ne_inl h).elim
      · exact congrArg Sum.inr (Sum.inr_injective (Sum.inr_injective h))
    have hB' := (hB b).comp φ hφ
    have hli : LinearIndependent K x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hsum : ∑ j, (Sum.elim (fun i => g (.inl i)) ![g (.inr ()) * r, g (.inr ())] j) •
          (((b (φ j)) : fixSpace T) : V) = 0 := by
        rw [Fintype.sum_sum_type, Fin.sum_univ_two]
        rw [Fintype.sum_sum_type] at hg
        simp only [hx, hφdef, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, Finset.univ_unique, Finset.sum_singleton] at hg ⊢
        rw [← hg, hz, smul_add, smul_smul]
      have key := Fintype.linearIndependent_iff.mp hB' _ hsum
      rintro (i | ⟨⟩)
      · simpa using key (.inl i)
      · simpa using key (.inr 1)
    refine ⟨Submodule.span K (Set.range x), ?_,
      fun v hv => quadratic_eq_zero_of_mem_span Q x hQx hPx hv⟩
    rw [finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, hdim]
    omega

end PlusType

end CFSG.SeitzReduction.OmegaPilot
