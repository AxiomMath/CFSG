module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanU0

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

variable {a : ℕ} {c e : K}

theorem closure_eq_top_of_eq_top (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup K} (hΛ : Λ = ⊤) {x : K × K × K} :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  subst hΛ
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
  by_contra hne
  obtain ⟨β, hβ, hβH⟩ := exists_ne_zero_trace_mul_eq_zero_of_ne_top hne
  obtain ⟨u, hux⟩ : ∃ u, u = x.1 := ⟨_, rfl⟩
  obtain ⟨r, hrx⟩ : ∃ r, r = x.2.1 := ⟨_, rfl⟩
  obtain ⟨s, hsx⟩ : ∃ s, s = x.2.2 := ⟨_, rfl⟩
  let φ : K →+* K := iterateFrobenius K 2 (a + 1)
  let ψ : K →+* K := iterateFrobenius K 2 a
  have hφ : ∀ y, φ y = y ^ 2 ^ (a + 1) := fun y => iterateFrobenius_def (p := 2) (a + 1) y
  have hψ : ∀ y, ψ y = y ^ 2 ^ a := fun y => iterateFrobenius_def (p := 2) a y
  have hφψ : ∀ y, φ (ψ y) = y := fun y => by rw [hψ, hφ, pow_sigma_pow_theta hK]
  have hφsq : ∀ y, φ y = ψ y ^ 2 := fun y => by rw [hφ, hψ, ← pow_mul, pow_succ]
  have trφ : ∀ γ t, Algebra.trace (ZMod 2) K (γ * φ t) = Algebra.trace (ZMod 2) K (ψ γ * t) :=
    fun γ t => by rw [hφ, hψ]; exact trace_mul_pow_theta hK γ t
  have trψ : ∀ γ t, Algebra.trace (ZMod 2) K (γ * ψ t) = Algebra.trace (ZMod 2) K (φ γ * t) :=
    fun γ t => by rw [hφ, hψ]; exact trace_mul_pow_sigma hK γ t
  obtain ⟨C, hCdef⟩ : ∃ C, C = φ (β * c) := ⟨_, rfl⟩
  let Madd : K × K × K →+ K :=
    { toFun := fun z => commMap a c x z
      map_zero' := by simp [commMap]
      map_add' := fun z z' => commMap_add_right x z z' }
  let M : K × K × K →ₗ[ZMod 2] K := Madd.toZModLinearMap 2
  let Sadd : K →+ K × K × K :=
    { toFun := fun δ => (ψ (δ * u) + φ u * δ + φ c * r * φ δ, φ c * u * φ δ + s * δ, δ * r)
      map_zero' := by simp
      map_add' := fun δ δ' => by
        simp only [map_add, add_mul, mul_add, Prod.mk_add_mk]
        congr 1
        · ring
        · congr 1; ring }
  let S : K →ₗ[ZMod 2] K × K × K := Sadd.toZModLinearMap 2
  let Φadd : K × K × K →+ K × K × K :=
    { toFun := fun z => (ψ (β * z.1) + β * φ z.1 + C * z.2.1, C * z.1 + β * z.2.2, β * z.2.1)
      map_zero' := by simp
      map_add' := fun z z' => by
        simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add, Prod.mk_add_mk]
        congr 1
        · ring
        · congr 1; ring }
  let Φ : K × K × K →ₗ[ZMod 2] K × K × K := Φadd.toZModLinearMap 2
  have hker : LinearMap.ker M ≤ (LinearMap.range S).comap Φ := by
    intro z hz
    have hz0 : commMap a c x z = 0 := hz
    have hmem : ∀ z' : K × K × K, commMap a c x z' = 0 → z' ∈ perp a c ⊤ x :=
      fun z' hz' => ⟨AddSubgroup.mem_top _, hz'⟩
    have hadj : ∀ z' : K × K × K, Algebra.trace (ZMod 2) K (β * commMap a c z z') =
        Algebra.trace (ZMod 2) K ((ψ (β * z.1) + β * φ z.1 + C * z.2.1) * z'.1 +
          (C * z.1 + β * z.2.2) * z'.2.1 + β * z.2.1 * z'.2.2) := fun z' => by
      have e1 : β * commMap a c z z' = β * z.1 * φ z'.1 + β * φ z.1 * z'.1 +
          β * c * ψ z.1 * ψ z'.2.1 + β * c * ψ z.2.1 * ψ z'.1 + β * z.2.2 * z'.2.1 +
          β * z.2.1 * z'.2.2 := by
        simp only [commMap, hφ, hψ, mul_pow]
        ring
      rw [e1, map_add, map_add, map_add, map_add, map_add, trφ, trψ, trψ, hCdef]
      rw [← map_add, ← map_add, ← map_add, ← map_add, ← map_add]
      congr 1
      simp only [map_mul, hφψ]
      ring
    let g : K × K × K →ₗ[ZMod 2] ZMod 2 := (Algebra.trace (ZMod 2) K).comp
      ((LinearMap.mulLeft (ZMod 2) (ψ (β * z.1) + β * φ z.1 + C * z.2.1)).comp
          (LinearMap.fst (ZMod 2) K (K × K)) +
        (LinearMap.mulLeft (ZMod 2) (C * z.1 + β * z.2.2)).comp
          ((LinearMap.fst (ZMod 2) K K).comp (LinearMap.snd (ZMod 2) K (K × K))) +
        (LinearMap.mulLeft (ZMod 2) (β * z.2.1)).comp
          ((LinearMap.snd (ZMod 2) K K).comp (LinearMap.snd (ZMod 2) K (K × K))))
    have hg_apply : ∀ z', g z' = Algebra.trace (ZMod 2) K
        ((ψ (β * z.1) + β * φ z.1 + C * z.2.1) * z'.1 + (C * z.1 + β * z.2.2) * z'.2.1 +
          β * z.2.1 * z'.2.2) := fun z' => rfl
    have hg : ∀ z', M z' = 0 → g z' = 0 := fun z' hz' => by
      rw [hg_apply, ← hadj]
      exact hβH _ (commMap_mem_closure (hmem z hz0) (hmem z' hz'))
    obtain ⟨δ, hδ⟩ := exists_trace_mul_eq_of_ker_le M g hg
    have hadjM : ∀ z' : K × K × K, Algebra.trace (ZMod 2) K (δ * commMap a c x z') =
        Algebra.trace (ZMod 2) K ((ψ (δ * u) + φ u * δ + φ c * r * φ δ) * z'.1 +
          (φ c * u * φ δ + s * δ) * z'.2.1 + δ * r * z'.2.2) := fun z' => by
      have e1 : δ * commMap a c x z' = δ * u * φ z'.1 + δ * φ u * z'.1 +
          δ * c * ψ u * ψ z'.2.1 + δ * c * ψ r * ψ z'.1 + δ * s * z'.2.1 +
          δ * r * z'.2.2 := by
        simp only [commMap, hφ, hψ, mul_pow, ← hux, ← hrx, ← hsx]
        ring
      rw [e1, map_add, map_add, map_add, map_add, map_add, trφ, trψ, trψ]
      rw [← map_add, ← map_add, ← map_add, ← map_add, ← map_add]
      congr 1
      simp only [map_mul, hφψ]
      ring
    have hcmp : ∀ z' : K × K × K, Algebra.trace (ZMod 2) K
        ((ψ (β * z.1) + β * φ z.1 + C * z.2.1) * z'.1 + (C * z.1 + β * z.2.2) * z'.2.1 +
          β * z.2.1 * z'.2.2) =
        Algebra.trace (ZMod 2) K ((ψ (δ * u) + φ u * δ + φ c * r * φ δ) * z'.1 +
          (φ c * u * φ δ + s * δ) * z'.2.1 + δ * r * z'.2.2) := fun z' => by
      rw [← hg_apply, hδ, ← hadjM]
      rfl
    have key : ∀ {p p' : K}, (∀ y, Algebra.trace (ZMod 2) K (p * y) =
        Algebra.trace (ZMod 2) K (p' * y)) → p = p' := fun {p p'} h =>
      sub_eq_zero.mp (eq_zero_of_forall_trace_mul_eq_zero fun y => by
        rw [sub_mul, map_sub, h y, sub_self])
    have h1 := key fun y => by
      have := hcmp (y, 0, 0)
      simp only [mul_zero, add_zero] at this
      exact this
    have h2 := key fun y => by
      have := hcmp (0, y, 0)
      simp only [mul_zero, add_zero, zero_add] at this
      exact this
    have h3 := key fun y => by
      have := hcmp (0, 0, y)
      simp only [mul_zero, zero_add] at this
      exact this
    refine ⟨δ, ?_⟩
    change (Sadd δ : K × K × K) = Φadd z
    simp only [Sadd, Φadd, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h1, h2, h3]
  have hkerΦ : ∀ z z' : K × K × K, Φ z = 0 → Φ z' = 0 → z ≠ 0 → z' ≠ 0 → z = z' := by
    have hsol : ∀ z : K × K × K, Φ z = 0 → z ≠ 0 →
        z.2.1 = 0 ∧ z.2.2 = C * z.1 / β ∧ ψ z.1 = ψ β / β := by
      intro z hz hz0
      have hz' : (ψ (β * z.1) + β * φ z.1 + C * z.2.1, C * z.1 + β * z.2.2, β * z.2.1) =
          (0, 0, 0) := hz
      simp only [Prod.mk.injEq] at hz'
      obtain ⟨e1, e2, e3⟩ := hz'
      have hr0 : z.2.1 = 0 := (mul_eq_zero.mp e3).resolve_left hβ
      have hs0 : z.2.2 = C * z.1 / β := (eq_div_iff hβ).mpr (by
        linear_combination e2 - C * z.1 * (CharTwo.two_eq_zero : (2 : K) = 0))
      have hu0 : z.1 ≠ 0 := by
        intro h
        apply hz0
        rw [h, mul_zero, zero_div] at hs0
        exact Prod.ext h (Prod.ext hr0 hs0)
      refine ⟨hr0, hs0, ?_⟩
      rw [hr0, mul_zero, add_zero, map_mul, hφsq] at e1
      have hψu : ψ z.1 ≠ 0 := (map_ne_zero ψ).mpr hu0
      have h5 : ψ z.1 * (ψ β - β * ψ z.1) = 0 := by
        linear_combination e1 - β * ψ z.1 ^ 2 * (CharTwo.two_eq_zero : (2 : K) = 0)
      have h6 := (mul_eq_zero.mp h5).resolve_left hψu
      exact (eq_div_iff hβ).mpr (by linear_combination -h6)
    intro z z' hz hz' hz0 hz0'
    obtain ⟨a1, a2, a3⟩ := hsol z hz hz0
    obtain ⟨b1, b2, b3⟩ := hsol z' hz' hz0'
    have h1 : z.1 = z'.1 := by
      have : ψ z.1 = ψ z'.1 := by rw [a3, b3]
      rw [hψ, hψ] at this
      exact pow_two_pow_injective a this
    exact Prod.ext h1 (Prod.ext (by rw [a1, b1]) (by rw [a2, b2, h1]))
  have hdimΦ : Module.finrank (ZMod 2) (LinearMap.ker Φ) ≤ 1 := by
    by_cases hbot : LinearMap.ker Φ = ⊥
    · rw [hbot, finrank_bot]; exact Nat.zero_le _
    obtain ⟨z₀, hz₀, hz₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hle : LinearMap.ker Φ ≤ Submodule.span (ZMod 2) {z₀} := by
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Submodule.zero_mem _
      · rw [hkerΦ z z₀ hz hz₀ hz0 hz₀0]; exact Submodule.mem_span_singleton_self z₀
    calc Module.finrank (ZMod 2) (LinearMap.ker Φ)
        ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({z₀} : Set (K × K × K))) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := (finrank_span_singleton hz₀0).le
  have hn : Module.finrank (ZMod 2) K = 2 * a + 1 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, ZMod.card] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have h1 := LinearMap.finrank_range_add_finrank_ker M
  have h2 : Module.finrank (ZMod 2) (K × K × K) = Module.finrank (ZMod 2) K +
      (Module.finrank (ZMod 2) K + Module.finrank (ZMod 2) K) := by
    rw [Module.finrank_prod, Module.finrank_prod]
  have h3 : Module.finrank (ZMod 2) (LinearMap.range M) ≤ Module.finrank (ZMod 2) K :=
    Submodule.finrank_le _
  have h4 : Module.finrank (ZMod 2) (LinearMap.range S) ≤ Module.finrank (ZMod 2) K :=
    LinearMap.finrank_range_le S
  have h5 := Submodule.finrank_mono hker
  have h6 : Module.finrank (ZMod 2) ((LinearMap.range S).comap Φ) ≤
      Module.finrank (ZMod 2) (LinearMap.range S) + Module.finrank (ZMod 2) (LinearMap.ker Φ) := by
    have := LinearMap.lift_rank_comap_le (f := Φ) (LinearMap.range S)
    simp only [Cardinal.lift_id] at this
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at this
    exact_mod_cast this
  omega

end CFSG.ComponentClassification.GMS78.VLike
