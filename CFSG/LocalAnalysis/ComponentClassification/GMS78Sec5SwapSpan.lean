module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanU0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanC0

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

variable {a : ℕ}

omit [Fintype K] in
theorem add_self_eq_zero_prod (z : K × K × K) : z + z = 0 :=
  Prod.ext (CharTwo.add_self_eq_zero _)
    (Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _))

omit [Field K] [Fintype K] [CharP K 2] in
theorem finrank_span_singleton_le_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : V) : Module.finrank K (Submodule.span K ({v} : Set V)) ≤ 1 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; exact Nat.zero_le _
  · exact (finrank_span_singleton hv).le


theorem exists_polar_eq (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) (w : K) :
    ∃ u u' : K, u * u' ^ 2 ^ (a + 1) + u ^ 2 ^ (a + 1) * u' = w := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one ha hK
  have hd : t ^ 2 ^ (a + 1) + t ≠ 0 := by
    intro h
    have hfix : t ^ 2 ^ (a + 1) = t := by
      rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact h
    rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a_succ a) hfix with h0 | h1
    · exact ht0 h0
    · exact ht1 h1
  obtain ⟨l, hl⟩ := pow_theta_add_one_surjective hK (w / (t ^ 2 ^ (a + 1) + t))
  refine ⟨l, l * t, ?_⟩
  simp only at hl
  rw [mul_pow, ← div_mul_cancel₀ w hd, ← hl]
  ring

theorem closure_eq_top_of_index_le_two (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {c e : K} {x : K × K × K} {Y : AddSubgroup (K × K × K)}
    (hYi : ∀ z z' : K × K × K, commMap a c x z = 0 → commMap a c x z' = 0 → z ∉ Y → z' ∉ Y →
      z + z' ∈ Y) :
    AddSubgroup.closure (sqMap a c e '' Y) = ⊤ := by
  classical
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
  have hiso : ∀ z ∈ Y, ∀ z' ∈ Y, Algebra.trace (ZMod 2) K (β * commMap a c z z') = 0 := by
    intro z hz z' hz'
    apply hβH
    have h := sqMap_add (a := a) (c := c) (e := e) z z'
    have hmem : sqMap a c e (z + z') - sqMap a c e z - sqMap a c e z' ∈
        AddSubgroup.closure (sqMap a c e '' Y) :=
      AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _
        (AddSubgroup.subset_closure ⟨_, Y.add_mem hz hz', rfl⟩)
        (AddSubgroup.subset_closure ⟨z, hz, rfl⟩)) (AddSubgroup.subset_closure ⟨z', hz', rfl⟩)
    rwa [h, show sqMap a c e z + sqMap a c e z' + commMap a c z z' - sqMap a c e z -
      sqMap a c e z' = commMap a c z z' by ring] at hmem
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : K × K × K, (∃ w, commMap a c x w = 0 ∧ w ∉ Y) →
      commMap a c x z₀ = 0 ∧ z₀ ∉ Y := by
    by_cases hex : ∃ w, commMap a c x w = 0 ∧ w ∉ Y
    · obtain ⟨w, hw⟩ := hex
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hex⟩
  let pair : K × K × K →ₗ[ZMod 2] K :=
    (LinearMap.mulRight (ZMod 2) z₀.1).comp (LinearMap.fst (ZMod 2) K (K × K)) +
      (LinearMap.mulRight (ZMod 2) z₀.2.1).comp
        ((LinearMap.fst (ZMod 2) K K).comp (LinearMap.snd (ZMod 2) K (K × K))) +
      (LinearMap.mulRight (ZMod 2) z₀.2.2).comp
        ((LinearMap.snd (ZMod 2) K K).comp (LinearMap.snd (ZMod 2) K (K × K)))
  have hpair : ∀ p : K × K × K, pair p = p.1 * z₀.1 + p.2.1 * z₀.2.1 + p.2.2 * z₀.2.2 :=
    fun p => rfl
  let ℓ : K × K × K →ₗ[ZMod 2] ZMod 2 := (Algebra.trace (ZMod 2) K).comp (pair.comp Φ)
  let Ylin : Submodule (ZMod 2) (K × K × K) := AddSubgroup.toZModSubmodule 2 Y
  let Y₀ : Submodule (ZMod 2) (K × K × K) := Ylin ⊓ LinearMap.ker ℓ
  have hker : Y₀ ≤ (LinearMap.range S).comap Φ := by
    intro z hz
    have hzY : z ∈ Y := hz.1
    have hzℓ : ℓ z = 0 := hz.2
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
      have hz' : commMap a c x z' = 0 := hz'
      by_cases hz'Y : z' ∈ Y
      · rw [hg_apply, ← hadj]
        exact hiso z hzY z' hz'Y
      · obtain ⟨hz₀X, hz₀Y⟩ := hz₀ ⟨z', hz', hz'Y⟩
        have hsum := hYi z' z₀ hz' hz₀X hz'Y hz₀Y
        have h1 : g (z' + z₀) = 0 := by rw [hg_apply, ← hadj]; exact hiso z hzY _ hsum
        have h2 : g z₀ = 0 := by
          have : ℓ z = g z₀ := by
            show Algebra.trace (ZMod 2) K (pair (Φ z)) = g z₀
            rw [hg_apply, hpair]
            rfl
          rw [← this, hzℓ]
        rw [map_add, h2, add_zero] at h1
        exact h1
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
  have hinjY : ∀ z ∈ Y, Φ z = 0 → z = 0 := by
    intro z hzY hz
    by_contra hz0
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
    rw [hr0, mul_zero, add_zero, map_mul, hφsq] at e1
    have hψu : ψ z.1 ≠ 0 := (map_ne_zero ψ).mpr hu0
    have h5 : ψ z.1 * (ψ β - β * ψ z.1) = 0 := by
      linear_combination e1 - β * ψ z.1 ^ 2 * (CharTwo.two_eq_zero : (2 : K) = 0)
    have h6 := (mul_eq_zero.mp h5).resolve_left hψu
    have hw : (β * z.1 ^ (2 ^ (a + 1) + 1)) ^ 2 ^ a = β * z.1 ^ (2 ^ (a + 1) + 1) := by
      have e3 : ψ β = β * ψ z.1 := by linear_combination h6
      have e4 : (z.1 ^ 2 ^ (a + 1)) ^ 2 ^ a = z.1 := pow_theta_pow_sigma hK z.1
      have e5 : z.1 ^ 2 ^ (a + 1) = ψ z.1 ^ 2 := by rw [← hφsq, hφ]
      rw [hψ] at e3
      rw [mul_pow, pow_succ, mul_pow, e4, e3, e5, hψ]
      ring
    have hw1 : β * z.1 ^ (2 ^ (a + 1) + 1) = 1 := by
      rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a a) hw with h0 | h1
      · exact absurd h0 (mul_ne_zero hβ (pow_ne_zero _ hu0))
      · exact h1
    have hQ : sqMap a c e z = z.1 ^ (2 ^ (a + 1) + 1) := by
      have h0 : (0 : K) ^ 2 ^ a = 0 := zero_pow (by positivity)
      simp only [sqMap, hr0, mul_zero, h0, add_zero]
    have h0 := hβH _ (AddSubgroup.subset_closure ⟨z, hzY, rfl⟩)
    rw [hQ, hw1] at h0
    have htr : Algebra.trace (ZMod 2) K 1 = 1 := by
      have := Algebra.trace_algebraMap (R := ZMod 2) (S := K) 1
      rw [map_one] at this
      rw [this]
      have hn : Module.finrank (ZMod 2) K = 2 * a + 1 := by
        have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
        rw [hK, ZMod.card] at h
        exact (Nat.pow_right_injective le_rfl h).symm
      rw [hn, nsmul_eq_mul, mul_one]
      push_cast
      rw [show (2 : ZMod 2) * a = 0 by rw [show (2 : ZMod 2) = 0 from rfl, zero_mul], zero_add]
    rw [htr] at h0
    exact one_ne_zero h0
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
  have h6 : Module.finrank (ZMod 2) Y₀ ≤ Module.finrank (ZMod 2) (LinearMap.range S) := by
    let f : Y₀ →ₗ[ZMod 2] LinearMap.range S :=
      (Φ.domRestrict Y₀).codRestrict (LinearMap.range S) fun z => hker z.2
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have h1 : Φ z = 0 := congrArg Subtype.val hz
      exact Subtype.ext (hinjY z z.2.1 h1)
    exact LinearMap.finrank_le_finrank_of_injective hf
  have h7 : Module.finrank (ZMod 2) (LinearMap.ker M) ≤ Module.finrank (ZMod 2) Ylin + 1 := by
    have hle : LinearMap.ker M ≤ Ylin ⊔ Submodule.span (ZMod 2) {z₀} := by
      intro w hw
      have hw' : commMap a c x w = 0 := hw
      by_cases hwY : w ∈ Y
      · exact Submodule.mem_sup_left hwY
      · obtain ⟨hz₀X, hz₀Y⟩ := hz₀ ⟨w, hw', hwY⟩
        have hsum := hYi w z₀ hw' hz₀X hwY hz₀Y
        have e : w = (w + z₀) + z₀ := by rw [add_assoc, add_self_eq_zero_prod, add_zero]
        rw [e]
        exact Submodule.add_mem_sup hsum (Submodule.mem_span_singleton_self z₀)
    calc Module.finrank (ZMod 2) (LinearMap.ker M)
        ≤ Module.finrank (ZMod 2) (Ylin ⊔ Submodule.span (ZMod 2) {z₀} :
          Submodule (ZMod 2) (K × K × K)) := Submodule.finrank_mono hle
      _ ≤ Module.finrank (ZMod 2) Ylin +
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({z₀} : Set (K × K × K))) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ Module.finrank (ZMod 2) Ylin + 1 := by
          have := finrank_span_singleton_le_one (K := ZMod 2) z₀
          omega
  have h8 : Module.finrank (ZMod 2) Ylin ≤ Module.finrank (ZMod 2) Y₀ + 1 := by
    by_cases hex : ∃ z₁ ∈ Ylin, ℓ z₁ ≠ 0
    · obtain ⟨z₁, hz₁, hz₁ℓ⟩ := hex
      have hone : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      have hle : Ylin ≤ Y₀ ⊔ Submodule.span (ZMod 2) {z₁} := by
        intro z hz
        by_cases hzℓ : ℓ z = 0
        · exact Submodule.mem_sup_left ⟨hz, hzℓ⟩
        · have hmem : z + z₁ ∈ Y₀ := ⟨Ylin.add_mem hz hz₁, by
            show ℓ (z + z₁) = 0
            rw [map_add, hone _ hzℓ, hone _ hz₁ℓ]
            decide⟩
          have e : z = (z + z₁) + z₁ := by rw [add_assoc, add_self_eq_zero_prod, add_zero]
          rw [e]
          exact Submodule.add_mem_sup hmem (Submodule.mem_span_singleton_self z₁)
      calc Module.finrank (ZMod 2) Ylin
          ≤ Module.finrank (ZMod 2) (Y₀ ⊔ Submodule.span (ZMod 2) {z₁} :
            Submodule (ZMod 2) (K × K × K)) := Submodule.finrank_mono hle
        _ ≤ Module.finrank (ZMod 2) Y₀ +
            Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({z₁} : Set (K × K × K))) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ Module.finrank (ZMod 2) Y₀ + 1 := by
            have := finrank_span_singleton_le_one (K := ZMod 2) z₁
            omega
    · push Not at hex
      have hle : Ylin ≤ Y₀ := fun z hz => ⟨hz, hex z hz⟩
      have := Submodule.finrank_mono hle
      omega
  omega

end CFSG.ComponentClassification.GMS78.VLike
