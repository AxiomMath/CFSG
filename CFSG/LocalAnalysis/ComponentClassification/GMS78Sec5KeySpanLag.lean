module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanU0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanLagTools

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

variable {a : ℕ} {c e : K}

theorem closure_eq_top_c_ne_zero_u_ne_zero (ha : 2 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup K} (hc : c ≠ 0) {x : K × K × K} (hu : x.1 ≠ 0) :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
  by_contra hne
  obtain ⟨β, hβ, hβH⟩ := exists_ne_zero_trace_mul_eq_zero_of_ne_top hne
  obtain ⟨u, hux⟩ : ∃ u, u = x.1 := ⟨_, rfl⟩
  obtain ⟨r, hrx⟩ : ∃ r, r = x.2.1 := ⟨_, rfl⟩
  obtain ⟨s, hsx⟩ : ∃ s, s = x.2.2 := ⟨_, rfl⟩
  rw [← hux] at hu
  let φ : K →+* K := iterateFrobenius K 2 (a + 1)
  let ψ : K →+* K := iterateFrobenius K 2 a
  have hφ : ∀ y, φ y = y ^ 2 ^ (a + 1) := fun y => iterateFrobenius_def (p := 2) (a + 1) y
  have hψ : ∀ y, ψ y = y ^ 2 ^ a := fun y => iterateFrobenius_def (p := 2) a y
  have hψφ : ∀ y, ψ (φ y) = y := fun y => by rw [hψ, hφ, pow_theta_pow_sigma hK]
  have hφψ : ∀ y, φ (ψ y) = y := fun y => by rw [hψ, hφ, pow_sigma_pow_theta hK]
  have hφφ : ∀ y, φ (φ y) = y ^ 2 := fun y => by rw [hφ, hφ, pow_theta_pow_theta hK]
  have hψψ : ∀ y, ψ (ψ y) = y ^ 2 ^ (2 * a) := fun y => by
    rw [hψ, hψ, ← pow_mul, ← pow_add, two_mul]
  have trφ : ∀ γ t, Algebra.trace (ZMod 2) K (γ * φ t) = Algebra.trace (ZMod 2) K (ψ γ * t) :=
    fun γ t => by rw [hφ, hψ]; exact trace_mul_pow_theta hK γ t
  have trψ : ∀ γ t, Algebra.trace (ZMod 2) K (γ * ψ t) = Algebra.trace (ZMod 2) K (φ γ * t) :=
    fun γ t => by rw [hφ, hψ]; exact trace_mul_pow_sigma hK γ t
  let M : K × K → K := fun w =>
    u * φ w.1 + φ u * w.1 + c * (ψ (u * w.2) + ψ (w.1 * r)) + s * w.2
  have hM : ∀ w : K × K, commMap a c x (w.1, w.2, 0) = M w := fun w => by
    simp only [commMap, M, hφ, hψ, ← hux, ← hrx, ← hsx]
    ring
  let Madd : K × K →+ K :=
    { toFun := M
      map_zero' := by simp [M]
      map_add' := fun w w' => by
        simp only [M, Prod.fst_add, Prod.snd_add, map_add, mul_add, add_mul]
        ring }
  let Mlin : K × K →ₗ[ZMod 2] K := Madd.toZModLinearMap 2
  have hMlin : ∀ w, Mlin w = M w := fun w => rfl
  obtain ⟨C, hCdef⟩ : ∃ C, C = φ (β * c) := ⟨_, rfl⟩
  have hC : C ≠ 0 := by rw [hCdef]; exact (map_ne_zero φ).mpr (mul_ne_zero hβ hc)
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = s / C := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = φ c * u / C := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = (ψ u + ψ β * ψ A₀) / C := ⟨_, rfl⟩
  obtain ⟨R0, hR0⟩ : ∃ R0, R0 = (φ u + ψ β * ψ A₁) / C := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = (φ c * r + β * φ A₀) / C := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2, R2 = β * φ A₁ / C := ⟨_, rfl⟩
  let Zf : K → K × K := fun δ =>
    (A₀ * δ + A₁ * φ δ, Rm * ψ δ + R0 * δ + R1 * φ δ + R2 * φ (φ δ))
  let Zadd : K →+ K × K :=
    { toFun := Zf
      map_zero' := by simp [Zf]
      map_add' := fun δ δ' => by
        simp only [Zf, map_add, Prod.mk_add_mk]
        congr 1 <;> ring }
  let Zlin : K →ₗ[ZMod 2] K × K := Zadd.toZModLinearMap 2
  have hZlin : ∀ δ, Zlin δ = Zf δ := fun δ => rfl
  have hker : LinearMap.ker Mlin ≤ LinearMap.range Zlin := by
    intro w hw
    have hw0 : M w = 0 := hw
    have hmem : ∀ w' : K × K, M w' = 0 → ((w'.1, w'.2, 0) : K × K × K) ∈ perp a c Λ x :=
      fun w' hw' => ⟨Λ.zero_mem, by rw [hM]; exact hw'⟩
    obtain ⟨p, hp⟩ : ∃ p, p = ψ (β * w.1) + β * φ w.1 + C * w.2 := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = C * w.1 := ⟨_, rfl⟩
    have hadjB : ∀ w' : K × K, Algebra.trace (ZMod 2) K
        (β * commMap a c (w.1, w.2, 0) (w'.1, w'.2, 0)) =
          Algebra.trace (ZMod 2) K (p * w'.1 + t * w'.2) := fun w' => by
      have e1 : β * commMap a c (w.1, w.2, 0) (w'.1, w'.2, 0) = β * w.1 * φ w'.1 +
          β * φ w.1 * w'.1 + β * c * ψ w.1 * ψ w'.2 + β * c * ψ w.2 * ψ w'.1 := by
        simp only [commMap, hφ, hψ, mul_pow]
        ring
      rw [e1, map_add, map_add, map_add, trφ, trψ, trψ, hp, ht, hCdef]
      rw [← map_add, ← map_add, ← map_add]
      congr 1
      simp only [map_mul, hφψ]
      ring
    let g : K × K →ₗ[ZMod 2] ZMod 2 := (Algebra.trace (ZMod 2) K).comp
      ((LinearMap.mulLeft (ZMod 2) p).comp (LinearMap.fst (ZMod 2) K K) +
        (LinearMap.mulLeft (ZMod 2) t).comp (LinearMap.snd (ZMod 2) K K))
    have hg_apply : ∀ w', g w' = Algebra.trace (ZMod 2) K (p * w'.1 + t * w'.2) := fun w' => rfl
    have hg : ∀ w', Mlin w' = 0 → g w' = 0 := fun w' hw' => by
      rw [hg_apply, ← hadjB]
      exact hβH _ (commMap_mem_closure (hmem w hw0) (hmem w' hw'))
    obtain ⟨δ, hδ⟩ := exists_trace_mul_eq_of_ker_le Mlin g hg
    have hadjM : ∀ w' : K × K, Algebra.trace (ZMod 2) K (δ * M w') =
        Algebra.trace (ZMod 2) K ((ψ (δ * u) + φ u * δ + φ c * r * φ δ) * w'.1 +
          (φ c * u * φ δ + s * δ) * w'.2) := fun w' => by
      have e1 : δ * M w' = δ * u * φ w'.1 + δ * φ u * w'.1 + δ * c * ψ u * ψ w'.2 +
          δ * c * ψ r * ψ w'.1 + δ * s * w'.2 := by
        simp only [M, map_mul]
        ring
      rw [e1, map_add, map_add, map_add, map_add, trφ, trψ, trψ]
      rw [← map_add, ← map_add, ← map_add, ← map_add]
      congr 1
      simp only [map_mul, hφψ]
      ring
    have hcmp : ∀ w' : K × K, Algebra.trace (ZMod 2) K (p * w'.1 + t * w'.2) =
        Algebra.trace (ZMod 2) K ((ψ (δ * u) + φ u * δ + φ c * r * φ δ) * w'.1 +
          (φ c * u * φ δ + s * δ) * w'.2) := fun w' => by
      rw [← hg_apply, hδ, hMlin, hadjM]
    have hpδ : p = ψ (δ * u) + φ u * δ + φ c * r * φ δ := by
      refine sub_eq_zero.mp (eq_zero_of_forall_trace_mul_eq_zero fun y => ?_)
      have := hcmp (y, 0)
      simp only [mul_zero, add_zero] at this
      rw [sub_mul, map_sub, this, sub_self]
    have htδ : t = φ c * u * φ δ + s * δ := by
      refine sub_eq_zero.mp (eq_zero_of_forall_trace_mul_eq_zero fun y => ?_)
      have := hcmp (0, y)
      simp only [mul_zero, zero_add] at this
      rw [sub_mul, map_sub, this, sub_self]
    obtain ⟨h1, h2⟩ := lag_inv φ ψ hψφ (u := u) (r := r) (s := s) (c := c) (β := β)
      (δ := δ) (w₁ := w.1) (w₂ := w.2) hC hA₀ hA₁ hRm hR0 hR1 hR2 (by rw [← ht, htδ])
      (by rw [← hp, hpδ])
    exact ⟨δ, by rw [hZlin]; exact Prod.ext h1.symm h2.symm⟩
  obtain ⟨hrange, hinj⟩ := range_eq_ker_of_ker_le_range Mlin Zlin hker
  have hvan : ∀ δ, M (Zf δ) = 0 := fun δ => by
    have : Zlin δ ∈ LinearMap.ker Mlin := hrange ▸ LinearMap.mem_range_self Zlin δ
    exact this
  obtain ⟨Pmm, hPmm⟩ : ∃ P, P = c * ψ u * ψ Rm := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P, P = c * ψ u * ψ R0 + c * ψ r * ψ A₀ + s * Rm := ⟨_, rfl⟩
  obtain ⟨P0, hP0⟩ : ∃ P, P = φ u * A₀ + c * ψ u * ψ R1 + c * ψ r * ψ A₁ + s * R0 := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, P = u * φ A₀ + φ u * A₁ + c * ψ u * ψ R2 + s * R1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = u * φ A₁ + s * R2 := ⟨_, rfl⟩
  have hpoly : ∀ δ : K, Pmm * δ ^ 2 ^ (2 * a) + Pm * δ ^ 2 ^ a + P0 * δ +
      P1 * δ ^ 2 ^ (a + 1) + P2 * δ ^ 2 = 0 := fun δ => by
    have h := lag_expand φ ψ hψφ (r := r) δ hPmm hPm hP0 hP1 hP2
    rw [← hψψ δ, ← hψ δ, ← hφ δ, ← hφφ δ, ← h]
    exact hvan δ
  obtain ⟨hP1z, hP2z⟩ := coeffs_eq_zero_of_vanish_five ha hK hpoly
  obtain ⟨hN, hL⟩ := lag_final φ ψ hψφ (r := r) (s := s) hu hc hβ hCdef hA₁ hR1 hR2 hP1 hP2
    hP1z hP2z
  obtain ⟨h1, h2⟩ := lag_inv φ ψ hψφ (u := u) (r := r) (s := s) (c := c) (β := β) (δ := β)
    (w₁ := 0) (w₂ := 0) hC hA₀ hA₁ hRm hR0 hR1 hR2 (by rw [mul_zero, hN])
    (by simp only [mul_zero, map_zero, add_zero]; exact hL.symm)
  have hZβ : Zlin β = 0 := by rw [hZlin]; exact Prod.ext h1.symm h2.symm
  exact hβ (LinearMap.ker_eq_bot.mp hinj (by rw [hZβ, map_zero]))

end CFSG.ComponentClassification.GMS78.VLike
