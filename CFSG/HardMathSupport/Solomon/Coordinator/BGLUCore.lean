module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUCoreConj
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUThetaGen
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUCoreRat
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUIso
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLULevelMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {ι ρ : K ≃+* K}

theorem su3_core
    (hι : IsUnitaryInvolution ι) (h3 : ∃ s : K, s ≠ 0 ∧ ι s * s ≠ 1)
    (C : UCtx ι ρ) (three : (3 : K) ≠ 0)
    (hu : ∃ u : K, ρ u = u ∧ ι u * u = -1) (hω : ∃ ω : K, ρ ω = ω ∧ ι ω * ω = 1 ∧ ω ≠ 1)
    (kE : Subfield (Efix ι)) (hkE : ∀ e : Efix ι, e ∈ kE ↔ ρ (e : K) = e)
    (hcard : Nat.card (Efix ι) = Nat.card kE ^ 3) (hk2 : Nat.card kE ≠ 2)
    (hspan : ∀ z : K, z ∈ AddSubgroup.closure
      {z | ∃ t : K, ι t = t ∧ t ≠ 0 ∧ ∃ μ : K, ρ μ = μ ∧ z = t * μ})
    (h : GL (Fin 3) K)
    (hiso : ∀ x y, herm ι ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
      ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = herm ι x y)
    (hnot : ¬ ∃ c : K, c ≠ 0 ∧ ∀ i j, ρ (c * (h : Matrix (Fin 3) (Fin 3) K) i j) =
      c * (h : Matrix (Fin 3) (Fin 3) K) i j)
    (H : Subgroup (SUid ι 3))
    (hrat : ∀ g : SUid ι 3, RatM ρ ((g.1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ H)
    (hconj : ∀ g g' : SUid ι 3, RatM ρ ((g.1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      (g'.1 : GL (Fin 3) K) = h * g.1 * h⁻¹ → g' ∈ H) : H = ⊤ := by
  obtain ⟨u, hρu, hu⟩ := hu
  obtain ⟨ω, hρω, hω, hω1⟩ := hω
  obtain ⟨B⟩ := isoBasis_exists C.ιinv hρu hρω hu hω hω1
  set M : Matrix (Fin 3) (Fin 3) K := (h : Matrix (Fin 3) (Fin 3) K) with hM
  obtain ⟨a, b₀, ha, hb₀, haI, hb₀I, hβ⟩ := exists_irrational_pair C M B (exists_mulVec_eq h) hnot
  set β := Bf ι M a b₀ with hβdef
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hβ
    rw [h0]
    simp
  have hb'I : herm ι (M *ᵥ b₀) (M *ᵥ b₀) = 0 := by rw [hM, hiso]; exact hb₀I
  set b : Fin 3 → K := β⁻¹ • (M *ᵥ b₀) with hbdef
  have hbI : herm ι b b = 0 := by
    rw [hbdef, herm_smul_left, herm_smul_right, hb'I]; ring
  have hab : herm ι a b = 1 := by
    rw [hbdef, herm_smul_right]
    have : herm ι a (M *ᵥ b₀) = β := rfl
    rw [this, inv_mul_cancel₀ hβ0]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hab
  obtain ⟨w, hwI, haw, hbw⟩ := exists_norm_one_perp_pair hι (le_refl 3) haI hbI hab
  have hw0 : herm ι w w ≠ 0 := by rw [hwI]; exact one_ne_zero
  obtain ⟨c₀, hc0, hρc, hιc⟩ := C.c₀
  let P : HypPair ι :=
    ⟨a, b, c₀, c₀⁻¹, C.ιinv, haI, hbI, hab, by rw [hιc]; ring, mul_inv_cancel₀ hc0⟩
  have hNβ : ι (ι β * β) = ι β * β := by rw [map_mul, C.ιinv, mul_comm]
  let κ : Efix ι := ⟨c₀ ^ 2 * (ι β * β), by
    show ι (c₀ ^ 2 * (ι β * β)) = c₀ ^ 2 * (ι β * β)
    rw [map_mul, map_pow, hιc, hNβ]; ring⟩
  have hκ : κ ∉ kE := by
    intro hk
    rw [hkE] at hk
    apply hβ
    have : ρ (c₀ ^ 2 * (ι β * β)) = c₀ ^ 2 * (ι β * β) := hk
    rw [map_mul, map_pow, hρc] at this
    exact mul_left_cancel₀ (pow_ne_zero 2 hc0) this
  have hx : ∀ s ∈ kE, ∀ (hc : P.τ * ((s : Efix ι) : K) + ι (P.τ * ((s : Efix ι) : K)) = 0),
      tv P.inv P.ha hc ∈ H := by
    intro s hs hc
    apply hrat
    exact tv_ratM C ha (by show ρ (c₀ * (s : K)) = c₀ * (s : K); rw [map_mul, hρc, (hkE s).mp hs])
      haI hc
  have hy : ∀ s ∈ kE, ∀ (hc : P.τ' * (((κ * s : Efix ι)) : K) +
      ι (P.τ' * (((κ * s : Efix ι)) : K)) = 0), tv P.inv P.hb hc ∈ H := by
    intro s hs hc
    have hsρ := (hkE s).mp hs
    have hιs : ι (s : K) = s := s.2
    have hc₀s : c₀ * (s : K) + ι (c₀ * (s : K)) = 0 := by
      rw [map_mul, hιc, hιs]; ring
    refine hconj (tv C.ιinv hb₀I hc₀s) _
      (tv_ratM C hb₀ (by rw [map_mul, hρc, hsρ]) hb₀I hc₀s) ?_
    apply Units.ext
    refine tv_conj_eq h hiso C.ιinv hb₀I hc₀s (l := β⁻¹) (c' := c₀⁻¹ * (((κ * s : Efix ι)) : K))
      hbdef hbI hc ?_
    have : (((κ * s : Efix ι)) : K) = c₀ ^ 2 * (ι β * β) * (s : K) := rfl
    have hιβ : ι β ≠ 0 := by
      intro h0
      apply hβ0
      rw [← C.ιinv β, h0, map_zero]
    rw [this, map_inv₀]
    field_simp
  have hΘ := fun Mx => P.thetaSL_mem_all H kE hcard hk2 hκ hx hy Mx
  have hXa : ∀ (c : K) (hc : c + ι c = 0), tv C.ιinv haI hc ∈ H :=
    fun c hc => HypPair.tv_a_mem hΘ hc
  have hXb : ∀ (c : K) (hc : c + ι c = 0), tv C.ιinv hbI hc ∈ H :=
    fun c hc => HypPair.tv_b_mem hΘ hc
  have h𝒯 : ∀ t ∈ {t : K | ι t = t ∧ t ≠ 0},
      t ≠ 0 ∧ ∃ g ∈ H, g • a = t • a ∧ g • w = w :=
    fun t ht => ⟨ht.2, HypPair.torus_mem hΘ ht.1 ht.2 haw hbw⟩
  obtain ⟨y₀, hy₀r, hy₀p, hy₀n⟩ := exists_rational_perp C ha ha0 haI
  have hy₀w : herm ι w y₀ ≠ 0 := by
    intro h0
    obtain ⟨α, γ, hdec, hγ⟩ := exists_decomp_of_perp C.ιinv haI hbI hab haw hbw hw0 hy₀p
    have : γ = 0 := hγ.mpr h0
    exact hy₀n ⟨α, by rw [hdec, this, zero_smul, add_zero]⟩
  have hR : ∀ μ ∈ {μ : K | ρ μ = μ}, μ • y₀ ∈ EichSet ι C.ιinv H haI := by
    intro μ hμ
    have hrv : Ratv ρ (μ • y₀) := ratv_smul hμ hy₀r
    have hey : herm ι a (μ • y₀) = 0 := by rw [herm_smul_right, hy₀p, mul_zero]
    have hd : ρ (-herm ι (μ • y₀) (μ • y₀)) = -herm ι (μ • y₀) (μ • y₀) := by
      rw [map_neg, UCtx.ρ_herm C hrv hrv]
    have hd' : ι (-herm ι (μ • y₀) (μ • y₀)) = -herm ι (μ • y₀) (μ • y₀) := by
      rw [map_neg, herm_self_fixed ι C.ιinv]
    obtain ⟨c, hcρ, hc⟩ := exists_rational_trace C hι three hd hd'
    refine ⟨hey, c, hc, ?_⟩
    apply hrat
    exact eichler_ratM C ha hrv hcρ haI hey hc
  have hspan' : ∀ z : K, z ∈ AddSubgroup.closure {z | ∃ t ∈ {t : K | ι t = t ∧ t ≠ 0},
      ∃ μ ∈ {μ : K | ρ μ = μ}, z = ι t * μ} := by
    intro z
    refine AddSubgroup.closure_mono ?_ (hspan z)
    rintro _ ⟨t, ht, ht0, μ, hμ, rfl⟩
    exact ⟨t, ⟨ht, ht0⟩, μ, hμ, by rw [ht]⟩
  exact level_eq_top hι h3 H haI hbI hab haw hbw hw0 hXa hXb _ _ h𝒯 hy₀p hy₀w hR hspan'

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
