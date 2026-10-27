module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59URel

import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59R6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Phi

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

theorem fz59u_fixed_point [Finite G] {R : Subgroup G} {u₀ rho : G} (hrho : rho ^ 3 = 1)
    (hR : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R) (hu : u₀⁻¹ * (rho * u₀ * rho⁻¹) ∈ R)
    (h3 : ¬ 3 ∣ Nat.card R) : ∃ r ∈ R, rho * (u₀ * r) * rho⁻¹ = u₀ * r := by
  classical
  have hR' : ∀ r, rho * r * rho⁻¹ ∈ R ↔ r ∈ R := by
    intro r
    refine ⟨fun h => ?_, hR r⟩
    have h2 := hR _ (hR _ h)
    have e : rho * (rho * (rho * r * rho⁻¹) * rho⁻¹) * rho⁻¹ = rho ^ 3 * r * (rho ^ 3)⁻¹ := by
      rw [pow_three]; group
    rw [e, hrho] at h2
    simpa using h2
  let P : G → Prop := fun x => u₀⁻¹ * x ∈ R
  have hP : ∀ x, P ((MulAut.conj rho).toEquiv x) ↔ P x := by
    intro x
    simp only [P, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    have e : u₀⁻¹ * (rho * x * rho⁻¹) =
        (u₀⁻¹ * (rho * u₀ * rho⁻¹)) * (rho * (u₀⁻¹ * x) * rho⁻¹) := by group
    rw [e]
    constructor
    · intro h
      have := R.mul_mem (R.inv_mem hu) h
      rw [inv_mul_cancel_left] at this
      exact (hR' _).1 this
    · intro h
      exact R.mul_mem hu ((hR' _).2 h)
  let σ : Equiv.Perm {x // P x} := Equiv.Perm.subtypePerm (MulAut.conj rho).toEquiv hP
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    show rho * (rho * (rho * x.1 * rho⁻¹) * rho⁻¹) * rho⁻¹ = x.1
    have e : rho * (rho * (rho * x.1 * rho⁻¹) * rho⁻¹) * rho⁻¹ =
        rho ^ 3 * x.1 * (rho ^ 3)⁻¹ := by
      rw [pow_three]; group
    rw [e, hrho]; group
  haveI : Fintype {x // P x} := Fintype.ofFinite _
  have hcard : Fintype.card {x // P x} = Nat.card R := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨u₀⁻¹ * x.1, x.2⟩
        invFun := fun r => ⟨u₀ * r.1, by simp [P]⟩
        left_inv := fun x => by simp
        right_inv := fun r => by simp }
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hx⟩, hfix⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rw [hcard]; exact h3) hσ
  refine ⟨u₀⁻¹ * x, hx, ?_⟩
  rw [mul_inv_cancel_left]
  have := congrArg Subtype.val hfix
  simpa [σ, Equiv.Perm.subtypePerm_apply] using this

theorem fz59u_rho_mem [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) :
    rho ∈ normalizer ((fz59R b : Subgroup G) : Set G) := by
  rw [← hF.hR, mem_normalizer_iff]
  intro r
  refine ⟨hB.N2_nrm_R rho hB.rho_N2 r, fun h => ?_⟩
  have := hB.N2_nrm_R rho⁻¹ (inv_mem hB.rho_N2) _ h
  simpa [mul_assoc] using this

theorem fz59u_lam_mem [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) :
    lam ∈ normalizer ((fz59R b : Subgroup G) : Set G) := by
  rw [← hF.hR, mem_normalizer_iff]
  intro r
  refine ⟨hB.str.nrm_R lam hB.str.lam_T r, fun h => ?_⟩
  have := hB.str.nrm_R lam⁻¹ (inv_mem hB.str.lam_T) _ h
  simpa [mul_assoc] using this

theorem fz59u_phi_rho {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hρ : rho ∈ normalizer ((fz59R b : Subgroup G) : Set G)) :
    Φ ⟨rho, hρ⟩ = fz59RowRot := by
  refine fz59_phi_unique h.rows hΦ _ _ fun c => ⟨1, one_mem _, ?_⟩
  rw [mul_one]
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact h.rho_b i 0
  · exact h.rho_b i 1
  · show rho * (b i 0 * b i 1) * rho⁻¹ = b (i + 1) 0 * b (i + 1) 1
    rw [← h.rho_b i 0, ← h.rho_b i 1]
    group

theorem fz59u_phi_lam {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hlN : lam ∈ normalizer ((fz59R b : Subgroup G) : Set G)) :
    Φ ⟨lam, hlN⟩ = fz59RowSwap := by
  have key : ∀ i k, lam * b i k * lam⁻¹ = b (Equiv.swap (0 : Fin 3) 1 i) k := by
    intro i k
    rcases fz59u_fin3 i with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact h.lam_01 k
    · rw [Equiv.swap_apply_right]
      exact fz59u_lam_1 h k
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact h.lam_2 k
  refine fz59_phi_unique h.rows hΦ _ _ fun c => ⟨1, one_mem _, ?_⟩
  rw [mul_one]
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact key i 0
  · exact key i 1
  · show lam * (b i 0 * b i 1) * lam⁻¹ = b (Equiv.swap (0 : Fin 3) 1 i) 0 *
      b (Equiv.swap (0 : Fin 3) 1 i) 1
    rw [← key i 0, ← key i 1]
    group

theorem fz59u_g0 (i : Fin 3) : fz59ColPerm (Equiv.swap 0 2) (i, 0) = (i, 2) := by
  simp [fz59ColPerm]

theorem fz59u_fix_conj {rho x y : G} (hx : rho * x = x * rho) (hy : rho * y * rho⁻¹ = y) :
    rho * (x * y * x⁻¹) * rho⁻¹ = x * y * x⁻¹ := by
  calc rho * (x * y * x⁻¹) * rho⁻¹ = (rho * x) * y * (rho * x)⁻¹ := by group
    _ = x * (rho * y * rho⁻¹) * x⁻¹ := by rw [hx]; group
    _ = x * y * x⁻¹ := by rw [hy]

theorem fz59u_t_ne_one {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ : G} {T₂ : Subgroup G} [Finite G]
    (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) : t ≠ 1 := fun h =>
  hB.str.t_notin_E (h ▸ one_mem _)

theorem fz59u_s_ne_one {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G} [Finite G]
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) : s ≠ 1 := by
  intro hs
  rcases hF.s_cases with h | h
  · exact hB.str.tau_notin_Q (by rw [← h, hs]; exact one_mem _)
  · have htau : tau = t⁻¹ := eq_inv_of_mul_eq_one_right (h.symm.trans hs)
    exact hB.str.tau_notin_Q (by rw [htau]; exact inv_mem (hB.str.WQ hB.str.t_mem))

theorem fz59u_invol [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b)
    (hg : fz59ColPerm (Equiv.swap 0 2) ∈ Φ.range) :
    ∃ u : normalizer ((fz59R b : Subgroup G) : Set G), Φ u = fz59ColPerm (Equiv.swap 0 2) ∧
      (u : G) ^ 2 = 1 ∧ (u : G) * rho = rho * u ∧ (u : G) * t * (u : G)⁻¹ = t * s := by
  have hb := hF.grid.rows
  have hρ := fz59u_rho_mem hB hF
  have htR := fz59u_t_mem hF.grid
  have hs1 := fz59u_s_ne_one hB hF
  have hρt : rho * t = t * rho := mul_inv_eq_iff_eq_mul.mp hB.str.rho_t
  obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp hg
  have h1 : (u₀ : G)⁻¹ * (rho * u₀ * rho⁻¹) ∈ fz59R b := by
    have h := (hker (u₀⁻¹ * ⟨rho, hρ⟩ * u₀ * (⟨rho, hρ⟩ : normalizer _)⁻¹)).1 (by
      simp only [map_mul, map_inv, hu₀, fz59u_phi_rho hF.grid hΦ hρ]
      decide)
    simpa [mul_assoc] using h
  have hρR : ∀ r ∈ fz59R b, rho * r * rho⁻¹ ∈ fz59R b := fun r hr =>
    (mem_normalizer_iff.mp hρ r).1 hr
  obtain ⟨r, hr, hfix⟩ := fz59u_fixed_point hF.grid.rho_ord hρR h1
    (by rw [fz59_card_R hb]; decide)
  set u₁ : normalizer ((fz59R b : Subgroup G) : Set G) := u₀ * ⟨r, le_normalizer hr⟩ with hu₁
  have hu₁g : Φ u₁ = fz59ColPerm (Equiv.swap 0 2) := by
    rw [hu₁, map_mul, hu₀, (hker _).2 hr, mul_one]
  have hu₁ρ : rho * (u₁ : G) = u₁ * rho := mul_inv_eq_iff_eq_mul.mp hfix
  have hu₁N : ∀ x ∈ fz59R b, (u₁ : G) * x * (u₁ : G)⁻¹ ∈ fz59R b := fun x hx =>
    (mem_normalizer_iff.mp u₁.2 x).1 hx
  have hut : (u₁ : G) * t * (u₁ : G)⁻¹ = t * s := by
    obtain ⟨ω', z, hz, he, himg⟩ := fz59_phi_prod hb hΦ u₁ ![0, 0, 0]
    have hω' : ω' = ![2, 2, 2] := by
      rw [hu₁g, show (fz59Tr ![0, 0, 0]).image (fz59ColPerm (Equiv.swap 0 2)) =
        fz59Tr ![2, 2, 2] by decide] at himg
      exact (fz59u_tr_inj himg).symm
    subst hω'
    have ht0 : fz59Prod b ![0, 0, 0] = t := hF.grid.t_eq.symm
    have hs0 : fz59Prod b ![1, 1, 1] = s := hF.grid.s_eq.symm
    rw [ht0] at he
    have key : ∀ ω : Fin 3 → Fin 3, fz59Prod b ω = (u₁ : G) * t * (u₁ : G)⁻¹ →
        ω = ![2, 2, 2] := fun ω hω =>
      fz59_prod_inj hb (one_mem _) hz (by rw [mul_one, hω, he])
    have hfix' : rho * ((u₁ : G) * t * (u₁ : G)⁻¹) * rho⁻¹ = (u₁ : G) * t * (u₁ : G)⁻¹ :=
      fz59u_fix_conj hu₁ρ hB.str.rho_t
    rcases fz59_cent_rho hF.grid _ (hu₁N t htR) hfix' with h | h | h | h
    · exact absurd (conj_eq_one_iff.mp h) (fz59u_t_ne_one hB)
    · exact absurd (key _ (ht0.trans h.symm)) (by decide)
    · exact absurd (key _ (hs0.trans h.symm)) (by decide)
    · exact h
  have hsq : (u₁ : G) ^ 2 ∈ fz59R b := by
    have h := (hker (u₁ ^ 2)).1 (by rw [map_pow, hu₁g]; decide)
    simpa using h
  have hsqfix : rho * (u₁ : G) ^ 2 * rho⁻¹ = (u₁ : G) ^ 2 := by
    rw [sq, mul_inv_eq_iff_eq_mul, ← mul_assoc, hu₁ρ, mul_assoc, hu₁ρ, mul_assoc]
  rcases fz59_cent_rho hF.grid _ hsq hsqfix with h | h | h | h
  · exact ⟨u₁, hu₁g, h, hu₁ρ.symm, hut⟩
  · exfalso
    have e : (u₁ : G) * t * (u₁ : G)⁻¹ = t := by rw [← h, sq]; group
    rw [hut] at e
    exact hs1 (mul_left_cancel (e.trans (mul_one t).symm))
  · refine ⟨u₁ * ⟨t, le_normalizer htR⟩, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, hu₁g, (hker _).2 htR, mul_one]
    · show ((u₁ : G) * t) ^ 2 = 1
      have hss : s * s = 1 := by rw [← sq]; exact fz59u_s_sq hF.grid
      have htt : t * t = 1 := by rw [← sq]; exact hB.str.t_sq
      calc ((u₁ : G) * t) ^ 2 = ((u₁ : G) * t * (u₁ : G)⁻¹) * ((u₁ : G) * (u₁ : G)) * t := by
            rw [sq]; group
        _ = t * (s * s) * t := by rw [hut, ← sq, h]; group
        _ = 1 := by rw [hss, mul_one, htt]
    · show (u₁ : G) * t * rho = rho * ((u₁ : G) * t)
      rw [mul_assoc, ← hρt, ← mul_assoc, ← hu₁ρ, mul_assoc]
    · show (u₁ : G) * t * t * ((u₁ : G) * t)⁻¹ = t * s
      rw [← hut]
      group
  · exfalso
    have e : (u₁ : G) * (t * s) * (u₁ : G)⁻¹ = t * s := by rw [← h, sq]; group
    have e2 : (u₁ : G) * (t * s) * (u₁ : G)⁻¹ =
        ((u₁ : G) * t * (u₁ : G)⁻¹) * ((u₁ : G) * s * (u₁ : G)⁻¹) := by group
    rw [e2, hut] at e
    exact hs1 (conj_eq_one_iff.mp (mul_left_cancel (e.trans (mul_one _).symm)))

theorem fz59u_act {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (hG : Fz59Grid t s lam rho b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (u : normalizer ((fz59R b : Subgroup G) : Set G))
    (hu : Φ u = fz59ColPerm (Equiv.swap 0 2)) (hu2 : (u : G) ^ 2 = 1)
    (hur : (u : G) * rho = rho * u) :
    (∀ i, (u : G) * b i 1 * (u : G)⁻¹ = (b i 1)⁻¹) ∧
      (∀ z ∈ fz59Z b, (u : G) * z * (u : G)⁻¹ = z) ∧
      ∃ δ : Fin 3 → G, (∀ i, δ i ∈ fz59Z b) ∧
        (∀ i, (u : G) * b i 0 * (u : G)⁻¹ = b i 0 * b i 1 * δ i) ∧
        ∀ i, δ (i + 1) = rho * δ i * rho⁻¹ := by
  have hb := hG.rows
  set U : G := (u : G) with hU
  have hact0 : ∀ i, ∃ z ∈ fz59Z b, U * b i 0 * U⁻¹ = b i 0 * b i 1 * z := by
    intro i
    obtain ⟨z, hz, he⟩ := hΦ.1 u (i, 0)
    rw [hu, fz59u_g0] at he
    exact ⟨z, hz, he⟩
  have hact1 : ∀ i, U * b i 1 * U⁻¹ ∈ fz59R b := fun i =>
    (mem_normalizer_iff.mp u.2 _).1 (fz59u_mem_R b i 1)
  have hZfix : ∀ i, U * b i 0 ^ 2 * U⁻¹ = b i 0 ^ 2 := by
    intro i
    obtain ⟨z, hz, he⟩ := hact0 i
    rw [← conj_pow, he,
      fz59u_sq_mul_Z hb (mul_mem (fz59u_mem_R b i 0) (fz59u_mem_R b i 1)) hz,
      fz59u_sq_mul (hb.quat i)]
  have hZc : ∀ w ∈ fz59Z b, U * w * U⁻¹ = w := by
    intro w hw
    rcases (fz59_mem_Z hb w).1 hw with rfl | rfl | rfl | rfl
    · group
    all_goals exact hZfix _
  refine ⟨fun i => ?_, hZc, fun i => (b i 0 * b i 1)⁻¹ * (U * b i 0 * U⁻¹), fun i => ?_,
    fun i => by group, fun i => ?_⟩
  · obtain ⟨z, hz, he⟩ := hact0 i
    set y := U * b i 1 * U⁻¹ with hy
    have hc : Commute z y := fz59_Z_central hb z hz y (hact1 i)
    have hUU : U * U = 1 := by rw [← sq]; exact hu2
    have h1 : b i 0 = U * (U * b i 0 * U⁻¹) * U⁻¹ := by
      calc b i 0 = (U * U) * b i 0 * (U * U)⁻¹ := by rw [hUU]; group
        _ = U * (U * b i 0 * U⁻¹) * U⁻¹ := by group
    have h2 : U * (U * b i 0 * U⁻¹) * U⁻¹ = b i 0 * b i 1 * z * y * z := by
      calc U * (U * b i 0 * U⁻¹) * U⁻¹ = U * (b i 0 * b i 1 * z) * U⁻¹ := by rw [he]
        _ = (U * b i 0 * U⁻¹) * y * (U * z * U⁻¹) := by rw [hy]; group
        _ = b i 0 * b i 1 * z * y * z := by rw [he, hZc z hz]
    have hzz : z * z = 1 := by rw [← sq]; exact fz59u_Z_sq hb hz
    have h3 : b i 0 * b i 1 * z * y * z = b i 0 * (b i 1 * y) * (z * z) := by
      calc b i 0 * b i 1 * z * y * z = b i 0 * b i 1 * (z * y) * z := by group
        _ = b i 0 * b i 1 * (y * z) * z := by rw [hc.eq]
        _ = b i 0 * (b i 1 * y) * (z * z) := by group
    have h4 := h1.trans (h2.trans h3)
    rw [hzz, mul_one] at h4
    exact eq_inv_of_mul_eq_one_right (mul_left_cancel (h4.symm.trans (mul_one _).symm))
  · obtain ⟨z, hz, he⟩ := hact0 i
    show (b i 0 * b i 1)⁻¹ * (U * b i 0 * U⁻¹) ∈ fz59Z b
    rw [he, inv_mul_cancel_left]
    exact hz
  · show (b (i + 1) 0 * b (i + 1) 1)⁻¹ * (U * b (i + 1) 0 * U⁻¹) =
      rho * ((b i 0 * b i 1)⁻¹ * (U * b i 0 * U⁻¹)) * rho⁻¹
    rw [← hG.rho_b i 0, ← hG.rho_b i 1]
    calc (rho * b i 0 * rho⁻¹ * (rho * b i 1 * rho⁻¹))⁻¹ * (U * (rho * b i 0 * rho⁻¹) * U⁻¹) =
        (rho * b i 0 * rho⁻¹ * (rho * b i 1 * rho⁻¹))⁻¹ *
          ((U * rho) * b i 0 * (U * rho)⁻¹) := by group
      _ = (rho * b i 0 * rho⁻¹ * (rho * b i 1 * rho⁻¹))⁻¹ *
          ((rho * U) * b i 0 * (rho * U)⁻¹) := by rw [hur]
      _ = rho * ((b i 0 * b i 1)⁻¹ * (U * b i 0 * U⁻¹)) * rho⁻¹ := by group

theorem fz59u_u_s {t s lam rho u : G} {b : Fin 3 → Fin 2 → G} (hG : Fz59Grid t s lam rho b)
    (hb1 : ∀ i, u * b i 1 * u⁻¹ = (b i 1)⁻¹) : u * s * u⁻¹ = s := by
  calc u * s * u⁻¹ = (u * b 0 1 * u⁻¹) * (u * b 1 1 * u⁻¹) * (u * b 2 1 * u⁻¹) := by
        rw [hG.s_eq]; group
    _ = (b 2 1 * (b 1 1 * b 0 1))⁻¹ := by rw [hb1, hb1, hb1]; group
    _ = s⁻¹ := by rw [fz59u_rev hG.rows, ← hG.s_eq]
    _ = s := fz59u_inv_eq (fz59u_s_sq hG)

theorem fz59u_comm_cases [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b)
    (u : normalizer ((fz59R b : Subgroup G) : Set G)) (hu : Φ u = fz59ColPerm (Equiv.swap 0 2))
    (hu2 : (u : G) ^ 2 = 1) (hur : (u : G) * rho = rho * u)
    (hut : (u : G) * t * (u : G)⁻¹ = t * s) (hus : (u : G) * s * (u : G)⁻¹ = s) :
    lam * u * lam⁻¹ * (u : G)⁻¹ = 1 ∨ lam * u * lam⁻¹ * (u : G)⁻¹ = s := by
  have hlN := fz59u_lam_mem hB hF
  have hs1 := fz59u_s_ne_one hB hF
  set U : G := (u : G) with hU
  have hcR : lam * U * lam⁻¹ * U⁻¹ ∈ fz59R b := by
    have h := (hker (⟨lam, hlN⟩ * u * (⟨lam, hlN⟩ : normalizer _)⁻¹ * u⁻¹)).1 (by
      simp only [map_mul, map_inv, hu, fz59u_phi_lam hF.grid hΦ hlN]
      decide)
    simpa using h
  have hcfix : rho * (lam * U * lam⁻¹ * U⁻¹) * rho⁻¹ = lam * U * lam⁻¹ * U⁻¹ := by
    have h1 : Commute U rho := hur
    have h2 : Commute (lam * U * lam⁻¹) rho := by
      have h := (Commute.conj_iff lam).mpr h1
      rw [hF.grid.lam_rho] at h
      exact Commute.inv_right_iff.mp h
    have h3 : Commute (lam * U * lam⁻¹ * U⁻¹) rho := h2.mul_left h1.inv_left
    rw [← h3.eq, mul_inv_cancel_right]
  have hθ : U * (lam * U * lam⁻¹ * U⁻¹) * U⁻¹ = (lam * U * lam⁻¹ * U⁻¹)⁻¹ := by
    have hUi : U⁻¹ = U := fz59u_inv_eq hu2
    have hUU : U * U = 1 := by rw [← sq]; exact hu2
    calc U * (lam * U * lam⁻¹ * U⁻¹) * U⁻¹ = U * lam * U * lam⁻¹ * (U * U)⁻¹ := by group
      _ = U * lam * U * lam⁻¹ := by rw [hUU, inv_one, mul_one]
      _ = U * lam * U⁻¹ * lam⁻¹ := by rw [hUi]
      _ = (lam * U * lam⁻¹ * U⁻¹)⁻¹ := by group
  have ht := fz59u_inv_eq hB.str.t_sq
  have hs := fz59u_inv_eq (fz59u_s_sq hF.grid)
  rcases fz59_cent_rho hF.grid _ hcR hcfix with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, hut, ht] at hθ
    exact hs1 (mul_left_cancel (hθ.trans (mul_one t).symm))
  · exact Or.inr h
  · exfalso
    rw [h] at hθ
    have e2 : U * (t * s) * U⁻¹ = (U * t * U⁻¹) * (U * s * U⁻¹) := by group
    have hss : s * s = 1 := by rw [← sq]; exact fz59u_s_sq hF.grid
    rw [e2, hut, hus, mul_inv_rev, hs, ht, mul_assoc, hss, mul_one] at hθ
    exact hs1 (mul_right_cancel (hθ.symm.trans (one_mul t).symm))

theorem fz59u_delta_cases {t s lam rho : G} {b : Fin 3 → Fin 2 → G}
    (hG : Fz59Grid t s lam rho b) {U : G} {δ : Fin 3 → G} (hδZ : ∀ i, δ i ∈ fz59Z b)
    (hδ : ∀ i, U * b i 0 * U⁻¹ = b i 0 * b i 1 * δ i)
    (hδρ : ∀ i, δ (i + 1) = rho * δ i * rho⁻¹)
    (hc : lam * U * lam⁻¹ * U⁻¹ = 1 ∨ lam * U * lam⁻¹ * U⁻¹ = s) :
    (lam * U * lam⁻¹ * U⁻¹ = 1 ∧ (δ 0 = 1 ∨ δ 0 = b 0 0 ^ 2)) ∨
      (lam * U * lam⁻¹ * U⁻¹ = s ∧ (δ 0 = b 1 0 ^ 2 ∨ δ 0 = b 2 0 ^ 2)) := by
  have hb := hG.rows
  have hli : lam⁻¹ = lam := fz59u_inv_eq hG.lam_sq
  have hl10 : lam⁻¹ * b 0 0 * lam = b 1 0 := by
    rw [← hG.lam_01 0, hli]
  have hkey : lam * (U * b 1 0 * U⁻¹) * lam⁻¹ =
      (lam * U * lam⁻¹ * U⁻¹) * (U * b 0 0 * U⁻¹) * (lam * U * lam⁻¹ * U⁻¹)⁻¹ := by
    rw [← hl10]
    group
  have hL : lam * (U * b 1 0 * U⁻¹) * lam⁻¹ = b 0 0 * b 0 1 * (lam * δ 1 * lam⁻¹) := by
    rw [hδ 1]
    calc lam * (b 1 0 * b 1 1 * δ 1) * lam⁻¹ =
        (lam * b 1 0 * lam⁻¹) * (lam * b 1 1 * lam⁻¹) * (lam * δ 1 * lam⁻¹) := by group
      _ = b 0 0 * b 0 1 * (lam * δ 1 * lam⁻¹) := by rw [fz59u_lam_1 hG 0, fz59u_lam_1 hG 1]
  have hk1 : lam * U * lam⁻¹ * U⁻¹ = 1 → lam * δ 1 * lam⁻¹ = δ 0 := by
    intro hc1
    have h := hL.symm.trans hkey
    rw [hc1, one_mul, inv_one, mul_one, hδ 0] at h
    exact mul_left_cancel h
  have hks : lam * U * lam⁻¹ * U⁻¹ = s → lam * δ 1 * lam⁻¹ = b 0 0 ^ 2 * δ 0 := by
    intro hcs
    have h := hL.symm.trans hkey
    have hsδ : s * δ 0 * s⁻¹ = δ 0 := by
      rw [(fz59_Z_central hb (δ 0) (hδZ 0) s (fz59u_s_mem hG)).symm, mul_inv_cancel_right]
    have e : s * (b 0 0 * b 0 1 * δ 0) * s⁻¹ = b 0 0 * b 0 1 * (b 0 0 ^ 2 * δ 0) := by
      calc s * (b 0 0 * b 0 1 * δ 0) * s⁻¹ =
          (s * b 0 0 * s⁻¹) * (s * b 0 1 * s⁻¹) * (s * δ 0 * s⁻¹) := by group
        _ = b 0 0 * b 0 0 ^ 2 * b 0 1 * δ 0 := by
          rw [fz59u_s_b00 hG, fz59u_s_b01 hG, hsδ, (hb.quat 0).inv_eq]
        _ = b 0 0 * (b 0 0 ^ 2 * b 0 1) * δ 0 := by group
        _ = b 0 0 * b 0 1 * (b 0 0 ^ 2 * δ 0) := by rw [← (hb.quat 0).mul_comm_sq]; group
    rw [hcs, hδ 0, e] at h
    exact mul_left_cancel h
  have hz0 : b 0 0 ^ 2 ≠ 1 := (hb.quat 0).2.2.2
  have hδ1 : δ 1 = rho * δ 0 * rho⁻¹ := hδρ 0
  have r0 : rho * b 0 0 * rho⁻¹ = b 1 0 := hG.rho_b 0 0
  have r1 : rho * b 1 0 * rho⁻¹ = b 2 0 := hG.rho_b 1 0
  have r2 : rho * b 2 0 * rho⁻¹ = b 0 0 := hG.rho_b 2 0
  rcases (fz59_mem_Z hb _).1 (hδZ 0) with h0 | h0 | h0 | h0
  · have e : lam * δ 1 * lam⁻¹ = 1 := by rw [hδ1, h0]; group
    rcases hc with hc | hc
    · exact Or.inl ⟨hc, Or.inl h0⟩
    · exfalso
      have h := hks hc
      rw [e, h0, mul_one] at h
      exact hz0 h.symm
  · have e : lam * δ 1 * lam⁻¹ = b 0 0 ^ 2 := by
      rw [hδ1, h0, ← conj_pow, r0, ← conj_pow, fz59u_lam_1 hG 0]
    rcases hc with hc | hc
    · exact Or.inl ⟨hc, Or.inr h0⟩
    · exfalso
      have h := hks hc
      rw [e, h0, (hb.quat 0).sq_mul_sq] at h
      exact hz0 h
  · have e : lam * δ 1 * lam⁻¹ = b 2 0 ^ 2 := by
      rw [hδ1, h0, ← conj_pow, r1, ← conj_pow, hG.lam_2 0]
    rcases hc with hc | hc
    · exfalso
      have h := hk1 hc
      rw [e, h0, hb.sq_eq] at h
      exact hz0 (mul_right_cancel (h.trans (one_mul _).symm))
    · exact Or.inr ⟨hc, Or.inl h0⟩
  · have e : lam * δ 1 * lam⁻¹ = b 1 0 ^ 2 := by
      rw [hδ1, h0, ← conj_pow, r2, ← conj_pow, hG.lam_01 0]
    rcases hc with hc | hc
    · exfalso
      have h := hk1 hc
      rw [e, h0, hb.sq_eq] at h
      exact hz0 (mul_right_cancel ((one_mul _).trans h)).symm
    · exact Or.inr ⟨hc, Or.inr h0⟩

theorem fz59u_delta_one {rho : G} {δ : Fin 3 → G} (hδρ : ∀ i, δ (i + 1) = rho * δ i * rho⁻¹)
    (h0 : δ 0 = 1) : ∀ i, δ i = 1 := by
  have h1 : δ 1 = 1 := by rw [show δ 1 = rho * δ 0 * rho⁻¹ from hδρ 0, h0]; group
  have h2 : δ 2 = 1 := by rw [show δ 2 = rho * δ 1 * rho⁻¹ from hδρ 1, h1]; group
  intro i
  rcases fz59u_fin3 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem fz59u_delta_all {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (hG : Fz59Grid t s lam rho b)
    {δ : Fin 3 → G} (hδρ : ∀ i, δ (i + 1) = rho * δ i * rho⁻¹) {j : Fin 3}
    (h0 : δ 0 = b j 0 ^ 2) : ∀ i, δ i = b (i + j) 0 ^ 2 := by
  have hz : ∀ k, rho * b k 0 ^ 2 * rho⁻¹ = b (k + 1) 0 ^ 2 := fun k => by
    rw [← conj_pow, hG.rho_b]
  have h1 : δ 1 = b (j + 1) 0 ^ 2 := by
    rw [show δ 1 = rho * δ 0 * rho⁻¹ from hδρ 0, h0, hz]
  have h2 : δ 2 = b (j + 1 + 1) 0 ^ 2 := by
    rw [show δ 2 = rho * δ 1 * rho⁻¹ from hδρ 1, h1, hz]
  intro i
  rcases fz59u_fin3 i with rfl | rfl | rfl
  · rw [h0, zero_add]
  · rw [h1, add_comm]
  · rw [h2, show j + 1 + 1 = 2 + j by
      rcases fz59u_fin3 j with rfl | rfl | rfl <;> rfl]

theorem fz59u_sub_one (i : Fin 3) : i - 1 = i + 2 := by
  rcases fz59u_fin3 i with rfl | rfl | rfl <;> rfl

theorem fz59u_twist {t tau lam rho x₁ x₂ s u : G} {b : Fin 3 → Fin 2 → G}
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) {δ : Fin 3 → G}
    (hu2 : u ^ 2 = 1) (hur : u * rho = rho * u) (hut : u * t * u⁻¹ = t * s)
    (hb1 : ∀ i, u * b i 1 * u⁻¹ = (b i 1)⁻¹)
    (hδ : ∀ i, u * b i 0 * u⁻¹ = b i 0 * b i 1 * δ i)
    (hδρ : ∀ i, δ (i + 1) = rho * δ i * rho⁻¹)
    (hcases : (lam * u * lam⁻¹ * u⁻¹ = 1 ∧ (δ 0 = 1 ∨ δ 0 = b 0 0 ^ 2)) ∨
      (lam * u * lam⁻¹ * u⁻¹ = s ∧ (δ 0 = b 1 0 ^ 2 ∨ δ 0 = b 2 0 ^ 2))) :
    ∃ b' : Fin 3 → Fin 2 → G, Fz59Frame t tau lam rho x₁ x₂ s b' ∧
      (Fz59UGood t s lam rho u b' ∨ Fz59UBad t s lam rho u b') := by
  have hb := hF.grid.rows
  have hb1i : ∀ i, u * fz59uInv b i 1 * u⁻¹ = (fz59uInv b i 1)⁻¹ := fun i => by
    show u * (b i 1)⁻¹ * u⁻¹ = ((b i 1)⁻¹)⁻¹
    rw [← conj_inv, hb1]
  have hlN1 : lam * u * lam⁻¹ * u⁻¹ = 1 → lam * u = u * lam := fun h =>
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
  rcases hcases with ⟨hc, h0 | h0⟩ | ⟨hc, h0 | h0⟩
  · have hd := fz59u_delta_one hδρ h0
    exact ⟨b, hF, Or.inr ⟨hu2, hur, hb1, fun i => by rw [hδ i, hd i, mul_one], hut, hlN1 hc⟩⟩
  · have hd := fz59u_delta_all hF.grid hδρ h0
    refine ⟨fz59uInv b, fz59u_frame_inv hF, Or.inr ⟨hu2, hur, hb1i, fun i => ?_, hut, hlN1 hc⟩⟩
    show u * b i 0 * u⁻¹ = b i 0 * (b i 1)⁻¹
    rw [hδ i, hd i, add_zero, mul_assoc, (hb.quat i).q_inv_eq]
  · have hd := fz59u_delta_all hF.grid hδρ h0
    refine ⟨fz59uInv b, fz59u_frame_inv hF, Or.inl ⟨hu2, hur, hb1i, fun i => ?_, hut, hc⟩⟩
    show u * b i 0 * u⁻¹ = b i 0 * (b i 1)⁻¹ * b (i - 1) 0 ^ 2
    rw [hδ i, hd i, (hb.quat i).q_inv_eq, ← fz59u_z_mul hb i]
    group
  · have hd := fz59u_delta_all hF.grid hδρ h0
    refine ⟨b, hF, Or.inl ⟨hu2, hur, hb1, fun i => ?_, hut, hc⟩⟩
    rw [hδ i, hd i, fz59u_sub_one i]

theorem fz59u_not_T2 [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b) {u δ : G} (hδ : δ ∈ fz59Z b)
    (hu : u * b 0 0 * u⁻¹ = b 0 0 * b 0 1 * δ) : u ∉ T₂ := by
  intro huT
  have hN : u ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := hB.T2_le huT
  have hb00 : b 0 0 ∈ ctxW t x₁ x₂ := by
    rw [hF.hW]
    exact subset_closure ⟨0, rfl⟩
  have hδW : δ ∈ ctxW t x₁ x₂ := hB.str.EW (hB.str.ZE (by rw [hF.hZ]; exact hδ))
  have h1 := (mem_normalizer_iff.mp hN _).1 hb00
  rw [hu] at h1
  have hb01 : b 0 1 ∈ ctxW t x₁ x₂ := by
    have := mul_mem (mul_mem (inv_mem hb00) h1) (inv_mem hδW)
    simpa [mul_assoc] using this
  exact (hF.grid.quat 0).not_commute (hB.str.W_comm _ hb01 _ hb00)

theorem fz59u_T3 [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ : G} {T₂ : Subgroup G}
    (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) {u : G} (hu2 : u ^ 2 = 1)
    (huR : ∀ r ∈ fzR t x₁ x₂, u * r * u⁻¹ ∈ fzR t x₁ x₂) (hlam : u * lam * u⁻¹ ∈ T₂)
    (hnot : u ∉ T₂) :
    Nat.card (T₂ ⊔ zpowers u : Subgroup G) = 2 ^ 10 ∧ FzSylow (T₂ ⊔ zpowers u) := by
  have hT2 := (fzl59f_R_eq_R6_of_str hB.str hB.shape).2
  have huT : ∀ x ∈ T₂, u * x * u⁻¹ ∈ T₂ := by
    have hle : T₂ ≤ T₂.comap (MulAut.conj u).toMonoidHom := by
      conv_lhs => rw [hT2]
      refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
      · exact hB.str.RT (huR r hr)
      · exact hlam
    exact fun x hx => hle hx
  have hnorm : u ∈ normalizer ((T₂ : Subgroup G) : Set G) :=
    fzl59c_mem_normalizer_of_sq huT (fun m _ => by rw [hu2, one_mul, mul_one])
  have hpu : IsPGroup 2 (zpowers u) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hu2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hp : IsPGroup 2 (T₂ ⊔ zpowers u : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hB.T2_p hpu (zpowers_le.mpr hnorm)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hlt : Nat.card T₂ < Nat.card (T₂ ⊔ zpowers u : Subgroup G) := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hnot ?_)
    rw [h]
    exact mem_sup_right (mem_zpowers u)
  have hdvd : Nat.card (T₂ ⊔ zpowers u : Subgroup G) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card _
  rw [hk, hB.shape.card] at hlt
  rw [hk] at hdvd
  have hk10 : 10 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk11 : k < 11 := by
    by_contra h
    exact hB.bound ((Nat.pow_dvd_pow 2 (by omega)).trans hdvd)
  have hk' : k = 10 := by omega
  subst hk'
  refine ⟨hk, hp, fun h2 => hB.bound ?_⟩
  rw [← Subgroup.card_mul_index (T₂ ⊔ zpowers u), hk, show 2 ^ 11 = 2 ^ 10 * 2 by norm_num]
  exact mul_dvd_mul_left _ h2

theorem fz59u_card_N3 [Finite G] {t tau lam rho x₁ x₂ s : G} {b : Fin 3 → Fin 2 → G}
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b) (hcard : Nat.card Φ.range = 12) :
    Nat.card (fz59N3 t x₁ x₂) = 3 * 2 ^ 10 := by
  have hk : Φ.ker = (fz59R b).subgroupOf (normalizer ((fz59R b : Subgroup G) : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hkc : Nat.card Φ.ker = 2 ^ 8 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_normalizer).toEquiv,
      fz59_card_R hF.grid.rows]
  rw [fz59N3, hF.hR, ← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, hcard, hkc]
  norm_num

theorem fz59u_out [Finite G] {t tau lam rho x₁ x₂ s u : G} {b : Fin 3 → Fin 2 → G}
    {T₂ T₃ : Subgroup G} (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b)
    (hT₂ : T₂ = fzR t x₁ x₂ ⊔ zpowers lam) (hT₃ : T₃ = T₂ ⊔ zpowers u)
    (hcard : Nat.card T₃ = 2 ^ 10) (hsyl : FzSylow T₃)
    (hN3 : Nat.card (fz59N3 t x₁ x₂) = 3 * 2 ^ 10) :
    Fz59Out t T₂ x₁ x₂ lam rho tau s u b T₃ :=
  ⟨hF.grid, hF.s_cases, hu, hF.hR, hF.hZ, hF.z3, hF.hW, hF.hE, hT₂, hT₃, hcard, hsyl, hN3⟩

theorem fz59u_main [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b)
    (hN3 : Nat.card (fz59N3 t x₁ x₂) = 3 * 2 ^ 10)
    (hg : fz59ColPerm (Equiv.swap 0 2) ∈ Φ.range) :
    ∃ (s' u : G) (b' : Fin 3 → Fin 2 → G) (T₃ : Subgroup G),
      Fz59Out t T₂ x₁ x₂ lam rho tau s' u b' T₃ := by
  obtain ⟨u, hug, hu2, hur, hut⟩ := fz59u_invol hB hF hΦ hker hg
  obtain ⟨hb1, -, δ, hδZ, hδ, hδρ⟩ := fz59u_act hF.grid hΦ u hug hu2 hur
  have hus := fz59u_u_s hF.grid hb1
  have hc := fz59u_comm_cases hB hF hΦ hker u hug hu2 hur hut hus
  have hcases := fz59u_delta_cases hF.grid hδZ hδ hδρ hc
  have hnot : (u : G) ∉ T₂ := fz59u_not_T2 hB hF (hδZ 0) (hδ 0)
  have huR : ∀ r ∈ fzR t x₁ x₂, (u : G) * r * (u : G)⁻¹ ∈ fzR t x₁ x₂ := by
    rw [hF.hR]
    exact fun r hr => (mem_normalizer_iff.mp u.2 r).1 hr
  have hcR : lam * u * lam⁻¹ * (u : G)⁻¹ ∈ fzR t x₁ x₂ := by
    rw [hF.hR]
    rcases hc with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact fz59u_s_mem hF.grid
  have hlam : (u : G) * lam * (u : G)⁻¹ ∈ T₂ := by
    have e : (u : G) * lam * (u : G)⁻¹ = (lam * u * lam⁻¹ * (u : G)⁻¹)⁻¹ * lam := by group
    rw [e]
    exact mul_mem (inv_mem (hB.str.RT hcR)) hB.str.lam_T
  obtain ⟨hcard3, hsyl⟩ := fz59u_T3 hB hu2 huR hlam hnot
  obtain ⟨b', hF', hu'⟩ := fz59u_twist hF hu2 hur hut hb1 hδ hδρ hcases
  exact ⟨s, u, b', T₂ ⊔ zpowers (u : G), fz59u_out hF' hu'
    (fzl59f_R_eq_R6_of_str hB.str hB.shape).2 rfl hcard3 hsyl hN3⟩

theorem fz59_u [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ s : G} {T₂ : Subgroup G}
    {b : Fin 3 → Fin 2 → G} (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂)
    (hF : Fz59Frame t tau lam rho x₁ x₂ s b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (hker : ∀ n, Φ n = 1 ↔ (n : G) ∈ fz59R b)
    (hcard : Nat.card Φ.range = 12) {σ : Equiv.Perm (Fin 3)}
    (hσ : σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 0 1) (hg : fz59ColPerm σ ∈ Φ.range) :
    ∃ (s' u : G) (b' : Fin 3 → Fin 2 → G) (T₃ : Subgroup G),
      Fz59Out t T₂ x₁ x₂ lam rho tau s' u b' T₃ := by
  have hN3 := fz59u_card_N3 hF hker hcard
  rcases hσ with rfl | rfl
  · exact fz59u_main hB hF hΦ hker hN3 hg
  · obtain ⟨Φ', hΦ', hker', hg'⟩ := fz59u_phi_rel hF.grid.rows hΦ hker hg
    exact fz59u_main hB (fz59u_frame_rel hF) hΦ' hker' hN3 hg'

end CFSG.OddStandard.SmallF3.FritzII
