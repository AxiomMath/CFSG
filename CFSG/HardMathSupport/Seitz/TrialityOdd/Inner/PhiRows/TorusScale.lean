module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OddIdx
public import CFSG.GH74.GLS.Stage4.HexCoordD4
public import CFSG.LieType.Steinberg.CentralExt.TrialityTorus
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

section TorusScale

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

omit hσ in
theorem isSquare_map_iff_aux (hσ : ∀ c, σ (σ (σ c)) = c) (a : K) : IsSquare (σ a) → IsSquare a := by
  intro h
  have h2 : IsSquare (σ (σ a)) := by
    obtain ⟨r, hr⟩ := h
    exact ⟨σ r, by rw [hr, map_mul]⟩
  have h3 : IsSquare (σ (σ (σ a))) := by
    obtain ⟨r, hr⟩ := h2
    exact ⟨σ r, by rw [hr, map_mul]⟩
  rwa [hσ] at h3

omit hσ in
theorem quadraticChar_map [Fintype K] [DecidableEq K] (hσ : ∀ c, σ (σ (σ c)) = c) {a : K}
    (ha : a ≠ 0) : quadraticChar K (σ a) = quadraticChar K a := by
  have hσa : σ a ≠ 0 := fun h => ha (by simpa using (map_eq_zero σ).1 h)
  have key : quadraticChar K (σ a) = 1 ↔ quadraticChar K a = 1 := by
    rw [quadraticChar_one_iff_isSquare hσa, quadraticChar_one_iff_isSquare ha]
    exact ⟨isSquare_map_iff_aux hσ a, fun ⟨r, hr⟩ => ⟨σ r, by rw [hr, map_mul]⟩⟩
  rcases quadraticChar_dichotomy ha with h | h
  · rw [h]; exact key.2 h
  · rw [h]
    rcases quadraticChar_dichotomy hσa with h' | h'
    · exact absurd (key.1 h') (by rw [h]; decide)
    · exact h'

theorem isSquare_sigma_mul [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {u : K} (hu : u ≠ 0) :
    IsSquare (σ u * σ (σ u)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : σ u ≠ 0 := fun h => hu (by simpa using (map_eq_zero σ).1 h)
  have h2 : σ (σ u) ≠ 0 := fun h => h1 (by simpa using (map_eq_zero σ).1 h)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero h1 h2), map_mul,
    quadraticChar_map hσ h1, quadraticChar_map hσ hu]
  have := quadraticChar_sq_one hu
  rw [pow_two] at this
  exact this

theorem exists_sqrt_norm [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {u : K} (hu : u ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ r * r = σ u * σ (σ u) ∧ r * σ r * σ (σ r) = u * σ u * σ (σ u) := by
  obtain ⟨r₀, hr₀s⟩ := isSquare_sigma_mul hσ hu
  have hr₀ : r₀ * r₀ = σ u * σ (σ u) := hr₀s.symm
  have h1 : σ u ≠ 0 := fun h => hu (by simpa using (map_eq_zero σ).1 h)
  have h2 : σ (σ u) ≠ 0 := fun h => h1 (by simpa using (map_eq_zero σ).1 h)
  have hr0 : r₀ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero h1 h2 (by rw [hr₀s]; simp)
  have hsq : (r₀ * σ r₀ * σ (σ r₀)) ^ 2 = (u * σ u * σ (σ u)) ^ 2 := by
    have e1 : σ (r₀ * r₀) = σ (σ u * σ (σ u)) := by rw [hr₀]
    have e2 : σ (σ (r₀ * r₀)) = σ (σ (σ u * σ (σ u))) := by rw [hr₀]
    simp only [map_mul, hσ] at e1 e2
    calc (r₀ * σ r₀ * σ (σ r₀)) ^ 2 = (r₀ * r₀) * (σ r₀ * σ r₀) * (σ (σ r₀) * σ (σ r₀)) := by ring
      _ = _ := by rw [hr₀, e1, e2]; ring
  have hcases := sq_eq_sq_iff_eq_or_eq_neg.1 hsq
  rcases hcases with h | h
  · exact ⟨r₀, hr0, hr₀, h⟩
  · refine ⟨-r₀, neg_ne_zero.2 hr0, by rw [neg_mul_neg]; exact hr₀, ?_⟩
    simp only [map_neg]
    calc -r₀ * -σ r₀ * -σ (σ r₀) = -(r₀ * σ r₀ * σ (σ r₀)) := by ring
      _ = _ := by rw [h, neg_neg]

end TorusScale

section TorusScale2


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

omit hσ in
theorem chi_hexRoot_two (t : Kˣ) :
    chi σ.toRingHom 1 t (d43Lift (hexRoot 2)) =
      t⁻¹ * Units.map σ.toRingHom.toMonoidHom t *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t) := by
  have e0 : pr (nd 0) (d43Lift (hexRoot 2)) = -1 := by decide +kernel
  have e1 : pr (nd 1) (d43Lift (hexRoot 2)) = 1 := by decide +kernel
  have e3 : pr (nd 3) (d43Lift (hexRoot 2)) = 1 := by decide +kernel
  simp only [chi, e0, e1, e3, one_zpow, one_mul, zpow_neg_one, zpow_one]

omit hσ in
theorem chi_hexRoot_four (t : Kˣ) :
    chi σ.toRingHom 1 t (d43Lift (hexRoot 4)) =
      t * (Units.map σ.toRingHom.toMonoidHom t)⁻¹ *
        (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t))⁻¹ := by
  have e0 : pr (nd 0) (d43Lift (hexRoot 4)) = 1 := by decide +kernel
  have e1 : pr (nd 1) (d43Lift (hexRoot 4)) = -1 := by decide +kernel
  have e3 : pr (nd 3) (d43Lift (hexRoot 4)) = -1 := by decide +kernel
  simp only [chi, e0, e1, e3, one_zpow, one_mul, zpow_neg_one, zpow_one]

include hσ in
theorem tor_conj_d4X_four (s : fixedUnits σ.toRingHom) (t : Kˣ) (u : K) :
    tor hσ s t * d4X hσ 4 u * (tor hσ s t)⁻¹ =
      d4X hσ 4 (((chi σ.toRingHom s t (d43Lift (hexRoot 4)) : Kˣ) : K) * u) := by
  apply Subtype.ext
  have hα := isRoot_d43Lift (isRoot_hexRoot 4)
  have := torE_conj_xOrbit (σ := σ.toRingHom) hσ ((mem_fixedUnits σ.toRingHom).1 s.2) t hα u
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, tor_val hσ]
  exact this

include hσ in
theorem tor_conj_d4X_two (s : fixedUnits σ.toRingHom) (t : Kˣ) (u : K) :
    tor hσ s t * d4X hσ 2 u * (tor hσ s t)⁻¹ =
      d4X hσ 2 (((chi σ.toRingHom s t (d43Lift (hexRoot 2)) : Kˣ) : K) * u) := by
  apply Subtype.ext
  have hα := isRoot_d43Lift (isRoot_hexRoot 2)
  have := torE_conj_xOrbit (σ := σ.toRingHom) hσ ((mem_fixedUnits σ.toRingHom).1 s.2) t hα (-u)
  rw [mul_neg] at this
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, tor_val hσ]
  exact this

include hσ in
theorem exists_t_chi_two [Finite K] (u : Kˣ) :
    ∃ t : Kˣ, chi σ.toRingHom 1 t (d43Lift (hexRoot 2)) = u := by
  obtain ⟨r, hr0, hrr, hrN⟩ := exists_sqrt_norm hσ u.ne_zero
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [chi_hexRoot_two]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  field_simp
  have : r * (σ.toRingHom r * σ.toRingHom (σ.toRingHom r)) = (u : K) * (r * r) := by
    calc r * (σ.toRingHom r * σ.toRingHom (σ.toRingHom r))
        = r * σ.toRingHom r * σ.toRingHom (σ.toRingHom r) := by ring
      _ = u * σ.toRingHom u * σ.toRingHom (σ.toRingHom u) := hrN
      _ = u * (r * r) := by rw [mul_assoc, hrr]
  exact mul_left_cancel₀ hr0 (by rw [this]; ring)

include hσ in
theorem exists_t_chi_four [Finite K] (u : Kˣ) :
    ∃ t : Kˣ, chi σ.toRingHom 1 t (d43Lift (hexRoot 4)) = u := by
  obtain ⟨t, ht⟩ := exists_t_chi_two hσ u
  refine ⟨t⁻¹, ?_⟩
  rw [chi_hexRoot_four, ← ht, chi_hexRoot_two]
  simp only [map_inv, inv_inv]

end TorusScale2

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
