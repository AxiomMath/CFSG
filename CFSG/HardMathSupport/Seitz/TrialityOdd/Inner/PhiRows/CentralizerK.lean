module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingTwisted
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Tori

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits
open scoped MatrixGroups commutatorElement

section CentralizerK


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem diagGL_one :
    (CFSG.ClassicalInvolution.G2D4Models.diagGL (1 : Kˣ) : GL (Fin 2) K) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.ClassicalInvolution.G2D4Models.diagGL]

include hσ in
theorem nHat_one_eq_slShort :
    nHat σ (ng 1) = slShort σ hσ (sl2Upper (1 : K) * sl2Lower (-1 : K) * sl2Upper (1 : K)) := by
  have h1 : σ (1 : K) = 1 := map_one σ
  have h2 : σ (-1 : K) = -1 := by rw [map_neg, map_one]
  refine Subtype.ext ?_
  rw [map_mul, map_mul]
  rw [nHat_val, nHatE_one_eq, Subgroup.coe_mul, Subgroup.coe_mul, slShort_upper, slShort_lower]
  simp only [h1, h2]

theorem HSL_mul_W_mul_HSL (t : Kˣ) :
    HSL t * (sl2Upper (1 : K) * sl2Lower (-1 : K) * sl2Upper (1 : K)) * HSL t =
      sl2Upper (1 : K) * sl2Lower (-1 : K) * sl2Upper (1 : K) := by
  apply Subtype.ext
  show ((HSL t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      ((sl2Upper (1 : K) * sl2Lower (-1 : K) * sl2Upper (1 : K) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) * (HSL t : SL(2, K)) = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HSL, sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]

include hσ in
theorem slShort_HSL_mul_nHat_one (t : Kˣ) :
    slShort σ hσ (HSL t) * nHat σ (ng 1) = nHat σ (ng 1) * (slShort σ hσ (HSL t))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, nHat_one_eq_slShort hσ, ← map_mul, ← map_mul,
    HSL_mul_W_mul_HSL]

include hσ in
theorem slShort_HSL_commute_slLong (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1)
    (C : SL(2, fixedField σ)) : Commute (slShort σ hσ (HSL t)) (slLong σ hσ C) := by
  have hx := twistedIncl_slShort_HSL hσ t
  obtain ⟨s, hs, hconj⟩ := torus_conj_slLong hσ hx
  have hc1 : d4.cartan (nd 1) (nd 2) = -1 := by decide
  have hc3 : d4.cartan (nd 3) (nd 2) = -1 := by decide
  have hb : ((t ^ d4.cartan (nd 0) (nd 2) * (Units.map σ.toMonoidHom t) ^ d4.cartan (nd 1) (nd 2) *
      (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) ^ d4.cartan (nd 3) (nd 2) : Kˣ) :
        K) = 1 := by
    rw [cartan_zero_two, hc1, hc3]
    simp only [zpow_neg, zpow_one, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
    rw [← mul_inv, ← mul_inv]
    exact inv_eq_one.2 ht
  have hs1 : s = 1 := Units.ext (Subtype.ext (hs.trans hb))
  have h := hconj C
  rw [hs1, diagGL_one, glConjSL_one] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem hexPos_six : hexPos 6 = Pi.single (ng 0) 1 := by
  funext i; fin_cases i <;> rfl

theorem hexPos_neg_six : hexPos (-6) = -Pi.single (ng 0) 1 := by
  funext i; fin_cases i <;> rfl

include hσ in
theorem slShort_HSL_commute_root_six (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1) :
    (∀ x ∈ hexGroup (twistedX σ) 6, Commute (slShort σ hσ (HSL t)) x) ∧
    (∀ x ∈ hexGroup (twistedX σ) (-6), Commute (slShort σ hσ (HSL t)) x) := by
  have hle := rankOne_long_le_range_slLong σ hσ
  have h6 : hexGroup (twistedX σ) 6 ≤ rankOne (twistedRootGroup σ) (ng 0) := by
    show twistedRootGroup σ (hexPos 6) ≤ _
    rw [hexPos_six]
    exact le_sup_left
  have hm6 : hexGroup (twistedX σ) (-6) ≤ rankOne (twistedRootGroup σ) (ng 0) := by
    show twistedRootGroup σ (hexPos (-6)) ≤ _
    rw [hexPos_neg_six]
    exact le_sup_right
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨C, rfl⟩ := hle (h6 hx)
    exact slShort_HSL_commute_slLong hσ t ht C
  · obtain ⟨C, rfl⟩ := hle (hm6 hx)
    exact slShort_HSL_commute_slLong hσ t ht C

theorem longSub_le_centralizer_slShort_HSL
    (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1) :
    longSub 6 (hexGroup (twistedX σ)) ≤ Subgroup.centralizer {slShort σ hσ (HSL t)} := by
  have R := d4RGD2 σ hσ
  obtain ⟨h6, hm6⟩ := slShort_HSL_commute_root_six hσ t ht
  have hr₂ : Commute (slShort σ hσ (HSL t)) (nHat σ (ng 0)) := by
    obtain ⟨C, hC⟩ := rankOne_long_le_range_slLong σ hσ (nHat_mem_rankOne σ (ng 0))
    rw [← hC]
    exact slShort_HSL_commute_slLong hσ t ht C
  exact longSub_le_centralizer R _ h6 hm6 hr₂ (slShort_HSL_mul_nHat_one hσ t)

include hσ in
theorem d4X_zero_zero : d4X hσ 0 (0 : K) = 1 := by
  let φ : K →+ Additive (twistedGroup σ) :=
    AddMonoidHom.mk' (fun c : K => Additive.ofMul (d4X hσ 0 c)) fun a b =>
      congrArg Additive.ofMul (d4X_add hσ 0 a b)
  exact map_zero φ

include hσ in
theorem slShort_HSL_mem_hHat (t : Kˣ) :
    slShort σ hσ (HSL t) ∈ hHat σ (ng 1) := by
  show ((slShort σ hσ (HSL t) : twistedGroup σ) : adjointGroup d4 K) ∈ hHatE σ (ng 1)
  rw [slShort_HSL hσ]
  exact ⟨t, rfl⟩

include hσ in
theorem eq_top_of_long_torus_short
    [Finite K] (h2 : (2 : K) ≠ 0) (H : Subgroup (twistedGroup σ))
    (hlong : longSub 6 (hexGroup (twistedX σ)) ≤ H) (hT : (⨆ i, hHat σ i) ≤ H) {k : ℤ}
    (hk : k = 1 ∨ k = 5 ∨ k = -3 ∨ k = 3 ∨ k = -1 ∨ k = -5)
    {x : twistedGroup σ} (hx : x ∈ hexGroup (twistedX σ) k) (hxH : x ∈ H) (hx1 : x ≠ 1) :
    H = ⊤ := by
  have R := d4RGD2 σ hσ
  obtain ⟨v0, v2, v4, v6, -, v10⟩ := Rt6_values
  have key : ∀ P : Subgroup (twistedGroup σ), longSub 6 (hexGroup (twistedX σ)) ≤ P →
      (⨆ i, hHat σ i) ≤ P → (∃ y ∈ hexGroup (twistedX σ) 1, y ∈ P ∧ y ≠ 1) → P = ⊤ := by
    intro P hl hTP ⟨y, hy, hyP, hy1⟩
    obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 0 (by norm_num)).1 hy
    have hc : c ≠ 0 := by
      rintro rfl
      exact hy1 (d4X_zero_zero hσ)
    exact eq_top_of_long_short hσ h2 P hl
      (fun l => hTP (Subgroup.mem_iSup_of_mem (ng 1) (slShort_HSL_mem_hHat hσ l))) hc hyP
  have hswap : ∀ (q : ℤ), Rt 6 q = k → (Rt 6 (2 - q) = 1 ∨ Rt 6 (2 - q) = 5 ∨ Rt 6 (2 - q) = -3) →
      H = ⊤ := by
    intro q hq hq'
    obtain ⟨w, hwE, -, hwg, hwH⟩ := exists_swap R
    let P' : Subgroup (twistedGroup σ) := H.comap (MulAut.conj w).toMonoidHom
    have memP' : ∀ g, g ∈ P' ↔ w * g * w⁻¹ ∈ H := fun g => Iff.rfl
    have hl' : longSub 6 (hexGroup (twistedX σ)) ≤ P' := fun g hg => by
      rw [memP']
      exact hlong (conj_mem_longSub (by norm_num) (by norm_num) hwE hg)
    have hT' : (⨆ i, hHat σ i) ≤ P' := fun g hg => by
      rw [memP']
      exact hT (hwH g hg)
    have hy : w⁻¹ * x * (w⁻¹)⁻¹ ∈ hexGroup (twistedX σ) (Rt 6 (2 - q)) := hwg q x (by rw [hq]; exact hx)
    have hyP : w⁻¹ * x * (w⁻¹)⁻¹ ∈ P' := by
      rw [memP']
      have e : w * (w⁻¹ * x * (w⁻¹)⁻¹) * w⁻¹ = x := by group
      rw [e]; exact hxH
    have hy1 : w⁻¹ * x * (w⁻¹)⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have e : w * (w⁻¹ * x * (w⁻¹)⁻¹) * w⁻¹ = x := by group
      rw [← e, h]; group
    obtain ⟨y, hy', hyP', hy1'⟩ := exists_nonzero_root_one R P' hl' hq' hy hyP hy1
    have htop : P' = ⊤ := key P' hl' hT' ⟨y, hy', hyP', hy1'⟩
    rw [eq_top_iff]
    intro g _
    have : w⁻¹ * g * w ∈ P' := by rw [htop]; trivial
    rw [memP'] at this
    have e : w * (w⁻¹ * g * w) * w⁻¹ = g := by group
    rwa [e] at this
  rcases hk with hk | hk | hk | hk | hk | hk
  · exact key H hlong hT (exists_nonzero_root_one R H hlong (Or.inl hk) (hk ▸ hx) hxH hx1)
  · exact key H hlong hT (exists_nonzero_root_one R H hlong (Or.inr (Or.inl hk)) (hk ▸ hx) hxH hx1)
  · exact key H hlong hT (exists_nonzero_root_one R H hlong (Or.inr (Or.inr hk)) (hk ▸ hx) hxH hx1)
  · exact hswap 2 (by rw [hk]; exact v2) (Or.inl (by rw [show (2 : ℤ) - 2 = 0 by norm_num]; exact v0))
  · exact hswap 6 (by rw [hk]; exact v6) (Or.inr (Or.inr (by
      rw [show (2 : ℤ) - 6 = -4 by norm_num, Rt_of_neg (by norm_num) (by norm_num)]; norm_num)))
  · exact hswap 10 (by rw [hk]; exact v10) (Or.inr (Or.inl (by
      have h := Rt_add_mul 6 (-8) 1
      rw [show (-8 : ℤ) + 2 * ((6 : ℕ) : ℤ) * 1 = 4 by norm_num] at h
      rw [show (2 : ℤ) - 10 = -8 by norm_num, ← h]; exact v4)))

end CentralizerK

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
