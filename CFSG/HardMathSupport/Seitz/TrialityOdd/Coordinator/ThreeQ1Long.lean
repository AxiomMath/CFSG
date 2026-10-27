module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4LongZ
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylTwist
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBCentralizerL
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSL3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem le_centralizer_of_perfect_of_le_normalizer {Z P : Subgroup G} [IsCyclic Z]
    (hP : ⁅P, P⁆ = P) (hPN : P ≤ Subgroup.normalizer (Z : Set G)) :
    P ≤ Subgroup.centralizer (Z : Set G) := by
  have hcomm : ∀ x y : MulAut Z, x * y = y * x := fun x y => by
    apply (IsCyclic.mulAutMulEquiv Z).injective
    rw [map_mul, map_mul, mul_comm]
  have hcomm' : ⁅P, P⁆ ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    set a' : Subgroup.normalizer (Z : Set G) := ⟨a, hPN ha⟩
    set b' : Subgroup.normalizer (Z : Set G) := ⟨b, hPN hb⟩
    have hker : ⁅a', b'⁆ ∈ (Subgroup.normalizerMonoidHom Z).ker := by
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm ((Subgroup.normalizerMonoidHom Z) a') ((Subgroup.normalizerMonoidHom Z) b')]
      group
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  rw [hP] at hcomm'
  exact hcomm'

end Abstract

section Long


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem slLong_HSL_mem_hHat_zero (s : (fixedField σ)ˣ) :
    slLong σ hσ (HSL s) ∈ hHat σ (ng 0) := by
  show ((slLong σ hσ (HSL s) : twistedGroup σ) : adjointGroup d4 K) ∈ hHatE σ (ng 0)
  rw [slLong_val, slLongE_HSL]
  exact ⟨⟨Units.map (fixedField σ).subtype.toMonoidHom s,
    (mem_fixedUnits σ).2 (s : fixedField σ).2⟩, rfl⟩

include hσ in
theorem slLong_HSL_mem_longSub (s : (fixedField σ)ˣ) :
    slLong σ hσ (HSL s) ∈ longSub 6 (hexGroup (twistedX σ)) :=
  CFSG.GH74.GLS.Stage2.Bender.Thm1.d4z_hHat_zero_le_longSub hσ (slLong_HSL_mem_hHat_zero hσ s)

include hσ in
theorem slShort_HSL_fixed_mem_longSub (s : (fixedField σ)ˣ) :
    slShort σ hσ (HSL (Units.map (fixedField σ).subtype.toMonoidHom s)) ∈
      longSub 6 (hexGroup (twistedX σ)) := by
  set s' : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom s with hs'
  set h := slLong σ hσ (HSL s) with hh
  have hx := twistedIncl_slLong_HSL hσ s
  obtain ⟨u, hu, hconj⟩ := torus_conj_slShort hσ hx
  have hu' : u = s'⁻¹ := by
    apply Units.ext
    rw [hu]
    show ((s' ^ d4.cartan (nd 2) (nd 0) : Kˣ) : K) = ((s'⁻¹ : Kˣ) : K)
    rw [show d4.cartan (nd 2) (nd 0) = -1 by decide, zpow_neg_one]
  have key : h * nHat σ (ng 1) * h⁻¹ = nHat σ (ng 1) * slShort σ hσ (HSL s') := by
    rw [nHat_one_eq_slShort hσ, hconj, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [glConjSL_coe, hu']
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.ClassicalInvolution.G2D4Models.diagGL, HSL, sl2Upper, sl2Lower,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hhL : h ∈ longSub 6 (hexGroup (twistedX σ)) := slLong_HSL_mem_longSub hσ s
  have R := d4RGD2 σ hσ
  have hn : GoodActEven 6 (hexGroup (twistedX σ)) (nHat σ (ng 1))⁻¹ :=
    (R.goodActEven_r₁ (by norm_num)).inv
  have hnL := conj_mem_longSub (by norm_num) (by norm_num) hn hhL
  have e : slShort σ hσ (HSL s') =
      (nHat σ (ng 1))⁻¹ * h * ((nHat σ (ng 1))⁻¹)⁻¹ * h⁻¹ := by
    rw [inv_inv]
    calc slShort σ hσ (HSL s') = (nHat σ (ng 1))⁻¹ * (nHat σ (ng 1) * slShort σ hσ (HSL s')) := by
          group
      _ = (nHat σ (ng 1))⁻¹ * (h * nHat σ (ng 1) * h⁻¹) := by rw [key]
      _ = _ := by group
  rw [e]
  exact (longSub 6 (hexGroup (twistedX σ))).mul_mem hnL
    ((longSub 6 (hexGroup (twistedX σ))).inv_mem hhL)

include hσ in
theorem mem_zpowers_of_central_longSub [Finite K] {v z : twistedGroup σ}
    (hvL : v ∈ longSub 6 (hexGroup (twistedX σ)))
    (hvc : ∀ l ∈ longSub 6 (hexGroup (twistedX σ)), v * l = l * v) (hv1 : v ≠ 1)
    (hzL : z ∈ longSub 6 (hexGroup (twistedX σ)))
    (hzc : ∀ l ∈ longSub 6 (hexGroup (twistedX σ)), z * l = l * z) :
    z ∈ Subgroup.zpowers v := by
  classical
  obtain ⟨ρ, hrange, hker⟩ := exists_sl3_range hσ
  have hq3 := SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl
  have hφker : (ρ.rangeRestrict).ker ≤ Subgroup.center SL(3, fixedField σ) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hcenter := center_eq_map_center_of_isQuasisimple hq3 ρ.rangeRestrict_surjective hφker
  have hscal : ∀ w ∈ longSub 6 (hexGroup (twistedX σ)),
      (∀ l ∈ longSub 6 (hexGroup (twistedX σ)), w * l = l * w) →
        ∃ g ∈ Subgroup.center SL(3, fixedField σ), ρ g = w := by
    intro w hw hwc
    have hwr : w ∈ ρ.range := by rw [hrange]; exact hw
    have hcw : (⟨w, hwr⟩ : ↥ρ.range) ∈ Subgroup.center ↥ρ.range := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg : (g : twistedGroup σ) ∈ longSub 6 (hexGroup (twistedX σ)) := by
        rw [← hrange]; exact g.2
      exact (hwc _ hg).symm
    rw [hcenter] at hcw
    obtain ⟨g, hg, hgw⟩ := hcw
    exact ⟨g, hg, congrArg Subtype.val hgw⟩
  obtain ⟨gv, hgv, rfl⟩ := hscal v hvL hvc
  obtain ⟨gz, hgz, rfl⟩ := hscal z hzL hzc
  obtain ⟨m, hm3, hmv⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hgv
  obtain ⟨l, hl3, hlz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hgz
  simp only [Fintype.card_fin] at hm3 hl3
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm3
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl3
  set mu := Units.mk0 m hm0 with hmu
  set lu := Units.mk0 l hl0 with hlu
  have hmu3 : mu ^ 3 = 1 := Units.ext (by simp [hmu, hm3])
  have hlu3 : lu ^ 3 = 1 := Units.ext (by simp [hlu, hl3])
  have hmu1 : mu ≠ 1 := by
    intro h
    apply hv1
    have hm1 : m = 1 := by
      have := congrArg Units.val h
      simpa [hmu] using this
    have hgv1 : gv = 1 := by
      apply Subtype.ext
      rw [← hmv, hm1]
      simp
    rw [hgv1, map_one]
  rcases CFSG.GH74.GLS.Stage2.Bender.Thm1.units_pow_three_eq_one_cases hmu3 hmu1 hlu3 with
    h | h | h
  · have hl1 : l = 1 := by
      have := congrArg Units.val h
      simpa [hlu] using this
    have hgz1 : gz = 1 := by
      apply Subtype.ext
      rw [← hlz, hl1]
      simp
    rw [hgz1, map_one]
    exact Subgroup.one_mem _
  · have hlm : l = m := by
      have := congrArg Units.val h
      simpa [hlu, hmu] using this
    have hgz : gz = gv := by
      apply Subtype.ext
      rw [← hlz, ← hmv, hlm]
    rw [hgz]
    exact Subgroup.mem_zpowers _
  · have hlm : l = m ^ 2 := by
      have := congrArg Units.val h
      simpa [hlu, hmu] using this
    have hgz : gz = gv ^ 2 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hlz, ← hmv, hlm, map_pow]
    rw [hgz, map_pow]
    exact Subgroup.npow_mem_zpowers _ 2

include hσ in
theorem exists_noncentral_three_longSub [Finite K] (ω : (fixedField σ)ˣ) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) :
    ∃ t ∈ longSub 6 (hexGroup (twistedX σ)), t ^ 3 = 1 ∧
      ∃ l ∈ longSub 6 (hexGroup (twistedX σ)), t * l ≠ l * t := by
  classical
  obtain ⟨ρ, hrange, hker⟩ := exists_sl3_range hσ
  have hq3 := SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl
  have hφker : (ρ.rangeRestrict).ker ≤ Subgroup.center SL(3, fixedField σ) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hcenter := center_eq_map_center_of_isQuasisimple hq3 ρ.rangeRestrict_surjective hφker
  have hω0 : ((ω : fixedField σ)) ≠ 0 := ω.ne_zero
  let D : SL(3, fixedField σ) :=
    ⟨Matrix.diagonal ![(ω : fixedField σ), ((ω⁻¹ : (fixedField σ)ˣ) : fixedField σ), 1], by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp⟩
  have hDL : ρ D ∈ longSub 6 (hexGroup (twistedX σ)) := by rw [← hrange]; exact ⟨D, rfl⟩
  refine ⟨ρ D, hDL, ?_, ?_⟩
  · rw [← map_pow]
    have : D ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow]
      show (Matrix.diagonal ![(ω : fixedField σ), ((ω⁻¹ : (fixedField σ)ˣ) : fixedField σ), 1]) ^ 3 = 1
      rw [Matrix.diagonal_pow]
      have h1 : ((ω : fixedField σ)) ^ 3 = 1 := by
        have := congrArg Units.val hω3
        simpa using this
      have h2 : (((ω⁻¹ : (fixedField σ)ˣ) : fixedField σ)) ^ 3 = 1 := by
        have := congrArg Units.val (show ω⁻¹ ^ 3 = 1 by rw [inv_pow, hω3, inv_one])
        simpa using this
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h1]
    rw [this, map_one]
  · by_contra hall
    push Not at hall
    have hDr : ρ D ∈ ρ.range := ⟨D, rfl⟩
    have hcD : (⟨ρ D, hDr⟩ : ↥ρ.range) ∈ Subgroup.center ↥ρ.range := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg : (g : twistedGroup σ) ∈ longSub 6 (hexGroup (twistedX σ)) := by
        rw [← hrange]; exact g.2
      exact (hall _ hg).symm
    rw [hcenter] at hcD
    obtain ⟨g, hg, hgD⟩ := hcD
    have hgD' : ρ g = ρ D := congrArg Subtype.val hgD
    have hk : D * g⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgD', mul_inv_cancel]
    have hDc : D ∈ Subgroup.center SL(3, fixedField σ) := by
      have := Subgroup.mul_mem _ (hker hk) hg
      rwa [inv_mul_cancel_right] at this
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hDc
    have h00 := congrFun (congrFun hr 0) 0
    have h22 := congrFun (congrFun hr 2) 2
    simp [D, Matrix.scalar_apply] at h00 h22
    apply hω1
    apply Units.ext
    rw [← h00, h22]
    rfl

theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (hne : H ≠ K) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK
  have hpos : 0 < Nat.card H := Nat.card_pos (α := ↥H)
  have hposK : 0 < Nat.card K := Nat.card_pos (α := ↥K)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [hm, mul_one]))
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have h2m : 2 ≤ m := by omega
  calc 2 * Nat.card H ≤ m * Nat.card H := Nat.mul_le_mul_right (Nat.card H) h2m
    _ = Nat.card K := by rw [hm, mul_comm]

theorem isElemAbelian_closure_of_commute {G : Type*} [Group G] {p : ℕ} {S : Set G}
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hp : ∀ a ∈ S, a ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.closure S) := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (hle hb) a ha)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy hx' hy' =>
    rw [(Commute.mul_pow (show Commute x y from hcomm x hx y hy)), hx', hy', one_mul]
  | inv x _ hx' => rw [inv_pow, hx', inv_one]

include hσ in
theorem exists_mem_centralizer_not_normalizer_three [Finite K]
    (hcen : Subgroup.center (twistedGroup σ) = ⊥) (ω : (fixedField σ)ˣ) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1)
    (hrank : ∀ F : Subgroup (twistedGroup σ), CFSG.Open.IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2)
    {x : twistedGroup σ}
    (hxv : x * slShort σ hσ (HSL (Units.map (fixedField σ).subtype.toMonoidHom (ω ^ 2))) =
      slShort σ hσ (HSL (Units.map (fixedField σ).subtype.toMonoidHom (ω ^ 2))) * x)
    (hx3 : x ^ 3 = 1)
    (hxz : x ∉ Subgroup.zpowers
      (slShort σ hσ (HSL (Units.map (fixedField σ).subtype.toMonoidHom (ω ^ 2)))))
    (hperf : ⁅⁅Subgroup.centralizer ({x} : Set (twistedGroup σ)),
        Subgroup.centralizer ({x} : Set (twistedGroup σ))⁆,
      ⁅Subgroup.centralizer ({x} : Set (twistedGroup σ)),
        Subgroup.centralizer ({x} : Set (twistedGroup σ))⁆⁆ =
      ⁅Subgroup.centralizer ({x} : Set (twistedGroup σ)),
        Subgroup.centralizer ({x} : Set (twistedGroup σ))⁆)
    (hcard : Nat.card SL(3, fixedField σ) ≤
      Nat.card ↥⁅Subgroup.centralizer ({x} : Set (twistedGroup σ)),
        Subgroup.centralizer ({x} : Set (twistedGroup σ))⁆) :
    ∃ y ∈ Subgroup.centralizer ({x} : Set (twistedGroup σ)),
      y ∉ Subgroup.normalizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)) := by
  classical
  set L := longSub 6 (hexGroup (twistedX σ)) with hLdef
  set C := Subgroup.centralizer ({x} : Set (twistedGroup σ)) with hCdef
  set R := ⁅C, C⁆ with hRdef
  set s : (fixedField σ)ˣ := ω ^ 2 with hs
  set t : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom s with ht
  set v := slShort σ hσ (HSL t) with hv
  have hω3K : ((ω : fixedField σ) : K) ^ 3 = 1 := by
    have := congrArg (fun u : (fixedField σ)ˣ => ((u : fixedField σ) : K)) hω3
    simpa using this
  have hω1K : ((ω : fixedField σ) : K) ≠ 1 := by
    intro h
    apply hω1
    apply Units.ext
    apply Subtype.ext
    simpa using h
  have htK : (t : K) = ((ω : fixedField σ) : K) ^ 2 := by simp [ht, hs]
  have hσt : σ (t : K) = t := by
    rw [htK, map_pow]
    congr 1
    exact (ω : fixedField σ).2
  have hnorm : (t : K) * σ t * σ (σ t) = 1 := by
    rw [hσt, hσt, htK]
    calc ((ω : fixedField σ) : K) ^ 2 * ((ω : fixedField σ) : K) ^ 2 *
          ((ω : fixedField σ) : K) ^ 2 = (((ω : fixedField σ) : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3K, one_pow]
  have ht2 : (t : K) ^ 2 ≠ 1 := by
    rw [htK]
    intro h
    apply hω1K
    calc ((ω : fixedField σ) : K) = ((ω : fixedField σ) : K) ^ 3 * ((ω : fixedField σ) : K) := by
          rw [hω3K, one_mul]
      _ = (((ω : fixedField σ) : K) ^ 2) ^ 2 := by ring
      _ = 1 := h
  have hvL : v ∈ L := slShort_HSL_fixed_mem_longSub hσ s
  have hLv : L ≤ Subgroup.centralizer ({v} : Set (twistedGroup σ)) :=
    longSub_le_centralizer_slShort_HSL hσ t hnorm
  have hvc : ∀ l ∈ L, v * l = l * v := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLv hl)).symm
  have hv1 : v ≠ 1 := by
    intro h
    have h1 := slShort_HSL_fix_d4X_zero hσ t ht2 (1 : K)
      (by rw [show slShort σ hσ (HSL t) = 1 from h]; simp)
    have h2 : d4X hσ 0 (1 : K) = d4X hσ 0 (0 : K) := h1.trans (d4X_zero_zero hσ).symm
    have h3 : (1 : K) = 0 := d4X_injective hσ 0 h2
    exact one_ne_zero h3
  have hv3 : v ^ 3 = 1 := by
    have ht3 : t ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, htK]
      calc (((ω : fixedField σ) : K) ^ 2) ^ 3 = (((ω : fixedField σ) : K) ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hω3K, one_pow]
        _ = ((1 : Kˣ) : K) := rfl
    rw [hv, ← map_pow, CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_pow, ht3,
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_one', map_one]
  by_contra hall
  push Not at hall
  have hRC : R ≤ C := by
    rw [hRdef, Subgroup.commutator_le]
    intro a ha b hb
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
  have hRN : ∀ y ∈ R, y ∈ Subgroup.normalizer (L : Set (twistedGroup σ)) := fun y hy =>
    hall y (hRC hy)
  have hconjv : ∀ y ∈ R, y * v * y⁻¹ ∈ Subgroup.zpowers v := by
    intro y hy
    have hyN := Subgroup.mem_normalizer_iff.1 (hRN y hy)
    have hyvL : y * v * y⁻¹ ∈ L := (hyN v).1 hvL
    refine mem_zpowers_of_central_longSub hσ hvL hvc hv1 hyvL ?_
    intro l hl
    have hl' : y⁻¹ * l * y⁻¹⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hRN y hy)) l).1 hl
      exact this
    have hc := hvc _ hl'
    rw [inv_inv] at hc
    calc y * v * y⁻¹ * l = y * (v * (y⁻¹ * l * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * l * y) * v) * y⁻¹ := by rw [hc]
      _ = l * (y * v * y⁻¹) := by group
  have hRnv : R ≤ Subgroup.normalizer (Subgroup.zpowers v : Set (twistedGroup σ)) := by
    intro y hy
    have fwd : ∀ y ∈ R, ∀ h ∈ Subgroup.zpowers v, y * h * y⁻¹ ∈ Subgroup.zpowers v := by
      intro y hy h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ (hconjv y hy) k
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fwd y hy h
    · intro hh
      have := fwd y⁻¹ (R.inv_mem hy) _ hh
      rwa [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at this
  have hRv : R ≤ Subgroup.centralizer ({v} : Set (twistedGroup σ)) :=
    (le_centralizer_of_perfect_of_le_normalizer hperf hRnv).trans
      (Subgroup.centralizer_le (by
        rintro _ rfl
        exact Subgroup.mem_zpowers v))
  have hRL : R ≤ L := perfect_le_longSub_of_le_centralizer hσ hcen t hnorm ht2 hperf hRv
  obtain ⟨ρ, hrange, -⟩ := exists_sl3_range hσ
  have hLcard : Nat.card L ≤ Nat.card SL(3, fixedField σ) := by
    rw [show L = ρ.range from hrange.symm]
    exact Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hRL' : R = L := Subgroup.eq_of_le_of_card_ge hRL (hLcard.trans hcard)
  have hLx : L ≤ C := hRL' ▸ hRC
  have hxL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)).symm
  obtain ⟨t₀, ht₀L, ht₀3, l₀, hl₀L, ht₀l⟩ := exists_noncentral_three_longSub hσ ω hω3 hω1
  set S : Set (twistedGroup σ) := {v, x, t₀} with hS
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    have hvx : v * x = x * v := hxv.symm
    have hvt : v * t₀ = t₀ * v := hvc t₀ ht₀L
    have hxt : x * t₀ = t₀ * x := hxL t₀ ht₀L
    rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;>
      first | rfl | exact hvx | exact hvx.symm | exact hvt | exact hvt.symm | exact hxt |
        exact hxt.symm
  have hSp : ∀ a ∈ S, a ^ 3 = 1 := by
    rintro a (rfl | rfl | rfl)
    · exact hv3
    · exact hx3
    · exact ht₀3
  have hFab := isElemAbelian_closure_of_commute hScomm hSp
  have hvord : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hzcard : Nat.card (Subgroup.zpowers v) = 3 := by rw [Nat.card_zpowers, hvord]
  set M := Subgroup.closure ({v, x} : Set (twistedGroup σ)) with hM
  have hzM : Subgroup.zpowers v ≤ M :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hxM : x ∈ M := Subgroup.subset_closure (by simp)
  have hzM' : Subgroup.zpowers v ≠ M := fun h => hxz (h ▸ hxM)
  have hMF : M ≤ Subgroup.closure S := Subgroup.closure_mono (by
    intro a ha
    rcases ha with rfl | rfl
    · simp [hS]
    · simp [hS])
  have hMcent : M ≤ Subgroup.centralizer (L : Set (twistedGroup σ)) := by
    rw [hM, Subgroup.closure_le]
    rintro a (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.2 fun l hl => (hvc l hl).symm
    · exact Subgroup.mem_centralizer_iff.2 fun l hl => (hxL l hl).symm
  have ht₀F : t₀ ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hMF' : M ≠ Subgroup.closure S := by
    intro h
    have ht₀M : t₀ ∈ M := h ▸ ht₀F
    exact ht₀l (Subgroup.mem_centralizer_iff.1 (hMcent ht₀M) l₀ hl₀L).symm
  have h1 := two_mul_card_le_of_lt hzM hzM'
  have h2 := two_mul_card_le_of_lt hMF hMF'
  have h3 := hrank _ hFab
  rw [hzcard] at h1
  omega

end Long

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
