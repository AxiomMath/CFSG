module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OCU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem innU_or_fixed (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (h1 : α (thU p f K (uU h P hP 1)) = thU p f K (uU h P hP 1))
    (h2 : α (thU p f K (uL h P hP 1)) = thU p f K (uL h P hP 1))
    (h3 : α (thU p f K (uU h P hP μ)) = thU p f K (uU h P hP μ)) :
    α ∈ InnU p f K h ∨
      ∃ g : unitarySU p f K 4, α (thU p f K g) = thU p f K g ∧
        ∃ β γ : K, β ≠ 0 ∧ cP P g = gfix β γ := by
  classical
  have : Finite K := h.finite
  have hker : (thU p f K).ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2
    (d := 4) (by norm_num) (thU p f K) thU_surjective hker α
  obtain ⟨x, b, e, y, hblk, hun, hcase⟩ := blk_of_fix h hp2 P hP hμ hAu hlift h1 h2 h3
  rcases hcase with ⟨rfl, -, -⟩ | ⟨hφb, hx, hy⟩
  · left
    refine ⟨A, (mem_uMat h).2 hAu, fun g g' hg => ?_⟩
    rw [← hlift g]
    congr 1
    apply Subtype.ext
    rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, glAut_refl, hg]
  right
  subst hx hy
  rw [map_zero, zero_mul, add_zero] at hun
  have hμb := bar_ne_of_generator h hμ
  set β : K := μ - h.bar μ with hβdef
  set γ : K := -(β * e * h.bar e) with hγdef
  have hβ0 : β ≠ 0 := sub_ne_zero.2 (Ne.symm hμb)
  have hββ : β + h.bar β = 0 := by
    rw [hβdef, map_sub, h.bar_bar]
    ring
  have hγγ : γ + h.bar γ = 0 := by
    rw [hγdef, map_neg, map_mul, map_mul, h.bar_bar]
    linear_combination (-(e * h.bar e)) * hββ
  have hc1 : b * h.bar γ = β * e := by
    rw [hγdef, map_neg, map_mul, map_mul, h.bar_bar]
    linear_combination (-(h.bar β * e)) * hun - e * hββ
  have hc2 : b * γ = h.bar β * e := by
    rw [hγdef]
    linear_combination (-(β * e)) * hun - e * hββ
  refine ⟨hypSU h P hP (gfix β γ) (unitary_gfix h hββ hγγ) (det_gfix β γ), ?_, β, γ, hβ0,
    cP_hypSU h P hP _ _ _⟩
  rw [← hlift]
  congr 1
  apply Subtype.ext
  rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom]
  change A * glAut φ (P * toGL (gfix β γ) (det_gfix β γ) * P⁻¹) * A⁻¹ =
    P * toGL (gfix β γ) (det_gfix β γ) * P⁻¹
  obtain ⟨T, hT⟩ : ∃ X : GL (Fin 4) K, X = toGL (gfix β γ) (det_gfix β γ) := ⟨_, rfl⟩
  rw [← hT]
  obtain ⟨A', hA'⟩ : ∃ X : GL (Fin 4) K, X = P⁻¹ * A * glAut φ P := ⟨_, rfl⟩
  rw [← hA'] at hblk
  have hAT : A' * glAut φ T = T * A' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, hT, coe_toGL, hblk]
    have e' : (gfix β γ).map φ = gfix (h.bar β) (h.bar γ) := by
      rw [← hφb β, ← hφb γ]
      exact map_gfix' (φ : K →+* K) β γ
    rw [e']
    exact blk_mul_gfix h hc1 hc2
  have hAP : A * glAut φ P = P * A' := by
    rw [hA']
    group
  calc A * glAut φ (P * T * P⁻¹) * A⁻¹ =
      (A * glAut φ P) * glAut φ T * (A * glAut φ P)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
    _ = P * A' * glAut φ T * (P * A')⁻¹ := by rw [hAP]
    _ = P * (A' * glAut φ T) * A'⁻¹ * P⁻¹ := by group
    _ = P * T * P⁻¹ := by
        rw [hAT]
        group

include h in
theorem eq_of_thU_eq (hp2 : p ≠ 2) {w w' : unitarySU p f K 4} (hw : w ^ p = 1)
    (hw' : w' ^ p = 1) (he : thU p f K w' = thU p f K w) : w' = w := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at he
  have hzc := mem_center_of_mem_scal he
  set c := w'⁻¹ * w with hc
  have hcomm : Commute w' c := Subgroup.mem_center_iff.mp hzc w'
  have hwc : w = w' * c := by rw [hc, mul_inv_cancel_left]
  have hcp : c ^ p = 1 := by
    have e1 := congrArg (· ^ p) hwc
    rw [hcomm.mul_pow, hw, hw', one_mul] at e1
    exact e1.symm
  have hc1 := eq_one_of_pow_odd (h.prime.odd_of_ne_two hp2) hcp (pow_four_eq_one_of_mem_scal h he)
  rw [hwc, hc1, mul_one]

include h in
theorem not_mem_normalizer_diag (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} {z : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hz : IsCU h A z) (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) {μ : K}
    (hμb : h.bar μ ≠ μ) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJz : ∀ x ∈ J', z x = x) (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J')
    (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J') {g : unitarySU p f K 4} {β γ : K}
    (hβ : β ≠ 0) (hg : cP P g = gfix β γ) :
    thU p f K g ∉ Subgroup.normalizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
  intro hN
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hcomm : ∀ u : unitarySU p f K 4, thU p f K u ∈ J' → u ^ p = 1 →
      A * ((g⁻¹ * u * g : unitarySU p f K 4) : GL (Fin 4) K) =
        ((g⁻¹ * u * g : unitarySU p f K 4) : GL (Fin 4) K) * A := by
    intro u hu hup
    set w := g⁻¹ * u * g with hw
    have hwp : w ^ p = 1 := by
      have e : w = g⁻¹ * u * g⁻¹⁻¹ := by rw [hw, inv_inv]
      rw [e, conj_pow, hup, mul_one, mul_inv_cancel]
    have hwJ : thU p f K w ∈ J' := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) (thU p f K u)).mp hu
      have e1 : thU p f K w = (thU p f K g)⁻¹ * thU p f K u * (thU p f K g)⁻¹⁻¹ := by
        rw [inv_inv, hw, map_mul, map_mul, map_inv]
      rw [e1]
      exact h1
    have hfx := hJz _ hwJ
    rw [hz.apply h] at hfx
    set w' : unitarySU p f K 4 := ⟨_, conj_mem_SU h hz.1 w⟩ with hw'
    have hw'p : w' ^ p = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, hw']
      change (A * (w : GL (Fin 4) K) * A⁻¹) ^ p = 1
      rw [conj_pow, ← SubgroupClass.coe_pow, hwp, OneMemClass.coe_one, mul_one, mul_inv_cancel]
    have hee := eq_of_thU_eq h hp2 hwp hw'p hfx
    have e2 : A * (w : GL (Fin 4) K) * A⁻¹ = w := congrArg Subtype.val hee
    calc A * (w : GL (Fin 4) K) = A * (w : GL (Fin 4) K) * A⁻¹ * A := by group
      _ = (w : GL (Fin 4) K) * A := by rw [e2]
  set Yg : GL (Fin 4) K := (g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ with hYg
  have hcPu : ∀ u : unitarySU p f K 4,
      cP P u = ((P⁻¹ * (u : GL (Fin 4) K) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro u
    rw [cP, Units.val_mul, Units.val_mul]
  have hYc : ∀ u : unitarySU p f K 4, thU p f K u ∈ J' → u ^ p = 1 →
      ((P⁻¹ * Yg * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cP P u =
        cP P u * ((P⁻¹ * Yg * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro u hu hup
    have h1 := hcomm u hu hup
    have e : ((g⁻¹ * u * g : unitarySU p f K 4) : GL (Fin 4) K) =
        (g : GL (Fin 4) K)⁻¹ * u * g := rfl
    rw [e] at h1
    have h2 : Yg * (u : GL (Fin 4) K) = (u : GL (Fin 4) K) * Yg := by
      calc Yg * (u : GL (Fin 4) K) =
          (g : GL (Fin 4) K) * (A * ((g : GL (Fin 4) K)⁻¹ * u * g)) * (g : GL (Fin 4) K)⁻¹ := by
            rw [hYg]
            group
        _ = (g : GL (Fin 4) K) * (((g : GL (Fin 4) K)⁻¹ * u * g) * A) *
            (g : GL (Fin 4) K)⁻¹ := by rw [h1]
        _ = (u : GL (Fin 4) K) * Yg := by
            rw [hYg]
            group
    have h3 : (P⁻¹ * Yg * P) * (P⁻¹ * (u : GL (Fin 4) K) * P) =
        (P⁻¹ * (u : GL (Fin 4) K) * P) * (P⁻¹ * Yg * P) := by
      calc (P⁻¹ * Yg * P) * (P⁻¹ * (u : GL (Fin 4) K) * P) = P⁻¹ * (Yg * u) * P := by group
        _ = P⁻¹ * (u * Yg) * P := by rw [h2]
        _ = _ := by group
    rw [hcPu, ← Units.val_mul, ← Units.val_mul, h3]
  have m1 := hYc _ (hJU 1) (uU_pow_char h P hP 1)
  have m2 := hYc _ (hJL 1) (uL_pow_char h P hP 1)
  have m3 := hYc _ (hJU μ) (uU_pow_char h P hP μ)
  rw [cP_uU] at m1 m3
  rw [cP_uL] at m2
  have hW := eq_blk_diag_of_comm h hμb m1 m2 m3
  have hPA : ((P⁻¹ * A * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hE : ((P⁻¹ * Yg * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cP P g =
      cP P g * ((P⁻¹ * A * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hcPu, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hYg]
    group
  rw [hg, hPA, hW] at hE
  exact hβ (eq_zero_of_blk_mul_gfix h2K hl0 hE)

theorem det_X1' (l : K) : (X1 l).det = l ^ 4 := by
  rw [CSU.X1_eq_blk, det_blk]
  ring

include h in
theorem exists_conj_of_mod_four (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    {l : K} (hbl : h.bar l * l = -1) {A : GL (Fin 4) K}
    {z : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hz : IsCU h A z)
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) :
    ∃ Y : unitarySU p f K 4, z = MulAut.conj (thU p f K Y) := by
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one h hp2
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbl
    exact zero_ne_one (neg_eq_zero.1 hbl.symm).symm
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hi
    exact one_ne_zero (by linear_combination hi : (1 : K) = 0)
  have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hi]; norm_num
  have hbi : h.bar i = i := by
    rw [h.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
    rw [hk, pow_succ, pow_mul, hi4, one_pow, one_mul]
  set c : K := i * l⁻¹ with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero hi0 (inv_ne_zero hl0)
  have hcN : h.bar c * c = 1 := by
    have hbl' : h.bar l = -l⁻¹ := by
      field_simp
      linear_combination hbl
    rw [hcdef, map_mul, map_inv₀, hbi, hbl', inv_neg, inv_inv]
    field_simp
    linear_combination -hi
  set B : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc0) * A with hB
  have hBm : (B : Matrix (Fin 4) (Fin 4) K) = c • (A : Matrix (Fin 4) (Fin 4) K) := by
    rw [hB, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hAu : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1 :=
    (mem_uMat h).1 hz.1
  have hBu : ((B : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (B : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hBm]
    have e : (c • (A : Matrix (Fin 4) (Fin 4) K)).map h.bar =
        h.bar c • (A : Matrix (Fin 4) (Fin 4) K).map h.bar := by
      ext i j
      simp
    rw [e, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAu, smul_smul, hcN,
      one_smul]
  have hdetA : (A : Matrix (Fin 4) (Fin 4) K).det = l ^ 4 := by
    have h1 := congrArg Matrix.det hAP
    rw [Matrix.det_mul, Matrix.det_mul, det_X1'] at h1
    have hP0 : (P : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
    have h2 := mul_right_cancel₀ hP0 (h1.trans (mul_comm _ _))
    exact h2
  have hBdet : (B : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [hBm, Matrix.det_smul, Fintype.card_fin, hdetA, hcdef, mul_pow, inv_pow, hi4, one_mul,
      inv_mul_cancel₀ (pow_ne_zero 4 hl0)]
  have hBSU : B ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).2 ⟨hBdet, hBu⟩
  have hzB : IsCU h B z := hz.of_eq_smul h ((mem_uMat h).2 hBu) hBm
  exact ⟨⟨B, hBSU⟩, hzB.eq_conj h hBSU⟩

end OCU

end CFSG.ComponentClassification.CatFactsL4U4
