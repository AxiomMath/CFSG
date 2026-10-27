module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TU4Block
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank TBlocks
  Subgroup CFSG.ComponentClassification.GSThmB
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem det_jj : (jj : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [jj, Matrix.det_fin_two]

theorem real_of_unitary_det {a : Matrix (Fin 2) (Fin 2) K}
    (ha : (a.map h.bar)ᵀ * jj * a = jj) (hd : a.det = 1) : a.map h.bar = a := by
  have h1 : aᵀ * jj * a = jj := by rw [transpose_mul_jj_mul, hd, one_smul]
  have hN : IsUnit (jj * a).det := by
    rw [det_mul, det_jj, hd, one_mul]
    exact isUnit_one
  have h2 : (a.map h.bar)ᵀ * (jj * a) = aᵀ * (jj * a) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ha, h1]
  have h3 : (a.map h.bar)ᵀ = aᵀ := by
    calc (a.map h.bar)ᵀ = (a.map h.bar)ᵀ * ((jj * a) * (jj * a)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
      _ = aᵀ * ((jj * a) * (jj * a)⁻¹) := by rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
      _ = aᵀ := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
  have := congrArg Matrix.transpose h3
  rwa [Matrix.transpose_transpose, Matrix.transpose_transpose] at this

@[expose] noncomputable def toFix (a : Matrix (Fin 2) (Fin 2) K) (ha : a.map h.bar = a) :
    Matrix (Fin 2) (Fin 2) h.fixedField :=
  Matrix.of fun i j => ⟨a i j, h.mem_fixedField.2 (by
    have := congrFun (congrFun ha i) j
    rwa [Matrix.map_apply] at this)⟩

theorem map_toFix (a : Matrix (Fin 2) (Fin 2) K) (ha : a.map h.bar = a) :
    (toFix h a ha).map h.fixedField.subtype = a := by
  ext i j
  rfl

theorem det_toFix (a : Matrix (Fin 2) (Fin 2) K) (ha : a.map h.bar = a) (hd : a.det = 1) :
    (toFix h a ha).det = 1 := by
  apply Subtype.ext
  have e : ((toFix h a ha).det : K) = ((toFix h a ha).map h.fixedField.subtype).det := by
    rw [show (toFix h a ha).map h.fixedField.subtype =
      h.fixedField.subtype.mapMatrix (toFix h a ha) from rfl, ← RingHom.map_det]
    rfl
  rw [e, map_toFix, hd]
  rfl

theorem uStar_bd (a b : Matrix (Fin 2) (Fin 2) K) :
    uStar h (bd a b) = bd ((a.map h.bar)ᵀ) ((b.map h.bar)ᵀ) := by
  rw [uStar, map_bd, transpose_bd]

theorem unitary_cP_bJ {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    (g : unitarySU p f K 4) : uStar h (cP R g) * bJ 1 1 * cP R g = bJ 1 1 := by
  have hg : uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := ((mem_unitarySU_iff h).1 g.2).2
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
      = 1 := by rw [← uStar_mul, hRR, uStar_one]
  have key : uStar h (cP R g) * (t • bJ 1 1) * cP R g = t • bJ 1 1 := by
    rw [← hR, cP, uStar_mul, uStar_mul]
    calc uStar h (R : Matrix (Fin 4) (Fin 4) K) *
          (uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (R : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (R : Matrix (Fin 4) (Fin 4) K) *
          (uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
            ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
            ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * (R : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRi, hRR, Matrix.mul_one, Matrix.mul_one, hg, Matrix.mul_one]
  rw [Matrix.mul_smul, Matrix.smul_mul] at key
  exact smul_right_injective _ ht0 key

theorem cP_X {R : GL (Fin 4) K} {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) : cP R X = X1 (1 : K) := by
  have hRR : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [cP, Matrix.mul_assoc, hXR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]

theorem blocks_unitary {M : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M)
    (hU : uStar h M * bJ 1 1 * M = bJ 1 1) :
    ((ul M).map h.bar)ᵀ * jj * ul M = jj ∧ ((lr M).map h.bar)ᵀ * jj * lr M = jj := by
  have e : bJ (1 : K) 1 = bd jj jj := by rw [← bd_eq_bJ, one_smul]
  rw [eq_bd hM, uStar_bd, e, bd_mul, bd_mul] at hU
  exact ⟨by simpa [ul_bd] using congrArg ul hU, by simpa [lr_bd] using congrArg lr hU⟩

include h in
theorem isBD_cP_of_comm (hp2 : p ≠ 2) {R : GL (Fin 4) K} {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    {c : unitarySU p f K 4} (hc : c * X = X * c) : IsBD (cP R c) := by
  have hm := congrArg (cP R) hc
  rw [cP_mul, cP_mul, cP_X hXR] at hm
  exact isBD_of_comm_X1 (two_ne_zero_of_odd h hp2) one_ne_zero hm

theorem mem_range_of_det_ul {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {c : unitarySU p f K 4} (hBD : IsBD (cP R c)) (hdu : (ul (cP R c)).det = 1) :
    c ∈ (bdHomU h hR).range := by
  have hRR' : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hd := det_cP h R c
  have hdl : (lr (cP R c)).det = 1 := by
    rw [det_of_isBD hBD, hdu, one_mul] at hd
    exact hd
  obtain ⟨hua, hub⟩ := blocks_unitary h hBD (unitary_cP_bJ h ht0 hR c)
  have hra := real_of_unitary_det h hua hdu
  have hrb := real_of_unitary_det h hub hdl
  refine ⟨(⟨toFix h _ hra, det_toFix h _ hra hdu⟩, ⟨toFix h _ hrb, det_toFix h _ hrb hdl⟩), ?_⟩
  apply ext_val
  rw [val_bdHomU, bdK]
  change (R : Matrix (Fin 4) (Fin 4) K) * bd ((toFix h _ hra).map h.fixedField.subtype)
    ((toFix h _ hrb).map h.fixedField.subtype) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = _
  rw [map_toFix, map_toFix, ← eq_bd hBD, cP]
  simp only [← Matrix.mul_assoc]
  rw [hRR', Matrix.one_mul, Matrix.mul_assoc, hRR', Matrix.mul_one]

include h in
@[expose] noncomputable def ulHom (hp2 : p ≠ 2) {R : GL (Fin 4) K} {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    centralizer ({X} : Set (unitarySU p f K 4)) →* Matrix (Fin 2) (Fin 2) K where
  toFun c := ul (cP R c.1)
  map_one' := by
    change ul (cP R 1) = 1
    rw [cP_one, ul_one]
  map_mul' := fun c d => by
    have hc := isBD_cP_of_comm h hp2 hXR (mem_centralizer_singleton_iff.mp c.2)
    have hd := isBD_cP_of_comm h hp2 hXR (mem_centralizer_singleton_iff.mp d.2)
    change ul (cP R (c.1 * d.1)) = ul (cP R c.1) * ul (cP R d.1)
    rw [cP_mul, ul_mul hc hd]

theorem ulHom_apply (hp2 : p ≠ 2) {R : GL (Fin 4) K} {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    (c : centralizer ({X} : Set (unitarySU p f K 4))) : ulHom h hp2 hXR c = ul (cP R c.1) := rfl

include h in
theorem exists_blockDetU (hp2 : p ≠ 2) {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    ∃ δ : centralizer ({X} : Set (unitarySU p f K 4)) →* Kˣ,
      ∀ c : centralizer ({X} : Set (unitarySU p f K 4)), δ c = 1 →
        (c : unitarySU p f K 4) ∈ (bdHomU h hR).range := by
  refine ⟨(Matrix.detMonoidHom.comp (ulHom h hp2 hXR)).toHomUnits, fun c hc => ?_⟩
  have h1 := congrArg Units.val hc
  rw [MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply, ulHom_apply] at h1
  have hdu : (ul (cP R c.1)).det = 1 := h1
  exact mem_range_of_det_ul h ht0 hR
    (isBD_cP_of_comm h hp2 hXR (mem_centralizer_singleton_iff.mp c.2)) hdu

include h in
theorem centralizerCore516_le_tU (hp2 : p ≠ 2) (hq3 : p ^ f ≠ 3) {R : GL (Fin 4) K} {t : K}
    (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    centralizerCore516 (p ^ f) (QuotientGroup.mk' (scal p f K) X) ≤
      ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range := by
  classical
  set θ := QuotientGroup.mk' (scal p f K) with hθ
  set CX := centralizer ({X} : Set (unitarySU p f K 4)) with hCX
  obtain ⟨δ, hδ⟩ := exists_blockDetU h hp2 ht0 hR hXR
  have hrange : (θ.comp (bdHomU h hR)).range = (bdHomU h hR).range.map θ := by
    rw [MonoidHom.range_comp]
  unfold centralizerCore516
  rw [ite_eq_right hq3]
  refine (Quasithin.perfectCore_le_derivedSeriesOf _ 2).trans ?_
  have hsc : scal p f K ≤ center (unitarySU p f K 4) := fun z hz => mem_center_of_mem_scal hz
  have hC1 : ⁅centralizer {θ X}, centralizer {θ X}⁆ ≤ CX.map θ := by
    rw [commutator_le]
    intro u hu v hv
    obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) u
    obtain ⟨V, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) v
    refine ⟨⁅U, V⁆, ?_, by rw [map_commutatorElement]⟩
    have hmem : ∀ Z : unitarySU p f K 4, θ Z ∈ centralizer {θ X} →
        Z * X * Z⁻¹ * X⁻¹ ∈ scal p f K := by
      intro Z hZ
      rw [mem_centralizer_singleton_iff] at hZ
      have h1 : θ (Z * X * Z⁻¹ * X⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hZ]
        group
      rwa [hθ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [SetLike.mem_coe, hCX, mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod hsc (hmem U hu) (hmem V hv)
  have hC2 : ⁅CX, CX⁆ ≤ (bdHomU h hR).range := by
    rw [commutator_le]
    intro a ha b hb
    have : δ ⁅(⟨a, ha⟩ : CX), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact hδ _ this
  rw [Quasithin.derivedSeriesOf_succ, Quasithin.derivedSeriesOf_succ,
    Quasithin.derivedSeriesOf_zero, hrange]
  calc ⁅⁅centralizer {θ X}, centralizer {θ X}⁆, ⁅centralizer {θ X}, centralizer {θ X}⁆⁆ ≤
      ⁅CX.map θ, CX.map θ⁆ := commutator_mono hC1 hC1
    _ = (⁅CX, CX⁆).map θ := (map_commutator _ _ _).symm
    _ ≤ (bdHomU h hR).range.map θ := map_mono hC2

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
