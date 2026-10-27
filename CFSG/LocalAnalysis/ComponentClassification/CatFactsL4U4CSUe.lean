module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUh

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSU

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj HBlocks StabU DiagU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

section Transport

variable {X G : Type} [Group X] [Group G] {N : Subgroup G} [N.Normal] (e : ↥N ≃* X)

theorem actE_eq_conj {x : G} (hx : x ∈ N) : AZ.actE e x = MulAut.conj (e ⟨x, hx⟩) := by
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [AZ.actE_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem actE_comm_conj {g w : G} (hw : w ∈ N) (hgw : g * w = w * g) :
    AZ.actE e g * MulAut.conj (e ⟨w, hw⟩) = MulAut.conj (e ⟨w, hw⟩) * AZ.actE e g := by
  have h1 : AZ.actE e g (e ⟨w, hw⟩) = e ⟨w, hw⟩ := by
    rw [AZ.actE_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    change g * w * g⁻¹ = w
    rw [hgw, mul_inv_cancel_right]
  rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv', h1]

omit [N.Normal] in
theorem normalizes_of_mem_normalizer' {J : Subgroup G} {c : G} (hcN : c ∈ N)
    (hcJ : c ∈ normalizer (J : Set G)) (y : X) :
    y ∈ (J.subgroupOf N).map e.toMonoidHom ↔
      e ⟨c, hcN⟩ * y * (e ⟨c, hcN⟩)⁻¹ ∈ (J.subgroupOf N).map e.toMonoidHom := by
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [← map_inv, ← map_mul, ← map_mul]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := e.injective hwz
    subst hwz'
    refine ⟨_, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hw ⊢
    exact (mem_normalizer_iff.mp hcJ _).mp hw
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = ⟨c, hcN⟩ * z * (⟨c, hcN⟩)⁻¹ := e.injective hwz
    subst hwz'
    refine ⟨z, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hw ⊢
    exact (mem_normalizer_iff.mp hcJ _).mpr hw

omit [N.Normal] in
theorem mem_normalizer_of_normalizes' {J : Subgroup G} (hJN : J ≤ N) {w : G} (hwN : w ∈ N)
    (hw : ∀ y, y ∈ (J.subgroupOf N).map e.toMonoidHom ↔
      e ⟨w, hwN⟩ * y * (e ⟨w, hwN⟩)⁻¹ ∈ (J.subgroupOf N).map e.toMonoidHom) :
    w ∈ normalizer (J : Set G) := by
  rw [mem_normalizer_iff]
  intro j
  have hmem : ∀ z : ↥N, (z : G) ∈ J ↔ e z ∈ (J.subgroupOf N).map e.toMonoidHom := by
    intro z
    constructor
    · intro hz
      exact ⟨z, mem_subgroupOf.mpr hz, rfl⟩
    · rintro ⟨z', hz', hzz⟩
      have : z' = z := e.injective hzz
      rw [← this]
      exact mem_subgroupOf.mp hz'
  constructor
  · intro hj
    have hjN := hJN hj
    have h1 := (hw (e ⟨j, hjN⟩)).1 ((hmem ⟨j, hjN⟩).1 hj)
    rw [← map_inv, ← map_mul, ← map_mul, ← hmem] at h1
    exact h1
  · intro hj
    have hjN : j ∈ N := by
      have h2 : w * j * w⁻¹ ∈ N := hJN hj
      have e2 : j = w⁻¹ * (w * j * w⁻¹) * w := by group
      rw [e2]
      exact mul_mem (mul_mem (inv_mem hwN) h2) hwN
    have h1 : e (⟨w, hwN⟩ * ⟨j, hjN⟩ * (⟨w, hwN⟩)⁻¹) ∈ (J.subgroupOf N).map e.toMonoidHom :=
      (hmem _).1 hj
    rw [map_mul, map_mul, map_inv, ← hw] at h1
    exact (hmem _).2 h1

end Transport

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem bar_sq_of_order_eight (hq : p ^ f % 4 = 1) {ζ : K} (hζ : ζ ^ 8 = 1) :
    h.bar ζ ^ 2 = ζ ^ 2 := by
  rw [h.bar_apply, ← pow_mul]
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  rw [hk, show (4 * k + 1) * 2 = 8 * k + 2 by ring, pow_add, pow_mul, hζ, one_pow, one_mul]

theorem bar_ne_zero {ζ : K} (hζ : ζ ≠ 0) : h.bar ζ ≠ 0 := by
  intro h0
  have := congrArg h.bar h0
  rw [h.bar_bar, map_zero] at this
  exact hζ this

theorem tU_unitary {ζ : K} (hζ : ζ ≠ 0) :
    uStar h (blk ζ 0 0 (h.bar ζ)⁻¹) * stdG * blk ζ 0 0 (h.bar ζ)⁻¹ = stdG :=
  unitary_blk h (mul_inv_cancel₀ (bar_ne_zero h hζ))

theorem tU_det (hq : p ^ f % 4 = 1) {ζ : K} (hζ : ζ ^ 8 = 1) (hζ4 : ζ ^ 4 = -1) :
    (blk ζ 0 0 (h.bar ζ)⁻¹).det = 1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ
  rw [det_blk, inv_pow, bar_sq_of_order_eight h hq hζ, mul_inv_cancel₀ (pow_ne_zero 2 hζ0)]

@[expose] noncomputable def tU (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {ζ : K} (hζ : ζ ^ 8 = 1) (hζ4 : ζ ^ 4 = -1) : unitarySU p f K 4 :=
  hypSU h P hP (blk ζ 0 0 (h.bar ζ)⁻¹)
    (tU_unitary h (by rintro rfl; norm_num at hζ)) (tU_det h hq hζ hζ4)

theorem cP_tU (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {ζ : K} (hζ : ζ ^ 8 = 1) (hζ4 : ζ ^ 4 = -1) :
    cP P (tU h hq P hP hζ hζ4) = blk ζ 0 0 (h.bar ζ)⁻¹ := cP_hypSU h P hP _ _ _

theorem thU_tU_sq_ne_one (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {ζ : K} (hζ : ζ ^ 8 = 1) (hζ4 : ζ ^ 4 = -1) :
    thU p f K (tU h hq P hP hζ hζ4) ^ 2 ≠ 1 := by
  intro h1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, hc⟩ := val_of_mem_scal h1
  have hcP : cP P (tU h hq P hP hζ hζ4 ^ 2) = (c : K) • 1 := by
    rw [cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  rw [sq, cP_mul, cP_tU, blk_mul_blk] at hcP
  have e0 := congrFun (congrFun hcP 0) 0
  have e2 := congrFun (congrFun hcP 2) 2
  simp [blk] at e0 e2
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ
  have hb : h.bar ζ ^ 2 = ζ ^ 2 := bar_sq_of_order_eight h hq hζ
  have hb0 := bar_ne_zero h hζ0
  have h3 : ζ * ζ = (h.bar ζ)⁻¹ * (h.bar ζ)⁻¹ := by rw [e0, e2]
  have h4 : (ζ * ζ) * (h.bar ζ * h.bar ζ) = 1 := by
    rw [h3]
    field_simp
  rw [← sq, ← sq, hb, ← pow_add] at h4
  rw [show (2 + 2 : ℕ) = 4 by rfl, hζ4] at h4
  exact two_ne_zero_of_odd h hp2 (by linear_combination -h4)

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
