module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidFrame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Hyp

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

omit [CharP K 2] in
theorem eichM_zero_left (σ : K →+* K) (c : K) :
    eichM (ε := ε) σ 0 c = 1 + c • Matrix.single hE hF 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [eichM, one_apply, Fin.eq_zero]

theorem valid_zero {c : K} (hc : h.bar c = c) :
    c + h.bar c = ∑ k : Fin ε, h.bar ((0 : Fin ε → K) k) * (0 : Fin ε → K) k := by
  rw [hc, CharTwo.add_self_eq_zero]
  simp

@[expose] noncomputable def tz {c : K} (hc : h.bar c = c) : hypSU h 1 ε :=
  eich h (valid_zero (ε := ε) h hc)

theorem coe_tz {c : K} (hc : h.bar c = c) :
    (((tz (ε := ε) h hc : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
      Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = 1 + c • Matrix.single hE hF 1 := by
  rw [tz, coe_eich, eichM_zero_left]

theorem tz_mem_stabE {c : K} (hc : h.bar c = c) : tz (ε := ε) h hc ∈ stabE h :=
  eich_mem_stabE h _

theorem tz_mul_tz {c : K} (hc : h.bar c = c) : tz (ε := ε) h hc * tz h hc = 1 := by
  refine Subtype.ext (Units.ext ?_)
  change eichM h.bar 0 c * eichM h.bar 0 c = 1
  rw [eichM_mul]
  have h2 : c + c + ∑ k : Fin ε, h.bar ((0 : Fin ε → K) k) * (0 : Fin ε → K) k = 0 := by
    rw [CharTwo.add_self_eq_zero]
    simp
  rw [add_zero, h2, eichM_zero]

theorem stabE_le_centralizer_tz {c : K} (hc : h.bar c = c) :
    stabE h ≤ centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε)) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  have hker : (⟨tz h hc, tz_mem_stabE h hc⟩ : stabE (ε := ε) h) ∈ (zBlockHom h).ker :=
    (mem_ker_zBlockHom h _).mpr (eich_mem_eichSub h (valid_zero h hc))
  have hav : avec h (⟨tz h hc, tz_mem_stabE h hc⟩ : stabE (ε := ε) h) = 0 := by
    funext k
    simp [avec, smat, coe_tz, one_apply]
  have h1 := commute_of_avec_eq_zero h hker hav ⟨g, hg⟩
  exact (congrArg Subtype.val h1).symm

omit [CharP K 2] in
theorem mulVec_e_of_commute {c : K} (hc0 : c ≠ 0) {g : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K}
    (hg : g * (1 + c • Matrix.single hE hF 1) = (1 + c • Matrix.single hE hF 1) * g) :
    g *ᵥ Pi.single hE 1 = g hE hE • Pi.single hE 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul] at hg
  have h1 : g * Matrix.single hE hF 1 = Matrix.single hE hF 1 * g :=
    smul_right_injective _ hc0 (add_left_cancel hg)
  have h2 := congrArg (· *ᵥ (Pi.single hF (1 : K) : HypIndex 1 ε → K)) h1
  simp only [← mulVec_mulVec, single_mulVec_eq, Pi.single_eq_same, mul_one, one_mul,
    one_smul] at h2
  have h3 : g *ᵥ Pi.single hE 1 = (g *ᵥ Pi.single hF 1) hF • Pi.single hE 1 := h2
  have h4 : g hE hE = (g *ᵥ Pi.single hF 1) hF := by
    have := congrFun h3 hE
    rwa [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at this
  rw [h4]
  exact h3

end Hyp

section Core

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K) {c : K}
  (hc : h.bar c = c) (hc0 : c ≠ 0)
include hc0

theorem mulVec_e_of_mem_centralizer {g : hypSU h 1 ε}
    (hg : g ∈ centralizer ({tz h hc} : Set (hypSU h 1 ε))) :
    ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) *ᵥ Pi.single hE 1 =
      ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) hE hE •
        Pi.single hE 1 := by
  refine mulVec_e_of_commute hc0 ?_
  rw [mem_centralizer_singleton_iff] at hg
  have h1 := congrArg (fun x : hypSU h 1 ε =>
    ((x : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K)) hg
  simpa only [Subgroup.coe_mul, Units.val_mul, coe_tz] using h1

@[expose] noncomputable def eeHom :
    centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε)) →* K where
  toFun g := ((g : hypSU h 1 ε) : GL (HypIndex 1 ε) K).val hE hE
  map_one' := one_apply_eq _
  map_mul' g g' := by
    have hg' := mulVec_e_of_mem_centralizer h hc hc0 g'.2
    change (((g : hypSU h 1 ε) : GL (HypIndex 1 ε) K).val *
      ((g' : hypSU h 1 ε) : GL (HypIndex 1 ε) K).val) hE hE = _
    rw [Matrix.mul_apply, Finset.sum_eq_single hE]
    · intro l _ hl
      have h1 := congrFun hg' l
      rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_eq_of_ne hl, smul_zero] at h1
      rw [h1, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

theorem perfectCore_centralizer_tz (hf : 2 ≤ f) (hε : 2 ≤ ε) :
    perfectCore (centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε))) = stabE h := by
  apply le_antisymm
  · refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_
    change ⁅centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε)),
      centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε))⁆ ≤ stabE h
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    have hcm : ⁅g, g'⁆ ∈ centralizer ({tz h hc} : Set (hypSU h 1 ε)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    set s := eeHom (ε := ε) h hc hc0
    set x : centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε)) := ⟨g, hg⟩
    set y : centralizer ({tz (ε := ε) h hc} : Set (hypSU h 1 ε)) := ⟨g', hg'⟩
    have h1 : s x * s x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : s y * s y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h3 : s ⁅x, y⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul]
      calc s x * s y * s x⁻¹ * s y⁻¹ = (s x * s x⁻¹) * (s y * s y⁻¹) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    have h4 : (((⁅g, g'⁆ : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
        Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) hE hE = 1 := h3
    rw [mem_stabE, mulVec_e_of_mem_centralizer h hc hc0 hcm, h4, one_smul]
  · exact CFSG.Quasithin.le_perfectCore_of_perfect (stabE_le_centralizer_tz h hc)
      (le_antisymm (Subgroup.commutator_le_self _) (stabE_le_commutator h hf hε))

end Core

section Psi

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)
  {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K} (hR : IsHypTransport h R)

@[expose] noncomputable def psiU : stabE (ε := ε) h →* StatedProj (StatedSU (2 + ε) (2 ^ f) K) :=
  (uProj K (2 + ε) f).comp ((hypTransport h hR).toMonoidHom.comp (stabE h).subtype)

omit [CharP K 2] in
theorem psiU_apply (g : stabE (ε := ε) h) :
    psiU h hR g = uProj K (2 + ε) f (hypTransport h hR g) := rfl

omit [CharP K 2] in
theorem eq_one_of_scalar_mulVec {n : ℕ} {a : K} {v : Fin n → K} (hv : v ≠ 0)
    (h1 : Matrix.scalar (Fin n) a *ᵥ v = v) : a = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have h2 := congrFun h1 i
  simp only [scalar_apply, mulVec_diagonal] at h2
  exact (mul_eq_right₀ hi).mp h2

omit [CharP K 2] in
theorem psiU_injective : Function.Injective (psiU h hR) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : uProj K (2 + ε) f (hypTransport h hR g) = uProj K (2 + ε) f 1 := by
    rw [← psiU_apply, hg, map_one]
  obtain ⟨c, hc⟩ := uProj_eq_uProj_iff.mp hg'
  have h1 : GeneralLinearGroup.scalar (Fin (2 + ε)) c *
      ((hypTransport h hR g : StatedSU (2 + ε) (2 ^ f) K) : GL (Fin (2 + ε)) K) = 1 := by
    rw [← hc]
    rfl
  have hT := eq_inv_of_mul_eq_one_right h1
  have hfix := (mulVec_eq_iff_hypTransport h hR (g : hypSU h 1 ε) _).mp ((mem_stabE h).mp g.2)
  have hfix' : (((GeneralLinearGroup.scalar (Fin (2 + ε)) c)⁻¹ : GL (Fin (2 + ε)) K) :
      Matrix (Fin (2 + ε)) (Fin (2 + ε)) K) *ᵥ (R *ᵥ Pi.single hE 1) = R *ᵥ Pi.single hE 1 := by
    rw [← hT]
    exact hfix
  rw [← map_inv, GeneralLinearGroup.coe_scalar] at hfix'
  have hc1 := eq_one_of_scalar_mulVec (transport_col_ne_zero h hR) hfix'
  have hc2 : c⁻¹ = 1 := Units.ext hc1
  rw [← map_inv, hc2, map_one] at hT
  have h3 : hypTransport h hR g = 1 := Subtype.ext hT
  exact Subtype.ext ((MulEquiv.map_eq_one_iff _).mp h3)

end Psi

section Transfer

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)
  {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K} (hR : IsHypTransport h R)

omit [CharP K 2] in
theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (x : G) : (centralizer ({x} : Set G)).map φ.toMonoidHom = centralizer ({φ x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hz
    rw [mem_centralizer_singleton_iff]
    change φ z * φ x = φ x * φ z
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    rw [mem_centralizer_singleton_iff] at hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hy]

theorem centralizer_uProj_eq {n : ℕ} (hn : 1 ≤ n) {x : StatedSU n (2 ^ f) K} (hx : x * x = 1) :
    centralizer ({uProj K n f x} : Set (StatedProj (StatedSU n (2 ^ f) K))) =
      (centralizer ({x} : Set (StatedSU n (2 ^ f) K))).map (uProj K n f) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨g, rfl⟩ := uProj_surjective (K := K) (f := f) n z
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact commute_of_uProj_commute hn hx (mem_centralizer_singleton_iff.mp hz)
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]

omit [CharP K 2] in
theorem range_psiU :
    (psiU h hR).range = ((stabE (ε := ε) h).map (hypTransport h hR).toMonoidHom).map
      (uProj K (2 + ε) f) := by
  rw [psiU, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]

theorem perfectCore_centralizer_psiU [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) {c : K}
    (hc : h.bar c = c) (hc0 : c ≠ 0) :
    perfectCore (centralizer ({psiU h hR ⟨tz h hc, tz_mem_stabE h hc⟩} :
      Set (StatedProj (StatedSU (2 + ε) (2 ^ f) K)))) = (psiU h hR).range := by
  have hT : (hypTransport h hR (tz h hc) : StatedSU (2 + ε) (2 ^ f) K) *
      hypTransport h hR (tz h hc) = 1 := by
    rw [← map_mul, tz_mul_tz, map_one]
  have hC : centralizer ({(hypTransport h hR (tz h hc) : StatedSU (2 + ε) (2 ^ f) K)} :
      Set (StatedSU (2 + ε) (2 ^ f) K)) =
        (centralizer ({tz h hc} : Set (hypSU h 1 ε))).map (hypTransport h hR).toMonoidHom :=
    (map_centralizer_singleton_mulEquiv (hypTransport h hR) (tz h hc)).symm
  rw [psiU_apply, centralizer_uProj_eq (by omega) hT, hC, ← CFSG.Quasithin.map_perfectCore,
    ← CFSG.Quasithin.map_perfectCore, perfectCore_centralizer_tz h hc hc0 hf hε, range_psiU]

end Transfer

section Frame

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} (h : UnitaryFieldData 2 f K) (hk : 2 ≤ k)
  {s : K} (hs : s + h.bar s = 1)

theorem tmat_tz {c : K} (hc : h.bar c = c) :
    tmat h hk hs (tz h hc) = blk 1 (1 + c • vecMulVec (uw₀ hk) (uw₀ hk)) := by
  rw [tmat, coe_hypTransport, coe_tz, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    mul_transportInv (isHypTransport_uFrame h hk hs), Matrix.mul_smul, Matrix.smul_mul,
    transport_single h, uFrame_mulVec_hE, comp_uv₀, vecMulVec_uv₀]
  change (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) +
    c • blk 0 (vecMulVec (uw₀ hk) (uw₀ hk)) = _
  rw [← blk_one, blk_smul, blk_add, smul_zero, add_zero]

end Frame

end CFSG.ComponentClassification.RankTwoClassical.URigid
