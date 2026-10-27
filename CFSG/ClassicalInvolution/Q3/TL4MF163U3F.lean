module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG CFSG.ClassicalInvolution Matrix CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_frame_formula (hp2 : p ≠ 2) {Y : Type} [Group Y]
    {N : Subgroup Y} (e : ↥N ≃* StatedProj (StatedSU 3 (p ^ f) K)) {t : Y} (htN : t ∈ N)
    (ht : orderOf t = 2) :
    ∃ (c : ↥(StatedSU 3 (p ^ f) K)) (π : ↥(GU2Stated (p ^ f) K) →* Y),
      π.range = N ⊓ Subgroup.centralizer ({t} : Set Y) ∧ CubeKer π ∧
      π ⟨-1, neg_one_mem_GU2 h⟩ = t ∧
      ∀ A, π A =
        ((e.symm (statedProjMk (StatedSU 3 (p ^ f) K) (Lemma41aU3.phi h c A)) : N) : Y) := by
  set u := e ⟨t, htN⟩ with hu
  have htt' : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htt : (⟨t, htN⟩ : N) * ⟨t, htN⟩ = 1 := Subtype.ext htt'
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, htt, map_one]
  have hker : (statedProjMk (StatedSU 3 (p ^ f) K)).ker ≤ Subgroup.center _ :=
    ker_statedProjMk_le_center _
  have hZ : ∀ z ∈ (statedProjMk (StatedSU 3 (p ^ f) K)).ker, z ^ 3 = 1 := fun z hz =>
    Lemma41aU3.ker_pow_three h z hz
  obtain ⟨a, ha, hau⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ f) K))
    (statedProjMk_surjective _) hZ hu2
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, hu] at hau
    have h1 : (⟨t, htN⟩ : N) = 1 := e.injective (by rw [← hau, map_one])
    have h2 : t = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  let π : ↥(GU2Stated (p ^ f) K) →* Y :=
    N.subtype.comp (e.symm.toMonoidHom.comp
      ((statedProjMk (StatedSU 3 (p ^ f) K)).comp (Lemma41aU3.phi h c)))
  have hπ : ∀ A, π A =
      ((e.symm (statedProjMk (StatedSU 3 (p ^ f) K) (Lemma41aU3.phi h c A)) : N) : Y) :=
    fun _ => rfl
  have hphi1 : Lemma41aU3.phi h c ⟨-1, neg_one_mem_GU2 h⟩ = a := by
    show c * Lemma41aU3.blkU h ⟨-1, neg_one_mem_GU2 h⟩ * c⁻¹ = a
    rw [blkU_neg_one, hc]
  have hπ1 : π ⟨-1, neg_one_mem_GU2 h⟩ = t := by
    rw [hπ, hphi1, hau, hu, MulEquiv.symm_apply_apply]
  refine ⟨c, π, ?_, ?_, hπ1, hπ⟩
  · ext y
    constructor
    · rintro ⟨A, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(e.symm _).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hπ1, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        show (A : GL (Fin 2) K) * -1 = -1 * A
        rw [neg_one_mul, mul_neg_one])
    · intro hy
      obtain ⟨hyN, hyt⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨g, hg⟩ := statedProjMk_surjective _ (e ⟨y, hyN⟩)
      have hcomm : statedProjMk _ g * statedProjMk _ a = statedProjMk _ a * statedProjMk _ g := by
        rw [hg, hau, hu, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyt)
      have hga := Lemma41aL3.commute_of_map_commute _ hker hZ ha hcomm
      have hgC : g ∈ Subgroup.centralizer ({c * unitaryInvT h * c⁻¹} :
          Set ↥(StatedSU 3 (p ^ f) K)) := by
        rw [hc]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hga
      rw [← Lemma41aU3.phi_range h hp2 c] at hgC
      obtain ⟨A, hA⟩ := hgC
      refine ⟨A, ?_⟩
      rw [hπ, hA, hg, MulEquiv.symm_apply_apply]
  · intro A hA
    rw [hπ] at hA
    have h1 : e.symm (statedProjMk _ (Lemma41aU3.phi h c A)) = 1 := Subtype.ext hA
    have h2 : statedProjMk _ (Lemma41aU3.phi h c A) = 1 := e.symm.map_eq_one_iff.mp h1
    have h3 : ((Lemma41aU3.phi h c A : ↥(StatedSU 3 (p ^ f) K)) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    obtain ⟨l, hl⟩ := h3
    have hcoe : ((Lemma41aU3.phi h c A : ↥(StatedSU 3 (p ^ f) K)) : GL (Fin 3) K) =
        (c : GL (Fin 3) K) * Lemma41aL3.blk (A : GL (Fin 2) K) * (c : GL (Fin 3) K)⁻¹ := rfl
    have hblk : Lemma41aL3.blk (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 3) l := by
      have e1 : Lemma41aL3.blk (A : GL (Fin 2) K) = (c : GL (Fin 3) K)⁻¹ *
          ((c : GL (Fin 3) K) * Lemma41aL3.blk A * (c : GL (Fin 3) K)⁻¹) * (c : GL (Fin 3) K) := by
        group
      rw [e1, ← hcoe, ← hl, mul_assoc, Q5L3.scalar_mul_comm₃ l, ← mul_assoc, inv_mul_cancel,
        one_mul]
    exact ⟨l, (blk_eq_scalar hblk).1, (blk_eq_scalar hblk).2⟩

theorem exists_std_equiv {Y : Type} [Group Y] {N : Subgroup Y}
    (e : ↥N ≃* StatedProj (StatedSU 3 (p ^ f) K)) (c : ↥(StatedSU 3 (p ^ f) K))
    {π : ↥(GU2Stated (p ^ f) K) →* Y}
    (hπ : ∀ A, π A =
      ((e.symm (statedProjMk (StatedSU 3 (p ^ f) K) (Lemma41aU3.phi h c A)) : N) : Y)) :
    ∃ E : ↥N ≃* unitaryPSU h 3, ∀ A (hA : π A ∈ N),
      E ⟨π A, hA⟩ = ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) := by
  refine ⟨(e.trans (unitaryPSUEquiv h (by norm_num)).symm).trans
    (MulAut.conj ((c : unitaryPSU h 3)⁻¹)), fun A hA => ?_⟩
  have hn : (⟨π A, hA⟩ : N) =
      e.symm (statedProjMk (StatedSU 3 (p ^ f) K) (Lemma41aU3.phi h c A)) :=
    Subtype.ext (hπ A)
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hn, MulEquiv.apply_symm_apply,
    MulAut.conj_apply]
  have h1 : (unitaryPSUEquiv h (by norm_num)).symm
      (statedProjMk (StatedSU 3 (p ^ f) K) (Lemma41aU3.phi h c A)) =
      ((Lemma41aU3.phi h c A : unitarySU p f K 3) : unitaryPSU h 3) := by
    rw [MulEquiv.symm_apply_eq]
    exact (unitaryPSUEquiv_unitaryProj h (by norm_num) _).symm
  rw [h1]
  show ((c : unitaryPSU h 3))⁻¹ * ((c * Lemma41aU3.blkU h A * c⁻¹ : unitarySU p f K 3) :
    unitaryPSU h 3) * ((c : unitaryPSU h 3))⁻¹⁻¹ = _
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_inv]
  group

theorem exists_norm_one_gen (hq : 5 ≤ p ^ f) :
    ∃ x : K, h.bar x * x = 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1 := by
  have := h.finite
  have hcard := (unitary_field_norm h).2.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Units.map h.normHom).ker)
  have hord : orderOf g = p ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hx := (h.mem_ker_normUnits).mp g.2
  rw [UnitaryFieldData.norm, mul_comm] at hx
  refine ⟨((g : Kˣ) : K), hx, fun h2 => ?_, fun h3 => ?_⟩
  · have hg2 : g ^ 2 = 1 := Subtype.ext (Units.ext (by simpa using h2))
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one hg2)
    omega
  · have hg3 : g ^ 3 = 1 := Subtype.ext (Units.ext (by simpa using h3))
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one hg3)
    omega

theorem dx_det {x : K} (hx0 : x ≠ 0) : x * x⁻¹ - 0 * 0 = 1 := by
  rw [mul_inv_cancel₀ hx0]
  ring

theorem w_det : (0 : K) * 0 - 1 * (-1) = 1 := by ring

theorem dx_mem {x : K} (hxu : h.bar x * x = 1) (hx0 : x ≠ 0) :
    mk2 x 0 0 x⁻¹ (dx_det hx0) ∈ GU2Stated (p ^ f) K := by
  rw [Lemma41aU3.mem_GU2Stated_iff h, coe_mk2]
  have hbx' : (h.bar x)⁻¹ * x⁻¹ = 1 := by rw [← mul_inv, hxu, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hxu, hbx']

include h in
theorem w_mem : mk2 (0 : K) 1 (-1) 0 w_det ∈ GU2Stated (p ^ f) K := by
  rw [Lemma41aU3.mem_GU2Stated_iff h, coe_mk2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_blkU_dx {x : K} (hxu : h.bar x * x = 1) (hx0 : x ≠ 0) :
    (((Lemma41aU3.blkU h ⟨_, dx_mem h hxu hx0⟩ : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![x, x⁻¹, 1] := by
  show ((Lemma41aL3.blk (mk2 x 0 0 x⁻¹ (dx_det hx0)) : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [Lemma41aL3.coe_blk, coe_mk2, Matrix.det_fin_two_of, dx_det hx0, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem coe_blkU_w :
    (((Lemma41aU3.blkU h ⟨_, w_mem h⟩ : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  show ((Lemma41aL3.blk (mk2 (0 : K) 1 (-1) 0 w_det) : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [Lemma41aL3.coe_blk, coe_mk2, Matrix.det_fin_two_of, w_det, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem coe_blkU_scalar {A : ↥(GU2Stated (p ^ f) K)} {l : Kˣ}
    (hA : (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) l) (hl : (l : K) ^ 2 = -1) :
    (((Lemma41aU3.blkU h A : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), l, -1] := by
  show ((Lemma41aL3.blk (A : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [Lemma41aL3.coe_blk, hA, GeneralLinearGroup.coe_scalar]
  have hdet : (Matrix.scalar (Fin 2) (l : K)).det = -1 := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, ← sq, hl]
  rw [hdet, inv_neg, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, Matrix.scalar_apply]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
