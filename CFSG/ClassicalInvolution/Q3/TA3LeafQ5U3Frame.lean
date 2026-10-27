module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Frame
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U3

open CFSG CFSG.ClassicalInvolution Matrix Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def mk2 (a b c d : K) (h : a * d - b * c = 1) : GL (Fin 2) K :=
  ⟨!![a, b; c, d], !![d, -b; -c, a],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h⟩

theorem coe_mk2 (a b c d : K) (h : a * d - b * c = 1) :
    ((mk2 a b c d h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] := rfl

theorem det_mk2 (a b c d : K) (h : a * d - b * c = 1) :
    GeneralLinearGroup.det (mk2 a b c d h) = 1 :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_mk2, Matrix.det_fin_two_of, h]; rfl)

theorem neg_one_mem_GU2 (h : UnitaryFieldData p f K) :
    (-1 : GL (Fin 2) K) ∈ GU2Stated (p ^ f) K := by
  rw [Lemma41aU3.mem_GU2Stated_iff h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem blkU_neg_one (h : UnitaryFieldData p f K) :
    Lemma41aU3.blkU h ⟨-1, neg_one_mem_GU2 h⟩ = unitaryInvT h := by
  apply Subtype.ext
  show Lemma41aL3.blk (-1 : GL (Fin 2) K) = _
  rw [Q5L3.blk_neg_one]
  apply Units.ext
  rw [RankThree.SubgroupLists.coe_negDiag3, coe_unitaryInvT]
  rfl

theorem exists_frame (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {Y : Type} [Group Y]
    {N : Subgroup Y} (e : ↥N ≃* StatedProj (StatedSU 3 (p ^ f) K)) {t : Y} (htN : t ∈ N)
    (ht : orderOf t = 2) :
    ∃ π : ↥(GU2Stated (p ^ f) K) →* Y,
      π.range = N ⊓ Subgroup.centralizer ({t} : Set Y) ∧ CubeKer π ∧
      π ⟨-1, neg_one_mem_GU2 h⟩ = t := by
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
  refine ⟨π, ?_, ?_, hπ1⟩
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

theorem exists_norm_one (h : UnitaryFieldData p f K) :
    ∃ x : Kˣ, h.bar (x : K) * x = 1 ∧ (x : K) * x ≠ 1 := by
  have hcard := (unitary_field_norm h).2.2.1
  have hq : 2 ≤ p ^ f :=
    (h.prime.two_le).trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  classical
  by_contra hne
  push Not at hne
  have hmem : ∀ x : (Units.map h.normHom).ker, ((x : Kˣ) : K) = 1 ∨ ((x : Kˣ) : K) = -1 := by
    intro x
    have hx := (h.mem_ker_normUnits).mp x.2
    rw [UnitaryFieldData.norm, mul_comm] at hx
    exact mul_self_eq_one_iff.mp (hne _ hx)
  have hinj : Function.Injective
      (fun x : (Units.map h.normHom).ker => decide (((x : Kˣ) : K) = 1)) := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    by_cases hx : ((x : Kˣ) : K) = 1
    · have hy : ((y : Kˣ) : K) = 1 := by simpa [hx] using hxy.symm
      rw [hx, hy]
    · have hy : ¬ ((y : Kˣ) : K) = 1 := by simpa [hx] using hxy.symm
      rw [(hmem x).resolve_left hx, (hmem y).resolve_left hy]
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  omega

theorem slCentScalar_GU2 (h : UnitaryFieldData p f K) : SLCentScalar (GU2Stated (p ^ f) K) := by
  obtain ⟨x, hxn, hx2⟩ := exists_norm_one h
  have hx0 : (x : K) ≠ 0 := x.ne_zero
  have hxinv : (x : K) * (x : K)⁻¹ - 0 * 0 = 1 := by rw [mul_inv_cancel₀ hx0]; ring
  set D := mk2 (x : K) 0 0 (x : K)⁻¹ hxinv with hD
  have hDmem : D ∈ GU2Stated (p ^ f) K := by
    rw [Lemma41aU3.mem_GU2Stated_iff h, hD, coe_mk2]
    have hbx' : (h.bar (x : K))⁻¹ * (x : K)⁻¹ = 1 := by
      rw [← mul_inv, hxn, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hxn, hbx']
  have hWdet : (0 : K) * 0 - 1 * (-1) = 1 := by ring
  set W := mk2 (0 : K) 1 (-1) 0 hWdet with hW
  have hWmem : W ∈ GU2Stated (p ^ f) K := by
    rw [Lemma41aU3.mem_GU2Stated_iff h, hW, coe_mk2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  intro A hA
  have h1 := congrArg Units.val (hA ⟨D, hDmem⟩ (mem_slPart.mpr (det_mk2 _ _ _ _ hxinv)))
  have h2 := congrArg Units.val (hA ⟨W, hWmem⟩ (mem_slPart.mpr (det_mk2 _ _ _ _ hWdet)))
  simp only [Units.val_mul] at h1 h2
  set M := (A : Matrix (Fin 2) (Fin 2) K) with hM
  have e01 : M 0 1 * (x : K)⁻¹ = (x : K) * M 0 1 := by
    have := congrFun (congrFun h1 0) 1
    simpa [hD, coe_mk2, Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : M 1 0 * (x : K) = (x : K)⁻¹ * M 1 0 := by
    have := congrFun (congrFun h1 1) 0
    simpa [hD, coe_mk2, Matrix.mul_apply, Fin.sum_univ_two] using this
  have e00 : M 0 0 = M 1 1 := by
    have := congrFun (congrFun h2 0) 1
    simpa [hW, coe_mk2, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hxx : (x : K)⁻¹ - (x : K) ≠ 0 := by
    intro h0
    apply hx2
    have : (x : K)⁻¹ = x := by linear_combination h0
    calc (x : K) * x = x * (x : K)⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel₀ hx0
  have h01 : M 0 1 = 0 := by
    have : M 0 1 * ((x : K)⁻¹ - (x : K)) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hxx
  have h10 : M 1 0 = 0 := by
    have : M 1 0 * ((x : K)⁻¹ - (x : K)) = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_right hxx
  have h00 : M 0 0 ≠ 0 := by
    intro h0
    have hdet : M.det = 0 := by
      rw [Matrix.det_fin_two, h01, h0]
      ring
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hdet
  refine ⟨Units.mk0 (M 0 0) h00, Units.ext ?_⟩
  show M = _
  rw [GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, e00]

theorem nonempty_slPart_equiv [Finite K] [Fact p.Prime] [CharP K p]
    (h : UnitaryFieldData p f K) :
    Nonempty (slPart (GU2Stated (p ^ f) K) ≃* SL(2, LieType.Steinberg.fixedSubfield K p f)) := by
  have hK := h.card_eq_sq
  obtain ⟨e₁⟩ := Models.nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  have hmem : ∀ A : GL (Fin 2) K,
      A ∈ LieType.Universal.Unitary.SUid (LieType.BorelTits.unitaryInvolution K p f) 2 ↔
        A ∈ GU2Stated (p ^ f) K ∧ GeneralLinearGroup.det A = 1 := by
    intro A
    rw [LieType.Universal.Unitary.SUid_eq_statedSU hK 2,
      show StatedSU 2 (p ^ f) K = ClassicalGroups.UnitaryFlag.unitarySU p f K 2 from rfl,
      ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, Lemma41aU3.mem_GU2Stated_iff h]
    constructor
    · rintro ⟨hd, hu⟩
      exact ⟨hu, Units.ext (by rw [GeneralLinearGroup.val_det_apply, hd]; rfl)⟩
    · rintro ⟨hu, hd⟩
      exact ⟨by rw [← GeneralLinearGroup.val_det_apply, hd]; rfl, hu⟩
  let e₂ : slPart (GU2Stated (p ^ f) K) ≃* Phan.Su K p f 2 :=
    { toFun := fun A => ⟨((A : ↥(GU2Stated (p ^ f) K)) : GL (Fin 2) K),
        (hmem _).mpr ⟨A.1.2, mem_slPart.mp A.2⟩⟩
      invFun := fun B => ⟨⟨B, ((hmem _).mp B.2).1⟩, mem_slPart.mpr ((hmem _).mp B.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact ⟨e₂.trans e₁.symm⟩

end CFSG.ClassicalInvolution.Q3.TA3.Q5U3
