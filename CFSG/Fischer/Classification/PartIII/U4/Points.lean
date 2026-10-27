module

public import CFSG.Fischer.Classification.PartIII.Beta.Iso
public import CFSG.Fischer.Classification.PartIII.U.Five
import all CFSG.Fischer.Classification.Unitary.Coords

public section

namespace CFSG.Fischer.Classification.LocalU4

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.LocalU CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

local instance (priority := high) decEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

@[expose] noncomputable def pt (i : Fin 45) : PG 4 := tq (vecK (uPt i))

theorem pt_mem_DG (i : Fin 45) : pt i ∈ DG 4 :=
  tq_mem_DG (vecK_ne_zero (uPt_spec i).1) (herm_vecK_uPt i)

theorem tq_vecK_eq {x : Fin 4 → F4} (hx0 : x ≠ 0) (hx : hU x x = 0) :
    tq (vecK x) = pt (uIdx x) := by
  obtain ⟨t, ht⟩ := exists_eq_smul_uPt_uIdx hx0 hx
  refine ((tq_eq_tq_iff (by norm_num) (vecK_ne_zero (uPt_spec _).1) (herm_vecK_uPt _)
    (vecK_ne_zero hx0) (by rw [herm_vecK, hx, map_zero])).2 ⟨eF4 t, ?_⟩).symm
  rw [← vecK_smul, ← ht]

theorem pt_injective : Function.Injective pt := by
  intro i j hij
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff (by norm_num) (vecK_ne_zero (uPt_spec i).1)
    (herm_vecK_uPt i) (vecK_ne_zero (uPt_spec j).1) (herm_vecK_uPt j)).1 hij
  obtain ⟨t, rfl⟩ := eF4.surjective c
  rw [← vecK_smul] at hc
  have hji := vecK_injective hc
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hji
    exact (uPt_spec j).1 hji
  rw [← uIdx_uPt j, hji, uIdx_smul_uPt i t ht]

theorem exists_pt_eq {q : PG 4} (hq : q ∈ DG 4) : ∃ i, pt i = q := by
  obtain ⟨v, hv0, hv, rfl⟩ := hq
  obtain ⟨x, rfl⟩ := vecK_surjective v
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hv0 vecK_zero
  have hx : hU x x = 0 := eF4.injective (by rw [← herm_vecK, hv, map_zero])
  exact ⟨uIdx x, (tq_vecK_eq hx0 hx).symm⟩

theorem DG_four_eq : DG 4 = Set.range pt :=
  Set.ext fun _ => ⟨fun hq => exists_pt_eq hq, fun ⟨i, hi⟩ => hi ▸ pt_mem_DG i⟩

theorem ncard_image_pt (I : Finset (Fin 45)) : (pt '' (I : Set (Fin 45))).ncard = I.card := by
  rw [Set.ncard_image_of_injective _ pt_injective, Set.ncard_coe_finset]

theorem ncard_DG_four : (DG 4).ncard = 45 := by
  rw [DG_four_eq, ← Set.image_univ, ← Finset.coe_univ, ncard_image_pt, Finset.card_univ,
    Fintype.card_fin]

@[expose] def cm (i j : Fin 45) : Prop := hU (uPt i) (uPt j) = 0

instance : DecidableRel cm := fun i j => inferInstanceAs (Decidable (hU (uPt i) (uPt j) = 0))

@[expose] def st (k l : Fin 45) : Prop := l ≠ k ∧ cm k l

instance : DecidableRel st := fun k l => inferInstanceAs (Decidable (l ≠ k ∧ cm k l))

@[expose] def tw (k i j : Fin 45) : Prop :=
  st k i ∧ st k j ∧ cm i j ∧ ∀ l, st k l → (cm l i ↔ cm l j)

instance (k i j : Fin 45) : Decidable (tw k i j) :=
  inferInstanceAs (Decidable (st k i ∧ st k j ∧ cm i j ∧ ∀ l, st k l → (cm l i ↔ cm l j)))

theorem pt_commute_iff (i j : Fin 45) : pt i * pt j = pt j * pt i ↔ cm i j := by
  rw [pt, pt, tq_commute_iff (by norm_num) (vecK_ne_zero (uPt_spec i).1) (herm_vecK_uPt i)
    (vecK_ne_zero (uPt_spec j).1) (herm_vecK_uPt j), herm_vecK, cm]
  exact map_eq_zero_iff eF4 eF4.injective

theorem pt_mem_localClass_iff (k l : Fin 45) : pt l ∈ LocalClass (DG 4) (pt k) ↔ st k l := by
  constructor
  · rintro ⟨-, hne, hc⟩
    exact ⟨fun h => hne (by rw [h]), (pt_commute_iff k l).1 hc.symm⟩
  · rintro ⟨hne, hc⟩
    exact ⟨pt_mem_DG l, fun h => hne (pt_injective h), ((pt_commute_iff k l).2 hc).symm⟩

theorem localClass_pt (k : Fin 45) : LocalClass (DG 4) (pt k) = pt '' {l | st k l} := by
  ext q
  constructor
  · intro hq
    obtain ⟨l, rfl⟩ := exists_pt_eq hq.1
    exact ⟨l, (pt_mem_localClass_iff k l).1 hq, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (pt_mem_localClass_iff k l).2 hl

theorem isTwin_pt_iff (k i j : Fin 45) :
    IsTwin (LocalClass (DG 4) (pt k)) (pt i) (pt j) ↔ tw k i j := by
  unfold IsTwin tw
  rw [pt_mem_localClass_iff, pt_mem_localClass_iff, pt_commute_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' ⟨fun h l hl => ?_,
    fun h c hc => ?_⟩))
  · have := h (pt l) ((pt_mem_localClass_iff k l).2 hl)
    rwa [pt_commute_iff, pt_commute_iff] at this
  · obtain ⟨l, rfl⟩ := exists_pt_eq hc.1
    rw [pt_commute_iff, pt_commute_iff]
    exact h l ((pt_mem_localClass_iff k l).1 hc)

@[expose] def tauI (i j : Fin 45) : Fin 45 := uIdx (tU (uPt i) (uPt j))

theorem pt_mul_mul (i j : Fin 45) : pt i * pt j * pt i = pt (tauI i j) := by
  have hx : vecK (tU (uPt i) (uPt j)) = tvU (vecK (uPt i)) • vecK (uPt j) :=
    (tvU_smul_vecK (uPt_spec i).2 _).symm
  have hx0 : tU (uPt i) (uPt j) ≠ 0 := fun h => by
    rw [h, vecK_zero] at hx
    exact vecK_ne_zero (uPt_spec j).1 ((smul_eq_zero_iff_eq _).1 hx.symm)
  have hxx : hU (tU (uPt i) (uPt j)) (tU (uPt i) (uPt j)) = 0 :=
    eF4.injective (by rw [← herm_vecK, hx, herm_smul_smul, herm_vecK_uPt, map_zero])
  rw [pt, pt, tq_mul_tq_mul_tq (herm_vecK_uPt i) (herm_vecK_uPt j), ← hx,
    tq_vecK_eq hx0 hxx, tauI]

theorem card_st : ∀ k : Fin 45, (Finset.univ.filter (st k)).card = 12 := by
  decide +kernel

theorem ncard_localClass_pt (k : Fin 45) : (LocalClass (DG 4) (pt k)).ncard = 12 := by
  rw [localClass_pt, ← card_st k, ← ncard_image_pt]
  congr 2
  ext l
  simp

theorem ncard_localClass_DG_four {g : PG 4} (hg : g ∈ DG 4) :
    (LocalClass (DG 4) g).ncard = 12 := by
  obtain ⟨k, rfl⟩ := exists_pt_eq hg
  exact ncard_localClass_pt k

@[expose] noncomputable def suOfMat {m : ℕ} (M₀ : Matrix (Fin m) (Fin m) F4) (h1 : M₀.det = 1)
    (h2 : M₀.transpose.map (fun c => c ^ 2) * M₀ = 1) : SUid frob m :=
  mkSU frob (M₀.map eF4)
    (by
      have h := RingHom.map_det (eF4 : F4 →+* K) M₀
      rw [RingHom.mapMatrix_apply, h1, map_one] at h
      exact h.symm)
    (fun x y => by
      have hc : conjTr frob (M₀.map eF4) * M₀.map eF4 = 1 := by
        have e1 : conjTr frob (M₀.map eF4) = (M₀.transpose.map (fun c => c ^ 2)).map eF4 := by
          ext i j
          simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, frob_eF4]
        rw [e1, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero eF4) (map_one eF4)]
      rw [herm_mulVec, hc, Matrix.one_mulVec])

theorem suOfMat_smul {m : ℕ} (M₀ : Matrix (Fin m) (Fin m) F4) (h1 : M₀.det = 1)
    (h2 : M₀.transpose.map (fun c => c ^ 2) * M₀ = 1) (v : Fin m → K) :
    suOfMat M₀ h1 h2 • v = Matrix.mulVec (M₀.map eF4) v := rfl

@[expose] def zMat : Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.diagonal ![F4.ω + 1, F4.ω + 1, F4.ω, F4.ω]

theorem det_zMat : zMat.det = 1 := by
  rw [zMat, Matrix.det_diagonal, Fin.prod_univ_four]
  decide +kernel

theorem unitary_zMat : zMat.transpose.map (fun c => c ^ 2) * zMat = 1 := by
  decide +kernel

@[expose] noncomputable def zSU : SUid frob 4 := suOfMat zMat det_zMat unitary_zMat

@[expose] noncomputable def zq : PG 4 := QuotientGroup.mk zSU

@[expose] def zF (x : Fin 4 → F4) : Fin 4 → F4 :=
  ![(F4.ω + 1) * x 0, (F4.ω + 1) * x 1, F4.ω * x 2, F4.ω * x 3]

theorem zSU_vecK (x : Fin 4 → F4) : zSU • vecK x = vecK (zF x) := by
  rw [zSU, suOfMat_smul]
  funext i
  fin_cases i <;> simp [zMat, zF, vecK, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.diagonal]

@[expose] def zI (i : Fin 45) : Fin 45 := uIdx (zF (uPt i))

theorem zF_spec : ∀ i : Fin 45, zF (uPt i) ≠ 0 ∧ hU (zF (uPt i)) (zF (uPt i)) = 0 := by
  decide +kernel

theorem conj_zq_pt (i : Fin 45) : zq * pt i * zq⁻¹ = pt (zI i) := by
  rw [zq, pt, conj_tq zSU (herm_vecK_uPt i), zSU_vecK, tq_vecK_eq (zF_spec i).1 (zF_spec i).2,
    zI]

theorem uPt_fifteen : uPt 15 = ![1, 1, 0, 0] := by
  decide +kernel

theorem uPt_twentyfive : uPt 25 = ![1, F4.ω, 0, 0] := by
  decide +kernel

theorem v₀_two_eq : v₀ 2 = vecK (uPt 15) := by
  rw [uPt_fifteen]
  funext i
  fin_cases i <;> simp [v₀, WittData.hypA, wd, vecK]

theorem u₀_two_eq : u₀ 2 = (1 - ω)⁻¹ • vecK (uPt 25) := by
  rw [uPt_twentyfive]
  funext i
  fin_cases i <;> simp [u₀, WittData.hypB, wd, vecK, omega_eq]

theorem tq_v₀_eq : tq (v₀ 2) = pt 15 := by
  rw [v₀_two_eq, pt]

theorem tq_u₀_eq : tq (u₀ 2) = pt 25 := by
  have hω : (1 - ω : K)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.2 (Ne.symm omega_ne_one))
  rw [u₀_two_eq, tq_smul_eq (herm_vecK_uPt 25) hω, pt]

theorem uy_zero : uy (0 : Fin 2 → K) = u₀ 2 := by
  rw [uy, map_zero, add_zero]
  have : γ (0 : Fin 2 → K) = 0 := by
    unfold γ
    simp
  rw [this, zero_smul, add_zero]

theorem muSet_pt_eq : ∀ l : Fin 45, (st 15 l ∧ st 25 l) ↔ (l = 0 ∨ l = 1 ∨ l = 2) := by
  decide +kernel

theorem muY_zero_eq : muY (0 : Fin 2 → K) = pt '' {l | l = 0 ∨ l = 1 ∨ l = 2} := by
  rw [muY, uy_zero, tq_v₀_eq, tq_u₀_eq, muSet, localClass_pt, localClass_pt,
    ← Set.image_inter pt_injective]
  congr 1
  ext l
  exact muSet_pt_eq l

end CFSG.Fischer.Classification.LocalU4
