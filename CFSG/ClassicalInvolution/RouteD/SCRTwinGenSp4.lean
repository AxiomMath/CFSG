module

public import CFSG.ClassicalInvolution.RouteD.SCRSp4Toral
public import CFSG.ClassicalInvolution.RouteD.SCRSp4Levi
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSL4
public import CFSG.Timmesfeld.Transvection.ModelSpGen
public import CFSG.Timmesfeld.ARS.CaseMSpPlane
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.Timmesfeld.ARS
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups
open CFSG.Timmesfeld.ARS.CaseM

variable {F : Type} [Field F]

noncomputable def g4 (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![1, 1, 1, 1; -1, 1, 1, -1; -1, -1, 1, 1; -1, 1, -1, 1]

noncomputable def e4 : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  (finCongr (by norm_num : 2 + 2 = 4)).symm.trans finSumFinEquiv.symm

noncomputable def gMat (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  (Matrix.reindex e4 e4) (g4 F)

theorem gMat_apply (i j : Fin 2 ⊕ Fin 2) :
    gMat F i j = g4 F (e4.symm i) (e4.symm j) := by
  simp [gMat, Matrix.reindex_apply]

noncomputable def J4 (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem gram_eq_reindex_J4 :
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 = (Matrix.reindex e4 e4) (J4 F) := by
  ext i j
  rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, J4, Matrix.reindex_apply, fromBlocks, e4, finSumFinEquiv]

theorem g4_symplectic (h3 : (3 : F) = 0) :
    (g4 F)ᵀ * J4 F * g4 F = J4 F := by
  have h2 : (2 : F) = -1 := by linear_combination h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g4, J4, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  all_goals first | linear_combination h3 | linear_combination -h3

theorem gMat_symplectic (h3 : (3 : F) = 0) :
    (gMat F)ᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 * gMat F = CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) F =>
      (Matrix.reindex e4 e4) M)
    (g4_symplectic (F := F) h3)
  simpa [gMat, gram_eq_reindex_J4, Matrix.transpose_reindex, Matrix.reindex_apply, e4,
    Matrix.mul_assoc] using h

noncomputable def Jsl (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  Ad (-1) (by simp)

theorem coe_Jsl : ((Jsl F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  rw [Jsl, coe_Ad]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem gMat_comm_ut_J :
    gMat F * mat 2 F (ut (Jsl F) (Jsl F)) =
      mat 2 F (ut (Jsl F) (Jsl F)) * gMat F := by
  ext i j
  rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [gMat, e4, mat_ut, coe_Jsl, Matrix.reindex_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, g4, finSumFinEquiv]

noncomputable def gEl (h3 : (3 : F) = 0) : StatedSp 2 F :=
  ofSymplecticMat (gMat F) (gMat_symplectic (F := F) h3)

theorem mat_gEl (h3 : (3 : F) = 0) : mat 2 F (gEl (F := F) h3) = gMat F :=
  mat_ofSymplecticMat _ _

theorem gEl_comm_u (h3 : (3 : F) = 0) :
    gEl (F := F) h3 * ut (Jsl F) (Jsl F) = ut (Jsl F) (Jsl F) * gEl (F := F) h3 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_gEl, gMat_comm_ut_J]

theorem x0_sq : x0 F * x0 F = 1 := by
  rw [x0_eq, ← map_mul]
  norm_num
  exact map_one (phi4 F)

theorem x0_mulVec_of_mem_minus {v : Fin 2 ⊕ Fin 2 → F}
    (hv : v ∈ minusSpace (x0 F)) : mat 2 F (x0 F) *ᵥ v = -v :=
  mem_minusSpace.mp hv

theorem x0_mulVec_of_mem_fix {v : Fin 2 ⊕ Fin 2 → F}
    (hv : v ∈ fixSpace (x0 F)) : mat 2 F (x0 F) *ᵥ v = v :=
  mem_fixSpace.mp hv

theorem transvectionGroup_le_centralizer_of_minus {v : Fin 2 ⊕ Fin 2 → F}
    {X : Subgroup (StatedSp 2 F)} (hX : IsTransGroup v X)
    (hv : mat 2 F (x0 F) *ᵥ v = -v) : X ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨c, hc⟩ := (hX.1 x).1 hx
  have hconj : mat 2 F (x0 F * x * (x0 F)⁻¹) = mat 2 F x := by
    rw [mat_conj_of_mat_eq hc (x0 F), hv]
    have hneg : spTrans (-v) c = spTrans v c := by
      rw [show -v = (-1 : F) • v by simp, spTrans_smul]
      simp
    rw [hneg, ← hc]
  have heq : x0 F * x * (x0 F)⁻¹ = x := mat_injective hconj
  have hinv : (x0 F)⁻¹ = x0 F := inv_eq_of_mul_eq_one_right x0_sq
  rw [hinv] at heq
  calc x * x0 F = (x0 F * x * x0 F) * x0 F := by rw [heq]
    _ = x0 F * x * (x0 F * x0 F) := by group
    _ = x0 F * x := by rw [x0_sq, mul_one]

theorem transvectionGroup_le_centralizer_of_fix {v : Fin 2 ⊕ Fin 2 → F}
    {X : Subgroup (StatedSp 2 F)} (hX : IsTransGroup v X)
    (hv : mat 2 F (x0 F) *ᵥ v = v) : X ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_of_mat_mulVec_eq hX hv x hx).symm

def plane0Vec (v : Fin 2 ⊕ Fin 2 → F) : Fin 2 → F := ![v (Sum.inl 0), v (Sum.inr 0)]

def plane1Vec (v : Fin 2 ⊕ Fin 2 → F) : Fin 2 → F := ![v (Sum.inl 1), v (Sum.inr 1)]

def w0 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1

theorem plane0Vec_gw (h3 : (3 : F) = 0) :
    plane0Vec (mat 2 F (gEl (F := F) h3) *ᵥ w0) = ![1, -1] := by
  ext i
  fin_cases i <;>
    simp [plane0Vec, w0, mat_gEl, gMat_apply, Matrix.mulVec, g4,
      e4, finSumFinEquiv]

theorem plane1Vec_gw (h3 : (3 : F) = 0) :
    plane1Vec (mat 2 F (gEl (F := F) h3) *ᵥ w0) = ![-1, -1] := by
  ext i
  fin_cases i <;>
    simp [plane1Vec, w0, mat_gEl, gMat_apply, Matrix.mulVec, g4,
      e4, finSumFinEquiv]

theorem gEl_mulVec_w0_inl0 (h3 : (3 : F) = 0) :
    (mat 2 F (gEl (F := F) h3) *ᵥ w0) (Sum.inl 0) = 1 :=
  congrFun (plane0Vec_gw h3) 0

theorem gEl_mulVec_w0_inr0 (h3 : (3 : F) = 0) :
    (mat 2 F (gEl (F := F) h3) *ᵥ w0) (Sum.inr 0) = -1 :=
  congrFun (plane0Vec_gw h3) 1

theorem gEl_mulVec_w0_inl1 (h3 : (3 : F) = 0) :
    (mat 2 F (gEl (F := F) h3) *ᵥ w0) (Sum.inl 1) = -1 :=
  congrFun (plane1Vec_gw h3) 0

theorem gEl_mulVec_w0_inr1 (h3 : (3 : F) = 0) :
    (mat 2 F (gEl (F := F) h3) *ᵥ w0) (Sum.inr 1) = -1 :=
  congrFun (plane1Vec_gw h3) 1

theorem plane0Vec_ne_zero_of_not_mem_fix (h2 : (2 : F) ≠ 0)
    {v : Fin 2 ⊕ Fin 2 → F} (hv : v ∉ fixSpace (x0 F)) : plane0Vec v ≠ 0 := by
  have h : ¬ ∀ t ∈ coords (0 : Fin 2), v t = 0 := by
    intro h
    exact hv ((mem_fixSpace_longInv h2 0).2 h)
  push Not at h
  obtain ⟨t, ht, hvt⟩ := h
  intro hzero
  have ht' : t = Sum.inl (0 : Fin 2) ∨ t = Sum.inr (0 : Fin 2) := by
    simpa [coords] using ht
  rcases ht' with rfl | rfl
  · exact hvt (by simpa [plane0Vec] using congrFun hzero 0)
  · exact hvt (by simpa [plane0Vec] using congrFun hzero 1)

theorem plane1Vec_ne_zero_of_not_mem_minus (h2 : (2 : F) ≠ 0)
    {v : Fin 2 ⊕ Fin 2 → F} (hv : v ∉ minusSpace (x0 F)) : plane1Vec v ≠ 0 := by
  have h : ¬ ∀ t, t ∉ coords (0 : Fin 2) → v t = 0 := by
    intro h
    exact hv ((mem_minusSpace_longInv h2 0).2 h)
  push Not at h
  obtain ⟨t, ht, hvt⟩ := h
  intro hzero
  have ht' : t = Sum.inl (1 : Fin 2) ∨ t = Sum.inr (1 : Fin 2) := by
    rcases t with i | i <;> fin_cases i <;> simp [coords] at ht ⊢
  rcases ht' with rfl | rfl
  · exact hvt (by simpa [plane1Vec] using congrFun hzero 0)
  · exact hvt (by simpa [plane1Vec] using congrFun hzero 1)

theorem phi4_mulVec (A0 A1 : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 ⊕ Fin 2 → F) :
    mat 2 F (phi4 F (A0, A1)) *ᵥ v =
      fun t => match t with
        | Sum.inl 0 => ((A0 : Matrix (Fin 2) (Fin 2) F) *ᵥ plane0Vec v) 0
        | Sum.inl 1 => ((A1 : Matrix (Fin 2) (Fin 2) F) *ᵥ plane1Vec v) 0
        | Sum.inr 0 => ((A0 : Matrix (Fin 2) (Fin 2) F) *ᵥ plane0Vec v) 1
        | Sum.inr 1 => ((A1 : Matrix (Fin 2) (Fin 2) F) *ᵥ plane1Vec v) 1 := by
  ext t
  rcases t with t | t <;> fin_cases t <;>
    simp [phi4_apply, map_mul, mat_longBlock, blockMat, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two, plane0Vec, plane1Vec, Fintype.sum_sum_type]

theorem transvectionGroup_le_of_mixed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0)
    {v : Fin 2 ⊕ Fin 2 → F} {X L : Subgroup (StatedSp 2 F)}
    (hX : IsTransGroup v X)
    (hv_minus : v ∉ minusSpace (x0 F)) (hv_fix : v ∉ fixSpace (x0 F))
    (hx0L : Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ≤ L)
    (hgL : gEl (F := F) h3 ∈ L) : X ≤ L := by
  have hv0 : plane0Vec v ≠ 0 := plane0Vec_ne_zero_of_not_mem_fix h2 hv_fix
  have hv1 : plane1Vec v ≠ 0 := plane1Vec_ne_zero_of_not_mem_minus h2 hv_minus
  have h10 : (![1, -1] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hm10 : (![-1, -1] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  obtain ⟨A0, hA0⟩ :=
    CFSG.CGT.PushingUpLit.BHS.exists_SL2_mulVec_eq ![1, -1] (plane0Vec v) h10 hv0
  obtain ⟨A1, hA1⟩ :=
    CFSG.CGT.PushingUpLit.BHS.exists_SL2_mulVec_eq ![-1, -1] (plane1Vec v) hm10 hv1
  let h : StatedSp 2 F := phi4 F (A0, A1)
  have hC : h ∈ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) :=
    phi4_mem_centralizer_x0 (A0, A1)
  have hL : h ∈ L := hx0L hC
  have hw_mem : w0 ∈ minusSpace (x0 F) := by
    rw [mem_minusSpace_longInv h2 0]
    intro t ht
    rcases t with i | i <;> fin_cases i <;> simp [w0, coords] at ht ⊢
  obtain ⟨Xw, hXw⟩ := exists_isTransGroup (n := 2) (K := F) w0
  have hXwC : Xw ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) :=
    transvectionGroup_le_centralizer_of_minus hXw (x0_mulVec_of_mem_minus hw_mem)
  have hXwL : Xw ≤ L := hXwC.trans hx0L
  let Xg : Subgroup (StatedSp 2 F) := conjSub Xw (gEl (F := F) h3)
  have hXg : IsTransGroup (mat 2 F (gEl (F := F) h3) *ᵥ w0) Xg :=
    hXw.conjSub (gEl (F := F) h3)
  have hXgL : Xg ≤ L := conjSub_le hXwL hgL
  let Xv : Subgroup (StatedSp 2 F) := conjSub Xg h
  have hXv : IsTransGroup (mat 2 F h *ᵥ (mat 2 F (gEl (F := F) h3) *ᵥ w0)) Xv :=
    hXg.conjSub h
  have hvec : mat 2 F h *ᵥ (mat 2 F (gEl (F := F) h3) *ᵥ w0) = v := by
    rw [phi4_mulVec]
    ext t
    rcases t with t | t <;> fin_cases t <;>
      simp [gEl_mulVec_w0_inl0 h3, gEl_mulVec_w0_inr0 h3,
      gEl_mulVec_w0_inl1 h3, gEl_mulVec_w0_inr1 h3, hA0, hA1, plane0Vec, plane1Vec]
  have hXv' : IsTransGroup v Xv := by
    rwa [hvec] at hXv
  have hXvL : Xv ≤ L := conjSub_le hXgL hL
  calc X = Xv := hX.eq hXv'
    _ ≤ L := hXvL

theorem card3_sup_eq_top_utJ (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0) :
    Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (Jsl F) (Jsl F)} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (Jsl F) (Jsl F)} : Set (StatedSp 2 F)) = ⊤ := by
  let L := Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (Jsl F) (Jsl F)} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (Jsl F) (Jsl F)} : Set (StatedSp 2 F))
  have hx0L : Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ≤ L :=
    le_sup_left.trans le_sup_left
  have huL : Subgroup.centralizer ({ut (Jsl F) (Jsl F)} : Set (StatedSp 2 F)) ≤ L :=
    le_sup_right.trans le_sup_left
  have hgL : gEl (F := F) h3 ∈ L :=
    huL (Subgroup.mem_centralizer_singleton_iff.mpr (gEl_comm_u h3))
  refine eq_top_of_forall_isTransGroup_le fun v X hX => ?_
  by_cases hv_minus : v ∈ minusSpace (x0 F)
  · exact (transvectionGroup_le_centralizer_of_minus hX (x0_mulVec_of_mem_minus hv_minus)).trans hx0L
  · by_cases hv_fix : v ∈ fixSpace (x0 F)
    · exact (transvectionGroup_le_centralizer_of_fix hX (x0_mulVec_of_mem_fix hv_fix)).trans hx0L
    · exact transvectionGroup_le_of_mixed h2 h3 hX hv_minus hv_fix hx0L hgL

theorem eq_one_or_neg_one_of_card3 (hcard3 : Nat.card F = 3) {d : F} (hd : d ≠ 0) :
    d = 1 ∨ d = -1 := by
  have hFinite : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
  have hFintype : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 3 := by rwa [← Nat.card_eq_fintype_card]
  have hsq : d ^ 2 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one d hd
    simpa [hq] using this
  have h : (d - 1) * (d + 1) = 0 := by
    calc
      (d - 1) * (d + 1) = d ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp h with h1 | h1
  · left
    linear_combination h1
  · right
    linear_combination h1

noncomputable def conjAd (d : F) (_hd : d ≠ 0) : SL(2, F) := by
  classical
  exact if h : d = 1 then ⟨!![1, 1; 1, 2], by
      norm_num [Matrix.det_fin_two]⟩ else 1

theorem conjAd_mul_Ad_mul_inv (hcard3 : Nat.card F = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0)
    (d : F) (hd : d ≠ 0) :
    conjAd d hd * Ad d hd * (conjAd d hd)⁻¹ = Jsl F := by
  have hd1 : d = 1 ∨ d = -1 := eq_one_or_neg_one_of_card3 hcard3 hd
  rcases hd1 with rfl | hdneg
  · let A : SL(2, F) := ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩
    have hA : conjAd 1 hd = A := by
      simp [conjAd, A]
      apply Subtype.ext
      rfl
    rw [hA]
    have h2neg : (2 : F) = -1 := by linear_combination h3
    have hInter : A * Ad 1 hd = Jsl F * A := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, Ad, Jsl, Matrix.mul_apply, Fin.sum_univ_two, h2neg]
    calc
      A * Ad 1 hd * A⁻¹ = Jsl F * A * A⁻¹ := by rw [hInter]
      _ = Jsl F := by group
  · subst d
    have hne : (-1 : F) ≠ 1 := by
      intro h
      have h2eq : (2 : F) = 0 := by
        calc
          (2 : F) = 1 + 1 := by ring
          _ = -1 + 1 := by rw [h]
          _ = 0 := by ring
      exact h2 h2eq
    simp [conjAd, hne]
    apply Subtype.ext
    rfl

theorem three_eq_zero_of_card_eq_three [Finite F] (hcard3 : Nat.card F = 3) : (3 : F) = 0 := by
  have hFintype : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 3 := by rwa [← Nat.card_eq_fintype_card]
  have h := Nat.cast_card_eq_zero F
  rwa [hq] at h

theorem sp4_sup_eq_top [Finite F] (h2 : (2 : F) ≠ 0) (hcard : 3 ≤ Nat.card F) (B B' : SL(2, F))
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = -1)
    (hB' : (B' : Matrix (Fin 2) (Fin 2) F) * B' = -1) :
    Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut B B'} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut B B'} : Set (StatedSp 2 F)) = ⊤ := by
  by_cases hι : IsSquare (-1 : F)
  · obtain ⟨ι, hι⟩ := hι
    have hι' : ι * ι = -1 := hι.symm
    obtain ⟨h, hh⟩ := exists_conj_Dι hι' h2 B hB
    obtain ⟨h', hh'⟩ := exists_conj_Dι hι' h2 B' hB'
    refine sup_eq_top_of_conj h h' B B' ?_
    rw [hh, hh']
    exact toral_sup_eq_top ι hι'
  · by_cases hcard3 : Nat.card F = 3
    · have h3 : (3 : F) = 0 := three_eq_zero_of_card_eq_three hcard3
      obtain ⟨h, d, hd, hh⟩ := exists_conj_Ad hι B hB
      obtain ⟨h', d', hd', hh'⟩ := exists_conj_Ad hι B' hB'
      let c : SL(2, F) := conjAd d hd * h
      let c' : SL(2, F) := conjAd d' hd' * h'
      have hcB : c * B * c⁻¹ = Jsl F := by
        dsimp [c]
        rw [show conjAd d hd * h * B * (conjAd d hd * h)⁻¹ =
            conjAd d hd * (h * B * h⁻¹) * (conjAd d hd)⁻¹ by group]
        rw [hh, conjAd_mul_Ad_mul_inv hcard3 h2 h3 d hd]
      have hcB' : c' * B' * c'⁻¹ = Jsl F := by
        dsimp [c']
        rw [show conjAd d' hd' * h' * B' * (conjAd d' hd' * h')⁻¹ =
            conjAd d' hd' * (h' * B' * h'⁻¹) * (conjAd d' hd')⁻¹ by group]
        rw [hh', conjAd_mul_Ad_mul_inv hcard3 h2 h3 d' hd']
      refine sup_eq_top_of_conj c c' B B' ?_
      rw [hcB, hcB']
      exact card3_sup_eq_top_utJ h2 h3
    · obtain ⟨h, d, hd, hh⟩ := exists_conj_Ad hι B hB
      obtain ⟨h', d', hd', hh'⟩ := exists_conj_Ad hι B' hB'
      refine sup_eq_top_of_conj h h' B B' ?_
      rw [hh, hh']
      have := Fintype.ofFinite F
      have hmod : Fintype.card F % 4 = 3 := by
        by_contra hne
        exact hι (FiniteField.isSquare_neg_one_iff.mpr hne)
      have hc3 : 3 ≤ Fintype.card F := by
        rw [← Nat.card_eq_fintype_card]
        exact hcard
      have hc6 : 6 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        have hne3 : Fintype.card F ≠ 3 := by
          intro h3
          apply hcard3
          rw [Nat.card_eq_fintype_card, h3]
        omega
      exact levi_sup_eq_top h2 hc6 d d' hd hd'

theorem mat_scalar_of_mem_center {g : StatedSp 2 F} (hg : g ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ r : F, mat 2 F g = Matrix.scalar _ r := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hg
  obtain ⟨r, hr⟩ := hg
  exact ⟨r, by rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar]⟩

theorem eq_one_of_longBlock_mem_center (k : Fin 2) {Y : SL(2, F)}
    (hg : longBlock F 2 k Y ∈ Subgroup.center (StatedSp 2 F)) : Y = 1 := by
  obtain ⟨r, hr⟩ := mat_scalar_of_mem_center hg
  rw [mat_longBlock] at hr
  have e := fun a b => congrFun (congrFun hr a) b
  have hk : Fin.rev k ≠ k := by fin_cases k <;> decide
  have h1 := e (Sum.inl (Fin.rev k)) (Sum.inl (Fin.rev k))
  have h2 := e (Sum.inl k) (Sum.inl k)
  have h3 := e (Sum.inl k) (Sum.inr k)
  have h4 := e (Sum.inr k) (Sum.inl k)
  have h5 := e (Sum.inr k) (Sum.inr k)
  simp [blockMat, hk, Matrix.scalar_apply] at h1 h2 h3 h4 h5
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4, h5]

theorem neg_one_inv_SL2 : (-1 : SL(2, F))⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by simp))

theorem sq_neg_one_of_center_same (k : Fin 2) {A : SL(2, F)}
    (h : longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F)) : (A : Matrix (Fin 2) (Fin 2) F) * A = -1 := by
  have e : longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹ =
      longBlock F 2 k (A * A * (-1)⁻¹) := by
    rw [longInv, ← map_inv, ← map_mul, ← map_mul]
  rw [e] at h
  have h1 := eq_one_of_longBlock_mem_center k h
  rw [neg_one_inv_SL2] at h1
  have h2 := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, mul_neg_one] at h2
  simpa [neg_eq_iff_eq_neg] using h2

theorem sq_neg_one_of_center_other (k : Fin 2) {A : SL(2, F)}
    (h : longBlock F 2 (Fin.rev k) A * longBlock F 2 (Fin.rev k) A * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F)) : (A : Matrix (Fin 2) (Fin 2) F) * A = -1 := by
  obtain ⟨r, hr⟩ := mat_scalar_of_mem_center h
  have hinv : (longInv F 2 k)⁻¹ = longInv F 2 k := by
    rw [longInv, ← map_inv, neg_one_inv_SL2]
  rw [hinv, map_mul, map_mul, longInv, mat_longBlock, mat_longBlock] at hr
  have e := fun a b => congrFun (congrFun hr a) b
  fin_cases k
  · have h1 := e (Sum.inl 0) (Sum.inl 0)
    have h2 := e (Sum.inl 1) (Sum.inl 1)
    have h3 := e (Sum.inl 1) (Sum.inr 1)
    have h4 := e (Sum.inr 1) (Sum.inl 1)
    have h5 := e (Sum.inr 1) (Sum.inr 1)
    simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.scalar_apply, Fin.rev] at h1 h2 h3 h4 h5
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h2 - h1
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5 - h1
  · have h1 := e (Sum.inl 1) (Sum.inl 1)
    have h2 := e (Sum.inl 0) (Sum.inl 0)
    have h3 := e (Sum.inl 0) (Sum.inr 0)
    have h4 := e (Sum.inr 0) (Sum.inl 0)
    have h5 := e (Sum.inr 0) (Sum.inr 0)
    simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.scalar_apply, Fin.rev] at h1 h2 h3 h4 h5
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h2 - h1
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5 - h1

theorem centralizer_eq_of_mat_neg {y₁ y₂ : StatedSp 2 F} (h : mat 2 F y₂ = -mat 2 F y₁) :
    Subgroup.centralizer ({y₂} : Set (StatedSp 2 F)) =
      Subgroup.centralizer ({y₁} : Set (StatedSp 2 F)) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    apply mat_injective
    have := congrArg (mat 2 F) hg
    rw [map_mul, map_mul, h] at this
    rw [map_mul, map_mul]
    simpa using this
  · intro hg
    apply mat_injective
    have := congrArg (mat 2 F) hg
    rw [map_mul, map_mul] at this
    rw [map_mul, map_mul, h]
    simp [this]

theorem sp4_core [Finite F] (h2 : (2 : F) ≠ 0) (hcard : 3 ≤ Nat.card F) (k : Fin 2)
    (A A' : SL(2, F)) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    Subgroup.centralizer ({longInv F 2 k} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({longBlock F 2 k A * longBlock F 2 (Fin.rev k) A'} :
        Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({longInv F 2 k * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A')} :
        Set (StatedSp 2 F)) = ⊤ := by
  fin_cases k
  · have := sp4_sup_eq_top h2 hcard A A' hA hA'
    simpa [ut, phi4_apply, x0] using this
  · have := sp4_sup_eq_top h2 hcard A' A hA' hA
    have e1 : mat 2 F (longInv F 2 1) = -mat 2 F (x0 F) :=
      CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.mat_longInv_rev (F := F) 0
    have hu : longBlock F 2 1 A * longBlock F 2 (Fin.rev 1) A' = ut A' A := by
      rw [show ut A' A = longBlock F 2 0 A' * longBlock F 2 1 A from phi4_apply A' A]
      exact (commute_longBlock_01 A' A).eq.symm
    have hc1 : Subgroup.centralizer ({longInv F 2 1} : Set (StatedSp 2 F)) =
        Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := centralizer_eq_of_mat_neg e1
    have hc3 : Subgroup.centralizer ({longInv F 2 1 * ut A' A} : Set (StatedSp 2 F)) =
        Subgroup.centralizer ({x0 F * ut A' A} : Set (StatedSp 2 F)) := by
      apply centralizer_eq_of_mat_neg
      rw [map_mul, map_mul, e1, neg_mul]
    show Subgroup.centralizer ({longInv F 2 1} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({longBlock F 2 1 A * longBlock F 2 (Fin.rev 1) A'} :
        Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({longInv F 2 1 * (longBlock F 2 1 A * longBlock F 2 (Fin.rev 1) A')} :
        Set (StatedSp 2 F)) = ⊤
    rw [hu, hc1, hc3]
    exact this

theorem sp4_mul_self_eq_one_of_center {R : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) {c : StatedSp 2 F} (hc : c ∈ R)
    (hcc : ∀ r ∈ R, c * r = r * c) : c * c = 1 := by
  obtain ⟨i, k, g, hRg, -⟩ := hR
  rw [hRg] at hc hcc
  obtain ⟨y, ⟨A, rfl⟩, rfl⟩ := hc
  have hAc : ∀ B : SL(2, F), B * A = A * B := by
    intro B
    have hmem : (MulAut.conj g) (longBlock F 2 k B) ∈
        (longRootSp2 F 2 k).map (MulAut.conj g).toMonoidHom := ⟨_, ⟨B, rfl⟩, rfl⟩
    have h := hcc _ hmem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h' : longBlock F 2 k A * longBlock F 2 k B = longBlock F 2 k B * longBlock F 2 k A := by
      have h3 := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using h3
    exact (longBlock_injective k (by simpa only [map_mul] using h')).symm
  have hAz : A ∈ Subgroup.center SL(2, F) := Subgroup.mem_center_iff.mpr hAc
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAz
  have hAA : A * A = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrA, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
    have hr2 : r * r = 1 := by simpa [pow_two] using hr
    rw [hr2, map_one]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have : longBlock F 2 k A * longBlock F 2 k A = 1 := by rw [← map_mul, hAA, map_one]
  calc g * longBlock F 2 k A * g⁻¹ * (g * longBlock F 2 k A * g⁻¹) =
      g * (longBlock F 2 k A * longBlock F 2 k A) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem sp4_gen [Finite F] (h2 : (2 : F) ≠ 0) (hcard : 3 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i)
    (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {a a' : StatedSp 2 F} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) :
    Subgroup.centralizer ({x} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({a * a'} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (StatedSp 2 F)) = ⊤ := by
  have hx2 : x * x = 1 := sp4_mul_self_eq_one_of_center hR hxR hxc
  have hx'2 : x' * x' = 1 := sp4_mul_self_eq_one_of_center hR' hx'R' hx'c
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).inv_mem hsame
    simpa using this
  obtain ⟨g, k, hRg, hR'g⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2
    hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hxg : x = g * longInv F 2 k * g⁻¹ := by
    have hi : IsLongRootSp2 R (g * longInv F 2 k * g⁻¹) := by
      rw [hRg]
      exact (isLongRootSp2_standard k).conj g
    exact hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).mul_mem hsq' hc
    simpa [mul_assoc] using this
  have hA₁ : longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹) * g⁻¹ =
        a * a * x⁻¹ := by
      rw [← hae, hA, hxg]
      group
    rw [e]
    exact hsq
  have hA₂ : longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' *
        (longInv F 2 k)⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', hA', hxg]
      group
    rw [e]
    exact hsq''
  have key := sp4_core h2 hcard k A A' (sq_neg_one_of_center_same k hA₁)
    (sq_neg_one_of_center_other k hA₂)
  have hk := sup_centralizer_conj g _ _ _ key
  have e2 : a * a' = g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹ := by
    rw [← hae, ← hae', hA, hA']
    group
  have e3 : x * (a * a') = g * (longInv F 2 k * (longBlock F 2 k A *
      longBlock F 2 (Fin.rev k) A')) * g⁻¹ := by
    rw [e2, hxg]
    group
  rw [e3, e2, hxg]
  exact hk

end CFSG.ClassicalInvolution.RouteD.SCRSp4

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal

variable {p : ℕ} [Fact p.Prime]

theorem twinMFGenerationOn_psp2 (hp2 : p ≠ 2) {e : ℕ} (hq : 3 ≤ p ^ e) :
    TwinMFGenerationOn .PSp (modelUniv .PSp 2 p e Fact.out) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSp 2 p e :=
    ⟨Fact.out, he, le_refl 2, fun h => by
      have : p ^ e = 2 := congrArg Prod.snd h
      omega⟩
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hcard : 3 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    exact hq
  intro R R' x x' hd a ha a' ha' hsq hsq' S hS
  have hR := (exists_isLongRootSp2_iff h2 R).mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hd.mem)
  have hR' := (exists_isLongRootSp2_iff h2 R').mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hd.mem')
  have key := CFSG.ClassicalInvolution.RouteD.SCRSp4.sp4_gen h2 hcard hR hR' hd.ne hd.hx hd.cx
    hd.nx hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq'
  exact le_top.trans key.symm.le

theorem twinMFGeneration_psp2 (hp2 : p ≠ 2) {e : ℕ} (hq : 3 ≤ p ^ e) :
    TwinMFGeneration p e .PSp 2 :=
  twinMFGeneration_of_on (twinMFGenerationOn_psp2 hp2 hq)

end CFSG.ClassicalInvolution.RouteD.TwinY
