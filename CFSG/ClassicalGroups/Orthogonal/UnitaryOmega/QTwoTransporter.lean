module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoRootBlocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankSiegel

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.ClassicalGroups.Orthogonal.OmegaSiegel CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {ω : K} (hω : IsTraceNormOne E ω)

@[expose] noncomputable def qTwoYCast : normOmega E 4 :=
  normOmegaCast E (Nat.le_succ 3) (qTwoY E hω)

private theorem qTwoYCast_coe :
    Subtype.val (qTwoYCast E hω) = castEquiv (Nat.le_succ 3) (qTwoYLin E ω) := by
  rw [qTwoYCast, normOmegaCast_apply]
  rfl

private theorem polar_normQuad_self (x : K) : polar (normQuad E) x x = 0 := by
  have h2 : (2 : F) = 0 := by
    apply (algebraMap F K).injective
    rw [map_ofNat, map_zero]
    exact CharP.cast_eq_zero K 2
  rw [polar_self_eq_two_mul, h2, zero_mul]

private theorem polar_Qn_pi_single {m : ℕ} (i j : Fin m) (x y : K) :
    polar (Qn E m) (Pi.single i x) (Pi.single j y) =
      if i = j then polar (normQuad E) x y else 0 := by
  rw [polar_Qn]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  · rw [if_neg h, Finset.sum_eq_zero]
    intro b _
    by_cases hb : b = i
    · subst b
      simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hb]

private theorem polar_normPlaneVec_normPlaneVec {m : ℕ} (i j : Fin m) (x y : K) :
    polar (normHypForm E m) (normPlaneVec F i x) (normPlaneVec F j y) =
      if i = j then polar (normQuad E) x y else 0 := by
  rw [normHypForm, polar_hypSum]
  simp only [normPlaneVec]
  rw [polar_Qn_pi_single]
  simp

private theorem normHypForm_normPlaneVec {m : ℕ} (i : Fin m) (x : K) :
    normHypForm E m (normPlaneVec F i x) = normQuad E x := by
  rw [normHypForm, hypSum_apply, Qn_apply, Finset.sum_eq_single i]
  · simp [normPlaneVec]
  · intro b _ hb
    simp [normPlaneVec, Pi.single_eq_of_ne hb]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

private theorem normHypForm_normWVec {m : ℕ} (s : Bool) :
    normHypForm E m (normWVec K m s) = 0 := by
  cases s <;> simp [normHypForm, normWVec, hypSum_apply, Qn_apply]

private theorem polar_normWVec_normWVec {m : ℕ} (s t : Bool) :
    polar (normHypForm E m) (normWVec K m s) (normWVec K m t) =
      if s = t then 0 else 1 := by
  cases s <;> cases t <;>
    simp [normHypForm, normWVec, polar_hypSum, hypSum_apply, Qn_apply]

private theorem polar_normWVec_normPlaneVec {m : ℕ} (s : Bool) (i : Fin m) (x : K) :
    polar (normHypForm E m) (normWVec K m s) (normPlaneVec F i x) = 0 := by
  cases s <;> simp [normHypForm, normWVec, normPlaneVec, polar_hypSum]

private theorem castLin_apply_eq_self {k m : ℕ} (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin m → K))
    (hv : g (castRestr h v) = castRestr h v) : castLin h g v = v := by
  rw [castLin_apply, hv]
  refine Prod.ext rfl (funext fun j => ?_)
  change (if hj : (j : ℕ) < k then
    (castRestr h v).2 ⟨(j : ℕ), hj⟩ else v.2 j) = v.2 j
  by_cases hj : (j : ℕ) < k
  · rw [dif_pos hj]
    rfl
  · rw [dif_neg hj]

include hω in
private theorem qTwoYLin_e1 :
    (qTwoYLin E ω) (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω) =
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω := by
  have hω1 : polar (normQuad E) ω 1 = 1 := by rw [polar_comm, hω.1]
  have hωω : polar (normQuad E) ω (1 + ω) = 1 := by
    rw [polar_add_right, polar_normQuad_self, hω1, add_zero]
  have h1ω : polar (normQuad E) (1 + ω) ω = 1 := by rw [polar_comm, hωω]
  have h11 : polar (normQuad E) (1 + ω) 1 = 1 := by
    rw [polar_add_left, polar_normQuad_self, zero_add, hω1]
  have h2 : (2 : F) = 0 := by
    apply (algebraMap F K).injective
    rw [map_ofNat, map_zero]
    exact CharP.cast_eq_zero K 2
  have hone : (1 : F) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
  rw [qTwoYLin]
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · simp only [polar_add_left, polar_add_right, polar_normPlaneVec_normPlaneVec,
      h1ω, h11]
    simp [hone]
  · simp only [polar_add_left, polar_add_right, polar_normPlaneVec_normPlaneVec,
      hω1, h1ω, h11]
    simp [hone]

include hω in
private theorem qTwoYLin_f1 :
    (qTwoYLin E ω) (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)) =
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω) := by
  have hω1 : polar (normQuad E) ω 1 = 1 := by rw [polar_comm, hω.1]
  have hωω : polar (normQuad E) ω (1 + ω) = 1 := by
    rw [polar_add_right, polar_normQuad_self, hω1, add_zero]
  have h1ω : polar (normQuad E) (1 + ω) ω = 1 := by rw [polar_comm, hωω]
  have h11 : polar (normQuad E) (1 + ω) 1 = 1 := by
    rw [polar_add_left, polar_normQuad_self, zero_add, hω1]
  have h2 : (2 : F) = 0 := by
    apply (algebraMap F K).injective
    rw [map_ofNat, map_zero]
    exact CharP.cast_eq_zero K 2
  have hone : (1 : F) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
  rw [qTwoYLin]
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · simp only [polar_add_left, polar_add_right, polar_normPlaneVec_normPlaneVec,
      h1ω, h11]
    simp [hone]
  · simp only [polar_add_left, polar_add_right, polar_normPlaneVec_normPlaneVec,
      h1ω, h11]
    simp [hone]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_qTwoVec_one_true :
    castRestr (Nat.le_succ 3) (qTwoVec F ω 1 true) =
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω := by
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;> simp [qTwoVec, castRestr, normPlaneVec]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_qTwoVec_one_false :
    castRestr (Nat.le_succ 3) (qTwoVec F ω 1 false) =
      normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω) := by
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;> simp [qTwoVec, castRestr, normPlaneVec]

private theorem qTwoYCast_qTwoVec_one_true :
    Subtype.val (qTwoYCast E hω) (qTwoVec F ω 1 true) = qTwoVec F ω 1 true := by
  rw [qTwoYCast_coe, castEquiv_apply]
  apply castLin_apply_eq_self
  rw [castRestr_qTwoVec_one_true]
  exact qTwoYLin_e1 E hω

private theorem qTwoYCast_qTwoVec_one_false :
    Subtype.val (qTwoYCast E hω) (qTwoVec F ω 1 false) = qTwoVec F ω 1 false := by
  rw [qTwoYCast_coe, castEquiv_apply]
  apply castLin_apply_eq_self
  rw [castRestr_qTwoVec_one_false]
  exact qTwoYLin_f1 E hω

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_normWVec (s : Bool) :
    castRestr (F := F) (K := K) (Nat.le_succ 3) (normWVec K 4 s) = normWVec K 3 s := by
  cases s <;> rfl

private theorem qTwoYCast_normWVec (s : Bool) :
    Subtype.val (qTwoYCast E hω) (normWVec K 4 s) = normWVec K 4 s := by
  rw [qTwoYCast_coe, castEquiv_apply]
  apply castLin_apply_eq_self
  show (qTwoYLin E ω) (castRestr (Nat.le_succ 3) (normWVec K 4 s)) =
    castRestr (Nat.le_succ 3) (normWVec K 4 s)
  rw [castRestr_normWVec]
  exact qTwoYLin_wVec E ω s

private theorem qTwoYCast_qTwoVec_two (s : Bool) :
    Subtype.val (qTwoYCast E hω) (qTwoVec F ω 2 s) = qTwoVec F ω 2 s := by
  cases s
  · simpa [qTwoVec] using qTwoYCast_normWVec (E := E) (hω := hω) false
  · simpa [qTwoVec] using qTwoYCast_normWVec (E := E) (hω := hω) true

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_normPlaneVec_two :
    castRestr (F := F) (K := K) (Nat.le_succ 3) (normPlaneVec F (2 : Fin 4) 1) =
      normPlaneVec F (2 : Fin 3) 1 := by
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;> simp [castRestr, normPlaneVec]

private theorem qTwoYCast_planeVec_two :
    Subtype.val (qTwoYCast E hω) (normPlaneVec F 2 1) = normPlaneVec F 0 (1 + ω) := by
  have happ : (↑(qTwoYLin E ω) :
      ((F × F) × (Fin 3 → K)) →ₗ[F] ((F × F) × (Fin 3 → K)))
      (normPlaneVec F 2 1) = normPlaneVec F 0 (1 + ω) :=
    qTwoYLin_planeVec_two E hω
  rw [qTwoYCast_coe, castEquiv_apply, castLin_apply, castRestr_normPlaneVec_two, happ]
  refine Prod.ext ?_ (funext fun j => ?_)
  · rfl
  · fin_cases j <;> simp [normPlaneVec]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_normPlaneVec_three (x : K) :
    castRestr (F := F) (K := K) (Nat.le_succ 3) (normPlaneVec F (3 : Fin 4) x) = 0 := by
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;> simp [castRestr, normPlaneVec]

private theorem qTwoYCast_planeVec_three (x : K) :
    Subtype.val (qTwoYCast E hω) (normPlaneVec F 3 x) = normPlaneVec F 3 x := by
  rw [qTwoYCast_coe, castEquiv_apply]
  apply castLin_apply_eq_self
  rw [castRestr_normPlaneVec_three]
  simp

include hω in
private theorem q4_qTwoVec (i : Fin 5) (s : Bool) :
    normHypForm E 4 (qTwoVec F ω i s) = 0 :=
  (qTwoFrame hω).map_vec i s

include hω in
private theorem q4_polar_qTwoVec_of_ne {i j : Fin 5} (hij : i ≠ j) (s t : Bool) :
    polar (normHypForm E 4) (qTwoVec F ω i s) (qTwoVec F ω j t) = 0 :=
  (qTwoFrame hω).polar_vec_of_ne hij s t

private theorem polar_qTwoVec_two_normPlaneVec (s : Bool) (i : Fin 4) (x : K) :
    polar (normHypForm E 4) (qTwoVec F ω 2 s) (normPlaneVec F i x) = 0 := by
  cases s <;> simp [qTwoVec, polar_normWVec_normPlaneVec]

include hω in
private theorem eichler_f3_c_e2 (c : F) :
    eichler (normHypForm E 4) (qTwoVec F ω 3 false) (c • qTwoVec F ω 2 true) =
      eichler (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 3 ω) *
        eichler (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 2 1) := by
  have hf3 : qTwoVec F ω 3 false = normPlaneVec F 3 ω + normPlaneVec F 2 1 := by
    simp [qTwoVec]
  have hchar : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hQf3 : normHypForm E 4 (qTwoVec F ω 3 false) = 0 :=
    q4_qTwoVec (E := E) (hω := hω) 3 false
  have hQe2 : normHypForm E 4 (qTwoVec F ω 2 true) = 0 :=
    q4_qTwoVec (E := E) (hω := hω) 2 true
  have hpol : polar (normHypForm E 4) (qTwoVec F ω 3 false) (qTwoVec F ω 2 true) = 0 :=
    q4_polar_qTwoVec_of_ne (E := E) (hω := hω) (by decide) false true
  have hQcf3 : normHypForm E 4 (c • qTwoVec F ω 3 false) = 0 := by
    rw [map_smul_eq_sq, hQf3, mul_zero]
  have hpolc : polar (normHypForm E 4) (c • qTwoVec F ω 3 false)
      (qTwoVec F ω 2 true) = 0 := by
    rw [polar_smul_left_eq, hpol, mul_zero]
  have hp1 : polar (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 3 ω) = 0 := by
    rw [polar_smul_right_eq, polar_qTwoVec_two_normPlaneVec, mul_zero]
  have hp2 : polar (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 2 1) = 0 := by
    rw [polar_smul_right_eq, polar_qTwoVec_two_normPlaneVec, mul_zero]
  calc
    eichler (normHypForm E 4) (qTwoVec F ω 3 false) (c • qTwoVec F ω 2 true)
        = eichler (normHypForm E 4) (c • qTwoVec F ω 3 false)
            (qTwoVec F ω 2 true) :=
          (eichler_smul_left c (qTwoVec F ω 3 false) (qTwoVec F ω 2 true)).symm
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 true)
          (c • qTwoVec F ω 3 false) :=
          @eichler_comm_of_singular F _ hchar ((F × F) × (Fin 4 → K)) _ _ (normHypForm E 4)
            (c • qTwoVec F ω 3 false) (qTwoVec F ω 2 true) hQcf3 hQe2 hpolc
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 true)
          (c • (normPlaneVec F 3 ω + normPlaneVec F 2 1)) := by rw [hf3]
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 true)
          (c • normPlaneVec F 3 ω + c • normPlaneVec F 2 1) := by rw [smul_add]
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 3 ω) *
          eichler (normHypForm E 4) (qTwoVec F ω 2 true) (c • normPlaneVec F 2 1) :=
          (eichler_mul hp1 hp2).symm

private theorem eichler_f2_c_e3 (c : F) :
    eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • qTwoVec F ω 3 true) =
      eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 3 1) *
        eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 2 1) := by
  have he3 : qTwoVec F ω 3 true = normPlaneVec F 3 1 + normPlaneVec F 2 1 := by
    simp [qTwoVec]
  have hp1 : polar (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 3 1) = 0 := by
    rw [polar_smul_right_eq, polar_qTwoVec_two_normPlaneVec, mul_zero]
  have hp2 : polar (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 2 1) = 0 := by
    rw [polar_smul_right_eq, polar_qTwoVec_two_normPlaneVec, mul_zero]
  calc
    eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • qTwoVec F ω 3 true)
        = eichler (normHypForm E 4) (qTwoVec F ω 2 false)
            (c • (normPlaneVec F 3 1 + normPlaneVec F 2 1)) := by rw [he3]
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 false)
          (c • normPlaneVec F 3 1 + c • normPlaneVec F 2 1) := by rw [smul_add]
    _ = eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 3 1) *
          eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • normPlaneVec F 2 1) :=
          (eichler_mul hp1 hp2).symm

include hω in
private theorem normQuad_one_add_omega : normQuad E (1 + ω) = 1 := by
  have hmap : normQuad E (1 + ω) =
      normQuad E 1 + normQuad E ω + polar (normQuad E) 1 ω := by
    rw [QuadraticMap.map_add (normQuad E)]
  have h2 : (2 : F) = 0 := by
    apply (algebraMap F K).injective
    rw [map_ofNat, map_zero]
    exact CharP.cast_eq_zero K 2
  have hone : (1 : F) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
  rw [hmap, normQuad_one, hω.2, hω.1, add_assoc, hone, add_zero]

private theorem exists_mem_normBlock_eichler {k : Fin 4} {s : Bool} {x y : K} {c : F}
    (hQx : normQuad E x ≠ 0) (hxy : polar (normQuad E) x y = normQuad E x)
    (hc : c ≠ 0) :
    ∃ g : normOmega E 4, g ∈ normBlock E 4 {k} ∧
      Subtype.val g =
        eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x) := by
  have hchar : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have hW : normWVec K 4 s ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))
      {k} := by
    rw [mem_coordSupport_refl_iff E (S := {k})]
    intro j _
    cases s <;> simp [normWVec]
  have hA : c • normPlaneVec F k x ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))
      {k} := by
    rw [mem_coordSupport_refl_iff E (S := {k})]
    intro j hj
    have hjk : j ≠ k := by
      intro h
      exact hj (by simp [h])
    simp [normPlaneVec, Pi.single_eq_of_ne hjk]
  have hB : c • normPlaneVec F k y ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))
      {k} := by
    rw [mem_coordSupport_refl_iff E (S := {k})]
    intro j hj
    have hjk : j ≠ k := by
      intro h
      exact hj (by simp [h])
    simp [normPlaneVec, Pi.single_eq_of_ne hjk]
  have hQa : normHypForm E 4 (c • normPlaneVec F k x) ≠ 0 := by
    rw [map_smul_eq_sq, normHypForm_normPlaneVec]
    exact mul_ne_zero (pow_ne_zero 2 hc) hQx
  have heA : polar (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x) = 0 := by
    rw [polar_smul_right_eq, polar_normWVec_normPlaneVec, mul_zero]
  have heB : polar (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k y) = 0 := by
    rw [polar_smul_right_eq, polar_normWVec_normPlaneVec, mul_zero]
  have hTxy : polar (normHypForm E 4) (c • normPlaneVec F k x) (c • normPlaneVec F k y) =
      normHypForm E 4 (c • normPlaneVec F k x) := by
    rw [polar_smul_left_eq, polar_smul_right_eq, polar_normPlaneVec_normPlaneVec,
      if_pos rfl, hxy, map_smul_eq_sq, normHypForm_normPlaneVec]
    ring_nf
  have hmemΩ : eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x) ∈
      normOmega E 4 :=
    @eichler_mem_orthDerived F _ hchar ((F × F) × (Fin 4 → K)) _ _ (normHypForm E 4)
      (normWVec K 4 s) (c • normPlaneVec F k x) (c • normPlaneVec F k y) hQa heA heB hTxy
  have hrel : eichler ((normHypForm E 4).comp
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {k}).subtype)
      ⟨normWVec K 4 s, hW⟩ ⟨c • normPlaneVec F k x, hA⟩ ∈
      orthDerived ((normHypForm E 4).comp
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {k}).subtype) := by
    refine @eichler_mem_orthDerived F _ hchar
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {k}) _ _
      ((normHypForm E 4).comp
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {k}).subtype)
      ⟨normWVec K 4 s, hW⟩ ⟨c • normPlaneVec F k x, hA⟩
      ⟨c • normPlaneVec F k y, hB⟩ ?_ ?_ ?_ ?_
    · change normHypForm E 4 (c • normPlaneVec F k x) ≠ 0
      exact hQa
    · rw [polar_comp_subtype_eq]
      exact heA
    · rw [polar_comp_subtype_eq]
      exact heB
    · rw [polar_comp_subtype_eq]
      change polar (normHypForm E 4) (c • normPlaneVec F k x) (c • normPlaneVec F k y) =
        normHypForm E 4 (c • normPlaneVec F k x)
      exact hTxy
  have hmemSD : eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x) ∈
      supportedDerived (normHypForm E 4)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {k}) :=
    eichler_mem_supportedDerived hW hA (normHypForm_normWVec (E := E) s) heA hrel
  refine ⟨⟨eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x), hmemΩ⟩,
    ?_, rfl⟩
  rw [normBlock, Subgroup.mem_subgroupOf]
  exact hmemSD

private theorem mem_normBlock_of_coe_eichler {k : Fin 4} {s : Bool} {x y : K} {c : F}
    (hQx : normQuad E x ≠ 0) (hxy : polar (normQuad E) x y = normQuad E x)
    (hc : c ≠ 0) {g : normOmega E 4}
    (hg : Subtype.val g =
      eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F k x)) :
    g ∈ normBlock E 4 {k} := by
  obtain ⟨h, hhmem, hhcoe⟩ := exists_mem_normBlock_eichler (E := E)
    (k := k) (s := s) (x := x) (y := y) (c := c) hQx hxy hc
  have hgh : g = h := Subtype.ext (hg.trans hhcoe.symm)
  rwa [hgh]

private theorem coe_conj_eichler_normW {s : Bool} {c : F} {g : normOmega E 4}
    (hg : Subtype.val g =
      eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F 2 1)) :
    Subtype.val (qTwoYCast E hω * g * (qTwoYCast E hω)⁻¹) =
      eichler (normHypForm E 4) (normWVec K 4 s) (c • normPlaneVec F 0 (1 + ω)) := by
  have hyO : Subtype.val (qTwoYCast E hω) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4) :=
    orthDerived_le_orthogonalGroup_of_commutator (normHypForm E 4) (qTwoYCast E hω).2
  have hcoe : Subtype.val (qTwoYCast E hω * g * (qTwoYCast E hω)⁻¹) =
      Subtype.val (qTwoYCast E hω) * Subtype.val g *
        (Subtype.val (qTwoYCast E hω))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, hg, eichler_conj hyO]
  congr 1
  · exact qTwoYCast_normWVec (E := E) (hω := hω) s
  · rw [map_smul, qTwoYCast_planeVec_two]

private theorem commute_of_eichler_fixed {a b : (F × F) × (Fin 4 → K)}
    (ha : Subtype.val (qTwoYCast E hω) a = a) (hb : Subtype.val (qTwoYCast E hω) b = b)
    {x : normOmega E 4}
    (hx : Subtype.val x =
      eichler (normHypForm E 4) a b) :
    Commute (qTwoYCast E hω) x := by
  have hyO : Subtype.val (qTwoYCast E hω) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4) :=
    orthDerived_le_orthogonalGroup_of_commutator (normHypForm E 4) (qTwoYCast E hω).2
  have hconj : Subtype.val (qTwoYCast E hω) *
        Subtype.val x *
        (Subtype.val (qTwoYCast E hω))⁻¹ =
      Subtype.val x := by
    rw [hx, eichler_conj hyO, ha, hb]
  have hsub : qTwoYCast E hω * x * (qTwoYCast E hω)⁻¹ = x := Subtype.ext hconj
  show qTwoYCast E hω * x = x * qTwoYCast E hω
  calc
    qTwoYCast E hω * x =
        (qTwoYCast E hω * x * (qTwoYCast E hω)⁻¹) * qTwoYCast E hω := by group
    _ = x * qTwoYCast E hω := by rw [hsub]

private theorem coe_symm_rootD_one (c : F) :
    Subtype.val ((qTwoLambda E hω).symm (rootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • qTwoVec F ω 1 true) := by
  simpa [rootD, rootIdxD, rootIdxD', rootSignD, qTwoVec, normWVec, normPlaneVec]
    using coe_qTwoLambda_symm_longRoot (E := E) (hω := hω) (i := 1) (j := 2)
      (by norm_num) true false c

private theorem coe_symm_negRootD_one (c : F) :
    Subtype.val ((qTwoLambda E hω).symm (negRootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 1 false) (c • qTwoVec F ω 2 true) := by
  simpa [negRootD, rootIdxD, rootIdxD', rootSignD, qTwoVec, normWVec, normPlaneVec]
    using coe_qTwoLambda_symm_longRoot (E := E) (hω := hω) (i := 2) (j := 1)
      (by norm_num) true false c

private theorem commute_qTwoYCast_rootD_one (c : F) :
    Commute (qTwoYCast E hω)
      ((qTwoLambda E hω).symm (rootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) := by
  have hx : Subtype.val ((qTwoLambda E hω).symm (rootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • qTwoVec F ω 1 true) :=
    coe_symm_rootD_one E hω c
  refine commute_of_eichler_fixed (E := E) (hω := hω) (a := qTwoVec F ω 2 false)
    (b := c • qTwoVec F ω 1 true) ?_ ?_ hx
  · exact qTwoYCast_qTwoVec_two (E := E) (hω := hω) false
  · rw [map_smul, qTwoYCast_qTwoVec_one_true]

private theorem commute_qTwoYCast_negRootD_one (c : F) :
    Commute (qTwoYCast E hω)
      ((qTwoLambda E hω).symm (negRootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) := by
  have hx : Subtype.val ((qTwoLambda E hω).symm (negRootD F (by norm_num) (1 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 1 false) (c • qTwoVec F ω 2 true) :=
    coe_symm_negRootD_one E hω c
  refine commute_of_eichler_fixed (E := E) (hω := hω) (a := qTwoVec F ω 1 false)
    (b := c • qTwoVec F ω 2 true) ?_ ?_ hx
  · exact qTwoYCast_qTwoVec_one_false (E := E) (hω := hω)
  · rw [map_smul, qTwoYCast_qTwoVec_two]

private theorem coe_symm_rootD_two (c : F) :
    Subtype.val ((qTwoLambda E hω).symm (rootD F (by norm_num) (2 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 3 false) (c • qTwoVec F ω 2 true) := by
  simpa [rootD, rootIdxD, rootIdxD', rootSignD, qTwoVec, normWVec, normPlaneVec]
    using coe_qTwoLambda_symm_longRoot (E := E) (hω := hω) (i := 2) (j := 3)
      (by norm_num) true false c

private theorem coe_symm_negRootD_two (c : F) :
    Subtype.val ((qTwoLambda E hω).symm (negRootD F (by norm_num) (2 : Fin 5) (.ofAdd c))) =
      eichler (normHypForm E 4) (qTwoVec F ω 2 false) (c • qTwoVec F ω 3 true) := by
  simpa [negRootD, rootIdxD, rootIdxD', rootSignD, qTwoVec, normWVec, normPlaneVec]
    using coe_qTwoLambda_symm_longRoot (E := E) (hω := hω) (i := 3) (j := 2)
      (by norm_num) true false c

theorem commute_qTwoYCast_map_rankOne_one :
    ∀ x ∈ (rankOne (plusRootGroup 5 F (by norm_num)) 1).map (qTwoLambda E hω).symm.toMonoidHom,
      Commute (qTwoYCast E hω) x := by
  have hle : (rankOne (plusRootGroup 5 F (by norm_num)) 1).map
      (qTwoLambda E hω).symm.toMonoidHom ≤
      Subgroup.centralizer ({qTwoYCast E hω} : Set (normOmega E 4)) := by
    rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) (1 : Fin 5), Subgroup.map_sup,
      MonoidHom.map_range, MonoidHom.map_range]
    apply sup_le
    · rintro x ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := (commute_qTwoYCast_rootD_one (E := E) (hω := hω)
        (Multiplicative.toAdd c)).symm
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at h
      exact h
    · rintro x ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := (commute_qTwoYCast_negRootD_one (E := E) (hω := hω)
        (Multiplicative.toAdd c)).symm
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at h
      exact h
  intro x hx
  exact (hle hx) (qTwoYCast E hω) (by simp)

theorem exists_factor_rootD_two (c : F) :
    ∃ g₁ ∈ normBlock E 4 {3}, ∃ g₂ ∈ normBlock E 4 {2},
      (qTwoLambda E hω).symm (rootD F (by norm_num) 2 (.ofAdd c)) = g₁ * g₂ ∧
        Commute (qTwoYCast E hω) g₁ ∧
        qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹ ∈ normBlock E 4 {0} := by
  by_cases hc : c = 0
  · subst hc
    refine ⟨1, (normBlock E 4 {3}).one_mem, 1, (normBlock E 4 {2}).one_mem, ?_, ?_, ?_⟩
    · change (qTwoLambda E hω).symm
        (rootD F (by norm_num) 2 (1 : Multiplicative F)) = 1 * 1
      rw [map_one, map_one, one_mul]
    · simp
    · simp
  ·
    have hQω : normQuad E ω ≠ 0 := by rw [hω.2]; exact one_ne_zero
    have hTω : polar (normQuad E) ω (1 + ω) = 1 := by
      rw [polar_add_right, polar_normQuad_self, add_zero, polar_comm, hω.1]
    have hxyω : polar (normQuad E) ω (1 + ω) = normQuad E ω := by rw [hTω, hω.2]
    have hQ1 : normQuad E 1 ≠ 0 := by rw [normQuad_one]; exact one_ne_zero
    have hxy1 : polar (normQuad E) 1 ω = normQuad E 1 := by rw [hω.1, normQuad_one]
    have hN1ω : normQuad E (1 + ω) = 1 := normQuad_one_add_omega E hω
    have hQ1ω : normQuad E (1 + ω) ≠ 0 := by rw [hN1ω]; exact one_ne_zero
    have hT1ω : polar (normQuad E) (1 + ω) ω = 1 := by
      rw [polar_add_left, polar_normQuad_self, add_zero, hω.1]
    have hxy1ω : polar (normQuad E) (1 + ω) ω = normQuad E (1 + ω) := by
      rw [hT1ω, hN1ω]
    obtain ⟨g₁, hg₁mem, hg₁coe⟩ := exists_mem_normBlock_eichler (E := E)
      (k := 3) (s := true) (x := ω) (y := 1 + ω) (c := c) hQω hxyω hc
    obtain ⟨g₂, hg₂mem, hg₂coe⟩ := exists_mem_normBlock_eichler (E := E)
      (k := 2) (s := true) (x := 1) (y := ω) (c := c) hQ1 hxy1 hc
    have hW : normWVec K 4 true = qTwoVec F ω 2 true := by simp [qTwoVec]
    refine ⟨g₁, hg₁mem, g₂, hg₂mem, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [coe_symm_rootD_two (E := E) (hω := hω), Subgroup.coe_mul, hg₁coe, hg₂coe, hW]
      exact eichler_f3_c_e2 E hω c
    · refine commute_of_eichler_fixed (E := E) (hω := hω) (a := normWVec K 4 true)
        (b := c • normPlaneVec F 3 ω)
        (qTwoYCast_normWVec (E := E) (hω := hω) true) ?_ hg₁coe
      rw [map_smul, qTwoYCast_planeVec_three]
    · have hconj := coe_conj_eichler_normW (E := E) (hω := hω) (s := true) (c := c)
        (g := g₂) hg₂coe
      exact mem_normBlock_of_coe_eichler (E := E) (k := 0) (s := true) (x := 1 + ω)
        (y := ω) (c := c) hQ1ω hxy1ω hc hconj

theorem exists_factor_negRootD_two (c : F) :
    ∃ g₁ ∈ normBlock E 4 {3}, ∃ g₂ ∈ normBlock E 4 {2},
      (qTwoLambda E hω).symm (negRootD F (by norm_num) 2 (.ofAdd c)) = g₁ * g₂ ∧
        Commute (qTwoYCast E hω) g₁ ∧
        qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹ ∈ normBlock E 4 {0} := by
  by_cases hc : c = 0
  · subst hc
    refine ⟨1, (normBlock E 4 {3}).one_mem, 1, (normBlock E 4 {2}).one_mem, ?_, ?_, ?_⟩
    · change (qTwoLambda E hω).symm
        (negRootD F (by norm_num) 2 (1 : Multiplicative F)) = 1 * 1
      rw [map_one, map_one, one_mul]
    · simp
    · simp
  ·
    have hQ1 : normQuad E 1 ≠ 0 := by rw [normQuad_one]; exact one_ne_zero
    have hxy1 : polar (normQuad E) 1 ω = normQuad E 1 := by rw [hω.1, normQuad_one]
    have hN1ω : normQuad E (1 + ω) = 1 := normQuad_one_add_omega E hω
    have hQ1ω : normQuad E (1 + ω) ≠ 0 := by rw [hN1ω]; exact one_ne_zero
    have hT1ω : polar (normQuad E) (1 + ω) ω = 1 := by
      rw [polar_add_left, polar_normQuad_self, add_zero, hω.1]
    have hxy1ω : polar (normQuad E) (1 + ω) ω = normQuad E (1 + ω) := by
      rw [hT1ω, hN1ω]
    obtain ⟨g₁, hg₁mem, hg₁coe⟩ := exists_mem_normBlock_eichler (E := E)
      (k := 3) (s := false) (x := 1) (y := ω) (c := c) hQ1 hxy1 hc
    obtain ⟨g₂, hg₂mem, hg₂coe⟩ := exists_mem_normBlock_eichler (E := E)
      (k := 2) (s := false) (x := 1) (y := ω) (c := c) hQ1 hxy1 hc
    have hW : normWVec K 4 false = qTwoVec F ω 2 false := by simp [qTwoVec]
    refine ⟨g₁, hg₁mem, g₂, hg₂mem, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [coe_symm_negRootD_two (E := E) (hω := hω), Subgroup.coe_mul, hg₁coe, hg₂coe, hW]
      exact eichler_f2_c_e3 E c
    · refine commute_of_eichler_fixed (E := E) (hω := hω) (a := normWVec K 4 false)
        (b := c • normPlaneVec F 3 1)
        (qTwoYCast_normWVec (E := E) (hω := hω) false) ?_ hg₁coe
      rw [map_smul, qTwoYCast_planeVec_three]
    · have hconj := coe_conj_eichler_normW (E := E) (hω := hω) (s := false) (c := c)
        (g := g₂) hg₂coe
      exact mem_normBlock_of_coe_eichler (E := E) (k := 0) (s := false) (x := 1 + ω)
        (y := ω) (c := c) hQ1ω hxy1ω hc hconj

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
