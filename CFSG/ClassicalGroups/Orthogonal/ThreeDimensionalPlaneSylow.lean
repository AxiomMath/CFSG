module

public import CFSG.ClassicalGroups.Orthogonal.PlaneSylow
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import CFSG.NumberTheory.OddModFour
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public noncomputable section

open Matrix QuadraticMap
open scoped Pointwise
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.ClassicalGroups.Orthogonal.PlaneSylow
open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane

namespace CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow

variable {K : Type} [Field K] [Finite K]

private def glToLinEquiv (n : Type) [Fintype n] [DecidableEq n] :
    GL n K ≃* ((n → K) ≃ₗ[K] (n → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K))

private def planeForm : QuadraticForm K (Fin 2 → K) :=
  Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) K)

private def splitCoord :
    (Fin 3 → K) ≃ₗ[K] (Fin 2 → K) × (Fin 1 → K) :=
  (LinearEquiv.funCongrLeft K K finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) K K)

private def lineForm (δ : K) : QuadraticForm K (Fin 1 → K) :=
  QuadraticMap.weightedSumSquares K (fun _ : Fin 1 => δ)

private def coordForm (δ : K) : QuadraticForm K (Fin 3 → K) :=
  (planeForm (K := K).prod (lineForm (K := K) δ)).comp splitCoord.toLinearMap

private theorem splitCoord_single_zero :
    splitCoord (K := K) (Pi.single (0 : Fin 3) 1) =
      (Pi.single (0 : Fin 2) 1, 0) := by
  have h0 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by decide
  have h1 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by decide
  have h2 : finSumFinEquiv (m := 2) (n := 1) (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by decide
  ext i <;> fin_cases i <;>
    simp [splitCoord, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single,
      h0, h1, h2]

private theorem splitCoord_single_one :
    splitCoord (K := K) (Pi.single (1 : Fin 3) 1) =
      (Pi.single (1 : Fin 2) 1, 0) := by
  have h0 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by decide
  have h1 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by decide
  have h2 : finSumFinEquiv (m := 2) (n := 1) (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by decide
  ext i <;> fin_cases i <;>
    simp [splitCoord, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single,
      h0, h1, h2]

private theorem coordForm_apply {δ : K} (x : Fin 3 → K) :
    coordForm (K := K) δ x =
      x 0 ^ 2 + x 1 ^ 2 + δ * x 2 ^ 2 := by
  have h0 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by decide
  have h1 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by decide
  have h2 : finSumFinEquiv (m := 2) (n := 1) (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by decide
  simp [coordForm, planeForm, lineForm, splitCoord, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, QuadraticMap.weightedSumSquares, QuadraticMap.prod,
    Fin.sum_univ_three, Fin.sum_univ_two, TauCeti.toQuadraticForm'_one_apply, dotProduct,
    h0, h1, h2]
  ring_nf

private def coordForm_isometry (δ : K) :
    (coordForm (K := K) δ).IsometryEquiv
      ((planeForm (K := K)).prod (lineForm (K := K) δ)) :=
  { toLinearEquiv := splitCoord
    map_app' := fun _ => rfl }

private theorem coordForm_polar_apply {δ : K} (x y : Fin 3 → K) :
    (coordForm (K := K) δ).polarBilin x y =
      2 * (x 0 * y 0 + x 1 * y 1 + δ * x 2 * y 2) := by
  rw [QuadraticMap.polarBilin_apply_apply]
  have h := QuadraticMap.map_add (coordForm (K := K) δ) x y
  rw [coordForm_apply (x + y), coordForm_apply x, coordForm_apply y] at h
  simp only [Pi.add_apply] at h
  linear_combination -h

private theorem planeBridge (h2 : (2 : K) ≠ 0) (m : O2 K) :
    glToLinEquiv (K := K) (Fin 2) (m : GL (Fin 2) K) ∈
      TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) := by
  have hm : ((m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∈
      Matrix.orthogonalGroup (Fin 2) K := by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact m.2
  change glToLinEquiv (K := K) (Fin 2) (m : GL (Fin 2) K) ∈
    TauCeti.QuadraticMap.orthogonalGroup
      (Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) K))
  rw [← TauCeti.toMatrix_mem_orthogonalGroup_iff (R := K) (n := Fin 2)
    (IsSMulRegular.of_ne_zero h2)]
  rw [show LinearMap.toMatrix'
      (glToLinEquiv (K := K) (Fin 2) (m : GL (Fin 2) K)).toLinearMap =
      (((m : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp [glToLinEquiv]]
  exact hm

private def planeToQuadratic (h2 : (2 : K) ≠ 0) :
    O2 K →* TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) :=
  (glToLinEquiv (K := K) (Fin 2)).toMonoidHom.comp (O2 K).subtype |>.codRestrict
    (TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)))
    (fun m => planeBridge (K := K) h2 m)

private theorem planeToQuadratic_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (planeToQuadratic (K := K) h2) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) =>
    (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) hab
  exact (glToLinEquiv (K := K) (Fin 2)).injective h

private def negOneO2 : O2 K :=
  ⟨(-1 : GL (Fin 2) K), by
    change (((-1 : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)ᵀ *
      (((-1 : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = 1
    simp⟩

private def negOneSub (c : GL (Fin 2) K) {r : ℕ}
    (hneg : c ^ (2 ^ (r - 1)) = -1) :
    ↥((planeSylow c).subgroupOf (O2 K)) :=
  ⟨negOneO2 (K := K), by
    rw [Subgroup.mem_subgroupOf]
    simpa [negOneO2] using neg_one_mem_planeSylow (K := K) hneg⟩

private theorem negOneO2_mem_center (c : GL (Fin 2) K) {r : ℕ}
    (hneg : c ^ (2 ^ (r - 1)) = -1) :
    negOneSub (K := K) c hneg ∈
      Subgroup.center ((planeSylow c).subgroupOf (O2 K)) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((x : O2 K) : GL (Fin 2) K) * (-1 : GL (Fin 2) K) =
    (-1 : GL (Fin 2) K) * ((x : O2 K) : GL (Fin 2) K)
  rw [mul_neg_one, neg_one_mul]

private theorem planeToQuadratic_negOne (h2 : (2 : K) ≠ 0) :
    planeToQuadratic (K := K) h2 (negOneO2 (K := K)) =
      QuadraticMap.negOrthogonal (planeForm (K := K)) := by
  apply Subtype.ext
  rw [QuadraticMap.coe_negOrthogonal]
  rw [show ((planeToQuadratic (K := K) h2 (negOneO2 (K := K)) :
      TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K))) :
      (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
      glToLinEquiv (K := K) (Fin 2) (-1 : GL (Fin 2) K) by rfl]
  rw [show glToLinEquiv (K := K) (Fin 2) (-1 : GL (Fin 2) K) = LinearEquiv.neg K by
    apply LinearEquiv.ext
    intro x
    simp [glToLinEquiv]]

private theorem lineForm_ne_zero {δ : K} (hδ : δ ≠ 0) :
    lineForm (K := K) δ ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : QuadraticForm K (Fin 1 → K) => q (Pi.single 0 1)) h
  simp [lineForm, QuadraticMap.weightedSumSquares] at h0
  exact hδ h0

variable {K : Type} [Field K] [Finite K]

private def coordWeight (δ : K) : Fin 3 → K :=
  fun i => if (i : ℕ) < 2 then 1 else δ

private theorem coordForm_eq_weighted {δ : K} :
    coordForm (K := K) δ = QuadraticMap.weightedSumSquares K (coordWeight (K := K) δ) := by
  ext x
  rw [coordForm_apply]
  simp [QuadraticMap.weightedSumSquares, coordWeight, Fin.sum_univ_three]
  ring

private theorem coordWeight_ne_zero {δ : K} (hδ : δ ≠ 0) :
    ∀ i : Fin 3, coordWeight (K := K) δ i ≠ 0 := by
  intro i
  fin_cases i <;> simp [coordWeight, hδ, one_ne_zero]

private theorem two_ne_zero_of_odd (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  letI : Fintype K := Fintype.ofFinite K
  exact CFSG.RankThree.Classical.two_ne_zero_of_card_odd (K := K) (by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd)

private theorem natCard_coordOrthogonal (hodd : Odd (Nat.card K)) {δ : K} (hδ : δ ≠ 0) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) : ℤ) =
      2 * (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd (K := K) hodd
  have hchar : ringChar K ≠ 2 := by
    intro h
    haveI : CharP K 2 := by simpa [h] using ringChar.charP K
    exact h2 (by simpa using CharP.cast_eq_zero K 2)
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  have hB : (QuadraticMap.polarBilin (coordForm (K := K) δ)).Nondegenerate := by
    rw [coordForm_eq_weighted]
    exact QuadraticMap.nondegenerate_polar_iff.mpr
      (QuadraticMap.nondegenerate_weightedSumSquares
        (fun i => isRegular_iff_ne_zero.mpr (coordWeight_ne_zero (K := K) hδ i)))
  have hdim : Module.finrank K (Fin 3 → K) = 3 := by simp
  have hraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K)
    (V := Fin 3 → K) hchar (Q := coordForm (K := K) δ) hB (n := 1) (by simpa using hdim)
  have hprod : (∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) =
      ((Nat.card K : ℤ) ^ 2 - 1) := by
    simp
  rw [hprod] at hraw
  simpa using hraw

variable {K : Type} [Field K] [Finite K]

private theorem splitCoord_zero_of_coord_zero {x : Fin 3 → K} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    splitCoord (K := K) x = (0, fun _ : Fin 1 => x 2) := by
  have hsum0 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by decide
  have hsum1 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by decide
  have hsum2 : finSumFinEquiv (m := 2) (n := 1) (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by decide
  ext i <;> fin_cases i <;>
    simp [splitCoord, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, h0, h1,
      hsum0, hsum1, hsum2]

private theorem coordForm_polar_single_left {δ : K} (h2 : (2 : K) ≠ 0) (i : Fin 3)
    (x : Fin 3 → K) :
    (coordForm (K := K) δ).polarBilin (Pi.single i 1) x =
      2 * coordWeight (K := K) δ i * x i := by
  rw [coordForm_polar_apply]
  fin_cases i <;> simp [Pi.single, coordWeight] <;> ring

private theorem coordForm_single_zero {δ : K} :
    coordForm (K := K) δ (Pi.single (0 : Fin 3) 1) = 1 := by
  rw [coordForm_apply]
  simp [Pi.single]

private theorem coordForm_single_one {δ : K} :
    coordForm (K := K) δ (Pi.single (1 : Fin 3) 1) = 1 := by
  rw [coordForm_apply]
  simp [Pi.single]

private theorem coordForm_polar_single_zero_one {δ : K} :
    (coordForm (K := K) δ).polarBilin
      (Pi.single (0 : Fin 3) 1) (Pi.single (1 : Fin 3) 1) = 0 := by
  rw [coordForm_polar_apply]
  simp [Pi.single]

private theorem coordSylow_exists (hodd : Odd (Nat.card K)) {δ : K} (hδ : δ ≠ 0) :
    ∃ (S : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)))
      (b : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)),
      b ∈ (S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) ∧
      (∀ x : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ),
        x ∈ (S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) →
        x * b = b * x) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1) = -Pi.single (0 : Fin 3) 1 ∧
      (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1) = -Pi.single (1 : Fin 3) 1 ∧
      (∀ x : Fin 3 → K,
        (coordForm (K := K) δ).polarBilin (Pi.single (0 : Fin 3) 1) x = 0 →
        (coordForm (K := K) δ).polarBilin (Pi.single (1 : Fin 3) 1) x = 0 →
        (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) x = x) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd (K := K) hodd
  let q : ℕ := Nat.card K
  obtain ⟨ε, hε, hq, m, n, _h, hm, hn, hoddn, _hq2h, _hoddh⟩ :=
    CFSG.NumberTheory.exists_sign_mod_four_odd_cofactors (q := Nat.card K) hodd
  obtain ⟨c, hcSO, hordc, hnegc, hcDle, hcardP, hcenterP, hcentmemP, hrot, hSylow⟩ :=
    CFSG.ClassicalGroups.Orthogonal.PlaneSylow.exists_planeSylow (K := K) h2 ε hε hq m hm
  let r : ℕ := padicValNat 2 m
  let m' : ℕ := m.divMaxPow 2
  have hfac : m = 2 ^ r * m' := by
    dsimp [r, m']
    exact (Nat.pow_padicValNat_mul_divMaxPow 2 m).symm
  have hmpos : 0 < m := by
    have hq2 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    have hpos : (0 : ℤ) < (m : ℤ) := by
      rcases hε with rfl | rfl <;> rw [hm] <;> omega
    exact_mod_cast hpos
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
  have hoddm' : Odd m' := by
    have hnd : ¬ 2 ∣ m' := Nat.not_dvd_divMaxPow (p := 2) (n := m) (by norm_num) hm0
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  let Dsub : Subgroup (O2 K) := (planeSylow c).subgroupOf (O2 K)
  have hDsubcard : Nat.card Dsub = 2 ^ (r + 1) := by
    dsimp [Dsub]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcDle).toEquiv, hcardP]
  let Dq : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K))) :=
    Dsub.map (planeToQuadratic (K := K) h2)
  have hDqcard : Nat.card Dq = 2 ^ (r + 1) := by
    rw [Subgroup.card_map_of_injective (planeToQuadratic_injective (K := K) h2), hDsubcard]
  let bPlane : TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) :=
    planeToQuadratic (K := K) h2 (negOneO2 (K := K))
  have hbPlaneMem : bPlane ∈ Dq := by
    refine Subgroup.mem_map.mpr ⟨negOneO2 (K := K), ?_, rfl⟩
    exact (negOneSub (K := K) c hnegc).property
  have hbPlaneCentral : ∀ x, x ∈ Dq → x * bPlane = bPlane * x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change planeToQuadratic (K := K) h2 y * planeToQuadratic (K := K) h2 (negOneO2 (K := K)) =
      planeToQuadratic (K := K) h2 (negOneO2 (K := K)) * planeToQuadratic (K := K) h2 y
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := (Subgroup.mem_center_iff.mp
      (negOneO2_mem_center (K := K) c hnegc)) ⟨y, hy⟩
    have hc' := congrArg (fun g : Dsub => (g : O2 K)) hc
    simpa [Dsub, negOneSub] using hc'
  let QL : QuadraticForm K (Fin 1 → K) := lineForm (K := K) δ
  have hdimL : Module.finrank K (Fin 1 → K) = 1 := by simp
  have hQLne : QL ≠ 0 := lineForm_ne_zero (K := K) hδ
  haveI : NeZero (2 : K) := ⟨h2⟩
  have hnegL : QuadraticMap.negOrthogonal QL ≠ 1 :=
    QuadraticMap.negOrthogonal_ne_one_of_finrank_eq_one QL hdimL
  let Lsub : Subgroup (TauCeti.QuadraticMap.orthogonalGroup QL) :=
    Subgroup.zpowers (QuadraticMap.negOrthogonal QL)
  have hLcard : Nat.card Lsub = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact QuadraticMap.negOrthogonal_mul_self QL) hnegL
  let Sprod : Subgroup
      (TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) ×
        TauCeti.QuadraticMap.orthogonalGroup QL) := Dq.prod Lsub
  have hSprodCard : Nat.card Sprod = 2 ^ (r + 1) * 2 := by
    change Nat.card ↥(Dq.prod Lsub) = 2 ^ (r + 1) * 2
    rw [Nat.card_congr (Subgroup.prodEquiv Dq Lsub).toEquiv, Nat.card_prod, hDqcard, hLcard]
  let bPair : TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) ×
      TauCeti.QuadraticMap.orthogonalGroup QL := (bPlane, 1)
  have hbPairMem : bPair ∈ Sprod := ⟨hbPlaneMem, Lsub.one_mem⟩
  have hbPairCentral : ∀ x, x ∈ Sprod → x * bPair = bPair * x := by
    rintro ⟨x1, x2⟩ ⟨hx1, hx2⟩
    apply Prod.ext
    · exact hbPlaneCentral x1 hx1
    · simp [bPair]
  let eProd := QuadraticMap.orthogonalGroupProd (planeForm (K := K)) QL
  let SprodO : Subgroup
      (TauCeti.QuadraticMap.orthogonalGroup ((planeForm (K := K)).prod QL)) :=
    Sprod.map eProd
  have hSprodOcard : Nat.card SprodO = Nat.card Sprod :=
    Subgroup.card_map_of_injective (QuadraticMap.orthogonalGroupProd_injective _ _)
  let eW := coordForm_isometry (K := K) δ
  let S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) :=
    SprodO.map (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm.toMonoidHom
  have hScard : Nat.card S = 2 ^ (r + 2) := by
    rw [Subgroup.card_map_of_injective (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm.injective,
      hSprodOcard, hSprodCard]
    calc 2 ^ (r + 1) * 2 = 2 ^ (r + 1) * 2 ^ 1 := by norm_num
      _ = 2 ^ ((r + 1) + 1) := by rw [← pow_add]
      _ = 2 ^ (r + 2) := by ring_nf
  let bProdO : TauCeti.QuadraticMap.orthogonalGroup ((planeForm (K := K)).prod QL) :=
    eProd bPair
  let bCoord : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ) :=
    (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm bProdO
  have hbProdMem : bProdO ∈ SprodO := Subgroup.mem_map.mpr ⟨bPair, hbPairMem, rfl⟩
  have hbCoordMem : bCoord ∈ S := Subgroup.mem_map.mpr ⟨bProdO, hbProdMem, rfl⟩
  have hbCoordCentral : ∀ x, x ∈ S → x * bCoord = bCoord * x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]
    change (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm (eProd z) *
        (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm (eProd bPair) =
      (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm (eProd bPair) *
        (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm (eProd z)
    rw [← (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm.map_mul (eProd z) (eProd bPair),
      ← (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm.map_mul (eProd bPair) (eProd z)]
    rw [show eProd z * eProd bPair = eProd bPair * eProd z by
      simpa using congrArg eProd (hbPairCentral z hz)]
  have hnegOneO2Sq : negOneO2 (K := K) * negOneO2 (K := K) = 1 := by
    apply Subtype.ext
    simp [negOneO2]
  have hbPlaneSq : bPlane * bPlane = 1 := by
    change planeToQuadratic (K := K) h2 (negOneO2 (K := K)) *
        planeToQuadratic (K := K) h2 (negOneO2 (K := K)) = 1
    rw [← map_mul, hnegOneO2Sq, map_one]
  have hbPairSq : bPair * bPair = 1 := by
    ext <;> simp [bPair, hbPlaneSq]
  have hbProdOSq : bProdO * bProdO = 1 := by
    change eProd bPair * eProd bPair = 1
    rw [← map_mul, hbPairSq, map_one]
  have hbCoordSq : bCoord * bCoord = 1 := by
    change (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm bProdO *
        (TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm bProdO = 1
    rw [← map_mul, hbProdOSq, map_one]
  have hbPlaneNe : bPlane ≠ 1 := by
    intro h
    have hinj := planeToQuadratic_injective (K := K) h2
    have h' : negOneO2 (K := K) = 1 := hinj (by simpa [bPlane] using h)
    have hmat := congrArg (fun g : O2 K => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h'
    simp [negOneO2] at hmat
    exact h2 (by linear_combination -hmat)
  have hbPairNe : bPair ≠ 1 := by
    intro h
    exact hbPlaneNe (congrArg Prod.fst h)
  have hbProdONe : bProdO ≠ 1 := by
    intro h
    apply hbPairNe
    apply (QuadraticMap.orthogonalGroupProd_injective (planeForm (K := K)) QL)
    simpa [bProdO, eProd] using h
  have hbCoordNe : bCoord ≠ 1 := by
    intro h
    apply hbProdONe
    have := congrArg (TauCeti.QuadraticMap.orthogonalGroupCongr eW) h
    simpa [bCoord] using this
  let u : ℕ := Nat.card K * m' * n
  have huodd : Odd u := by
    dsimp [u]
    rw [Nat.mul_assoc]
    exact hodd.mul (hoddm'.mul hoddn)
  have hOZ : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) : ℤ) =
      2 * (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
    simpa [q] using natCard_coordOrthogonal (K := K) hodd hδ
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdiff : (q : ℤ) ^ 2 - 1 = ((q : ℤ) - ε) * ((q : ℤ) + ε) := by
    have h : ((q : ℤ) - ε) * ((q : ℤ) + ε) = (q : ℤ) ^ 2 - ε ^ 2 := by ring
    rw [h, hεsq]
  have hmZ : (m : ℤ) = (2 : ℤ) ^ r * (m' : ℤ) := by
    exact_mod_cast hfac
  have hqminus : (q : ℤ) - ε = (m : ℤ) := by simpa [q] using hm.symm
  have htargetZ : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) : ℤ) =
      ((2 ^ (r + 2) * u : ℕ) : ℤ) := by
    rw [hOZ, hdiff, hqminus, hn, hmZ]
    dsimp [u]
    push_cast
    ring
  have hOcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) =
      2 ^ (r + 2) * u := Nat.cast_injective htargetZ
  have hSp : IsPGroup 2 ↥S := IsPGroup.of_card (n := r + 2) hScard
  have hpos : 0 < 2 ^ (r + 2) := pow_pos (by norm_num) _
  have hindex : S.index = u := by
    have hmul := Subgroup.index_mul_card
      (G := TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) (H := S)
    rw [hScard, hOcard] at hmul
    have hmul' : 2 ^ (r + 2) * S.index = 2 ^ (r + 2) * u := by
      rw [mul_comm (2 ^ (r + 2)) S.index]
      exact hmul
    exact Nat.eq_of_mul_eq_mul_left hpos hmul'
  have hSylowIndex : ¬ 2 ∣ S.index := by
    rw [hindex]
    exact huodd.not_two_dvd_nat
  have hbPlane_single0 :
      (bPlane : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single (0 : Fin 2) 1) =
        -Pi.single (0 : Fin 2) 1 := by
    rw [show bPlane = QuadraticMap.negOrthogonal (planeForm (K := K)) by
      exact planeToQuadratic_negOne (K := K) h2]
    rw [QuadraticMap.coe_negOrthogonal]
    simp [LinearEquiv.neg_apply]
  have hbPlane_single1 :
      (bPlane : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single (1 : Fin 2) 1) =
        -Pi.single (1 : Fin 2) 1 := by
    rw [show bPlane = QuadraticMap.negOrthogonal (planeForm (K := K)) by
      exact planeToQuadratic_negOne (K := K) h2]
    rw [QuadraticMap.coe_negOrthogonal]
    simp [LinearEquiv.neg_apply]
  have hsymm : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup ((planeForm (K := K)).prod QL))
      (x : Fin 3 → K),
      ((TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm g :
        (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) x =
      eW.symm ((g : (Fin 2 → K) × (Fin 1 → K) →ₗ[K]
        (Fin 2 → K) × (Fin 1 → K)) (eW x)) := by
    intro g x
    have h := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply eW
      ((TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm g) (eW x)
    have h' : (g : (Fin 2 → K) × (Fin 1 → K) →ₗ[K]
        (Fin 2 → K) × (Fin 1 → K)) (eW x) =
        eW (((TauCeti.QuadraticMap.orthogonalGroupCongr eW).symm g :
          (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) x) := by
      simpa using h
    simpa using (congrArg eW.symm h').symm
  have hbCoord_single0 :
      (bCoord : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1) =
        -Pi.single (0 : Fin 3) 1 := by
    apply eW.injective
    rw [hsymm bProdO (Pi.single (0 : Fin 3) 1)]
    change eW.toLinearEquiv
        ((eW.toLinearEquiv).symm ((bProdO : (Fin 2 → K) × (Fin 1 → K) →ₗ[K]
          (Fin 2 → K) × (Fin 1 → K)) (eW (Pi.single (0 : Fin 3) 1)))) =
      eW.toLinearEquiv (-Pi.single (0 : Fin 3) 1)
    rw [LinearEquiv.apply_symm_apply]
    rw [show eW (Pi.single (0 : Fin 3) 1) =
        (Pi.single (0 : Fin 2) 1, 0) by
      change splitCoord (K := K) (Pi.single (0 : Fin 3) 1) = _
      exact splitCoord_single_zero (K := K)]
    rw [show eW.toLinearEquiv (-Pi.single (0 : Fin 3) 1) =
        (-Pi.single (0 : Fin 2) 1, 0) by
      change splitCoord (K := K) (-Pi.single (0 : Fin 3) 1) = _
      rw [map_neg, splitCoord_single_zero (K := K)]
      apply Prod.ext <;> simp]
    change ((QuadraticMap.orthogonalGroupProd (planeForm (K := K)) QL) bPair :
      (Fin 2 → K) × (Fin 1 → K) →ₗ[K] (Fin 2 → K) × (Fin 1 → K))
        (Pi.single (0 : Fin 2) 1, 0) = (-Pi.single (0 : Fin 2) 1, 0)
    rw [QuadraticMap.coe_orthogonalGroupProd]
    apply Prod.ext <;> simp [bPair, hbPlane_single0]
  have hbCoord_single1 :
      (bCoord : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1) =
        -Pi.single (1 : Fin 3) 1 := by
    apply eW.injective
    rw [hsymm bProdO (Pi.single (1 : Fin 3) 1)]
    change eW.toLinearEquiv
        ((eW.toLinearEquiv).symm ((bProdO : (Fin 2 → K) × (Fin 1 → K) →ₗ[K]
          (Fin 2 → K) × (Fin 1 → K)) (eW (Pi.single (1 : Fin 3) 1)))) =
      eW.toLinearEquiv (-Pi.single (1 : Fin 3) 1)
    rw [LinearEquiv.apply_symm_apply]
    rw [show eW (Pi.single (1 : Fin 3) 1) =
        (Pi.single (1 : Fin 2) 1, 0) by
      change splitCoord (K := K) (Pi.single (1 : Fin 3) 1) = _
      exact splitCoord_single_one (K := K)]
    rw [show eW.toLinearEquiv (-Pi.single (1 : Fin 3) 1) =
        (-Pi.single (1 : Fin 2) 1, 0) by
      change splitCoord (K := K) (-Pi.single (1 : Fin 3) 1) = _
      rw [map_neg, splitCoord_single_one (K := K)]
      apply Prod.ext <;> simp]
    change ((QuadraticMap.orthogonalGroupProd (planeForm (K := K)) QL) bPair :
      (Fin 2 → K) × (Fin 1 → K) →ₗ[K] (Fin 2 → K) × (Fin 1 → K))
        (Pi.single (1 : Fin 2) 1, 0) = (-Pi.single (1 : Fin 2) 1, 0)
    rw [QuadraticMap.coe_orthogonalGroupProd]
    apply Prod.ext <;> simp [bPair, hbPlane_single1]
  have hbCoord_fix : ∀ x : Fin 3 → K,
      (coordForm (K := K) δ).polarBilin (Pi.single (0 : Fin 3) 1) x = 0 →
      (coordForm (K := K) δ).polarBilin (Pi.single (1 : Fin 3) 1) x = 0 →
      (bCoord : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) x = x := by
    intro x hx0 hx1
    have hx0' : x 0 = 0 := by
      have h := hx0
      rw [coordForm_polar_single_left (K := K) h2 0 x] at h
      have h' : (2 : K) * x 0 = 0 := by simpa [coordWeight] using h
      exact (mul_eq_zero.mp h').resolve_left h2
    have hx1' : x 1 = 0 := by
      have h := hx1
      rw [coordForm_polar_single_left (K := K) h2 1 x] at h
      have h' : (2 : K) * x 1 = 0 := by simpa [coordWeight] using h
      exact (mul_eq_zero.mp h').resolve_left h2
    have hxsplit : eW x = (0, fun _ : Fin 1 => x 2) := by
      change splitCoord x = (0, fun _ : Fin 1 => x 2)
      exact splitCoord_zero_of_coord_zero (K := K) hx0' hx1'
    apply eW.injective
    rw [hsymm bProdO x]
    change eW.toLinearEquiv ((eW.toLinearEquiv).symm
      ((bProdO : (Fin 2 → K) × (Fin 1 → K) →ₗ[K]
        (Fin 2 → K) × (Fin 1 → K)) (eW x))) = eW.toLinearEquiv x
    rw [LinearEquiv.apply_symm_apply]
    rw [hxsplit, QuadraticMap.coe_orthogonalGroupProd]
    simp [bPair, hxsplit]
  refine ⟨hSp.toSylow hSylowIndex, bCoord, ?_, ?_, hbCoordSq, hbCoordNe,
    hbCoord_single0, hbCoord_single1, hbCoord_fix⟩
  · rw [IsPGroup.toSylow_coe hSp hSylowIndex]
    exact hbCoordMem
  · intro x hx
    rw [IsPGroup.toSylow_coe hSp hSylowIndex] at hx
    exact hbCoordCentral x hx

variable {K : Type} [Field K] [Finite K]

private theorem coord_prescribed (hodd : Odd (Nat.card K)) {δ : K} (hδ : δ ≠ 0)
    (R : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) :
    ∃ (b : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)),
      b ∈ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) ∧
      (∀ x : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ),
        x ∈ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) →
        x * b = b * x) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      ∃ u v : Fin 3 → K,
        coordForm (K := K) δ u = 1 ∧ coordForm (K := K) δ v = 1 ∧
        (coordForm (K := K) δ).polarBilin u v = 0 ∧
        (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) u = -u ∧
        (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) v = -v ∧
        (∀ x : Fin 3 → K,
          (coordForm (K := K) δ).polarBilin u x = 0 →
          (coordForm (K := K) δ).polarBilin v x = 0 →
          (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) x = x) := by
  classical
  let G := TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (↥G) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (Set (↥G)) := inferInstance
  haveI : Finite (Subgroup (↥G)) :=
    Finite.of_injective (fun H : Subgroup (↥G) => (H : Set (↥G))) (by
      intro H K h
      exact Subgroup.ext (fun x =>
        Iff.of_eq (congrArg (fun S : Set (↥G) => x ∈ S) h)))
  haveI : Finite (Sylow 2 (↥G)) :=
    Finite.of_injective (fun P : Sylow 2 (↥G) => (P : Subgroup (↥G))) (by
      intro P Q h
      exact Sylow.ext h)
  obtain ⟨S, b₀, hb₀S, hb₀central, hb₀sq, hb₀ne, hb₀0, hb₀1, hb₀fix⟩ :=
    coordSylow_exists (K := K) hodd hδ
  letI : MulAction.IsPretransitive (↥G) (Sylow 2 (↥G)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := ↥G) (α := Sylow 2 (↥G)) S R
  let b : G := MulAut.conj g b₀
  have hbR : b ∈ (R : Subgroup G) := by
    have hmem : b ∈ (g • S : Sylow 2 (↥G)) := by
      change b ∈ ((g • S : Sylow 2 (↥G)) : Subgroup (↥G))
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact Subgroup.mem_map.mpr ⟨b₀, hb₀S, rfl⟩
    change b ∈ (↑R : Set G)
    simpa [hg] using hmem
  have hbCentral : ∀ x : G, x ∈ (R : Subgroup G) → x * b = b * x := by
    intro x hx
    have hxSub : x ∈ ((g • S : Sylow 2 (↥G)) : Subgroup (↥G)) := by simpa [hg] using hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hxSub
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxSub
    have hcent := hb₀central y hy
    rw [← hxy]
    change (MulAut.conj g y) * (MulAut.conj g b₀) =
      (MulAut.conj g b₀) * (MulAut.conj g y)
    rw [← map_mul, ← map_mul, hcent]
  have hbsq : b * b = 1 := by
    change MulAut.conj g b₀ * MulAut.conj g b₀ = 1
    rw [← map_mul, hb₀sq, map_one]
  have hbne : b ≠ 1 := by
    intro h
    apply hb₀ne
    have hb1 : (MulAut.conj g) b₀ = (MulAut.conj g) 1 := by simpa [b] using h
    exact (MulAut.conj g).injective hb1
  let u : Fin 3 → K := (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1)
  let v : Fin 3 → K := (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1)
  have hgu : (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1) = u := rfl
  have hgv : (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1) = v := rfl
  have hbconj : (b : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) =
      (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        (b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹) := by
    simp [b, MulAut.conj_apply]
  refine ⟨b, hbR, hbCentral, hbsq, hbne, u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hgu]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 _).trans
      (coordForm_single_zero (K := K))
  · rw [← hgv]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 _).trans
      (coordForm_single_one (K := K))
  · rw [← hgu, ← hgv, QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.2,
      ← QuadraticMap.polarBilin_apply_apply]
    exact coordForm_polar_single_zero_one (K := K)
  · rw [← hgu, hbconj]
    change ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        (b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹))
      ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1)) =
      -((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
      ((b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
        (((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)).symm)
          ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1)))) =
      -((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (0 : Fin 3) 1))
    rw [LinearEquiv.symm_apply_apply, hb₀0, map_neg]
  · rw [← hgv, hbconj]
    change ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        (b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹))
      ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1)) =
      -((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
      ((b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
        (((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)).symm)
          ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1)))) =
      -((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Pi.single (1 : Fin 3) 1))
    rw [LinearEquiv.symm_apply_apply, hb₀1, map_neg]
  · intro x hx0 hx1
    let y : Fin 3 → K := (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹ x
    have hgy : (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) y = x := LinearEquiv.apply_symm_apply _ _
    have hy0 : (coordForm (K := K) δ).polarBilin (Pi.single (0 : Fin 3) 1) y = 0 := by
      have h := hx0
      rw [← hgu, ← hgy, QuadraticMap.polarBilin_apply_apply,
        CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.2,
        ← QuadraticMap.polarBilin_apply_apply] at h
      exact h
    have hy1 : (coordForm (K := K) δ).polarBilin (Pi.single (1 : Fin 3) 1) y = 0 := by
      have h := hx1
      rw [← hgv, ← hgy, QuadraticMap.polarBilin_apply_apply,
        CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.2,
        ← QuadraticMap.polarBilin_apply_apply] at h
      exact h
    have hyfix := hb₀fix y hy0 hy1
    rw [← hgy, hbconj]
    change ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        (b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) *
        ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))⁻¹))
      ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) y) =
      ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
      ((b₀ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
        (((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)).symm)
          ((g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) y))) =
      (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) y
    rw [LinearEquiv.symm_apply_apply, hyfix]

variable {K : Type} [Field K] [Finite K]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

private theorem exists_coord_isometry (Q : QuadraticForm K W) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3) :
    ∃ (δ : K) (hδ : δ ≠ 0) (eQ : Q.IsometryEquiv (coordForm (K := K) δ)),
      Q (eQ.symm (Pi.single (0 : Fin 3) 1)) = 1 ∧
      Q (eQ.symm (Pi.single (1 : Fin 3) 1)) = 1 := by
  classical
  obtain ⟨e, horth, hnorm, hlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := K) hodd
      (V := W) (d := 3) hdim (by norm_num) Q hQ one_ne_zero
  let δ : K := Q (e 2)
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    simpa using hlast
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd (K := K) hodd
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  have hO : LinearMap.IsOrthoᵢ (QuadraticMap.associated Q) ⇑e := by
    intro i j hij
    change (QuadraticMap.associated Q) (e i) (e j) = 0
    rw [QuadraticMap.associated_apply (S := K), QuadraticMap.map_add Q, horth i j hij]
    simp
  let eRepr := QuadraticMap.isometryEquivBasisRepr Q e
  have hrepr : Q.basisRepr e = coordForm (K := K) δ := by
    rw [QuadraticMap.basisRepr_eq_of_iIsOrtho Q e hO]
    rw [show (fun i : Fin 3 => Q (e i)) = coordWeight (K := K) δ by
      funext i
      fin_cases i
      · simpa [coordWeight] using hnorm 0 (by norm_num)
      · simpa [coordWeight] using hnorm 1 (by norm_num)
      · simp [coordWeight, δ]]
    exact (coordForm_eq_weighted (K := K) (δ := δ)).symm
  rw [hrepr] at eRepr
  refine ⟨δ, hδ, eRepr, ?_, ?_⟩
  · simpa using coordForm_single_zero (K := K) (δ := δ)
  · simpa using coordForm_single_one (K := K) (δ := δ)

variable {K : Type} [Field K] [Finite K]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_central_plane_negation_of_sylow
    (Q : QuadraticForm K W) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    (R : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ∃ (b : TauCeti.QuadraticMap.orthogonalGroup Q),
      b ∈ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      (∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
        x ∈ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) → x * b = b * x) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      ∃ u v : W, Q u = 1 ∧ Q v = 1 ∧ Q.polarBilin u v = 0 ∧
        (b : W ≃ₗ[K] W) u = -u ∧ (b : W ≃ₗ[K] W) v = -v ∧
        (∀ x : W, Q.polarBilin u x = 0 → Q.polarBilin v x = 0 →
          (b : W ≃ₗ[K] W) x = x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  obtain ⟨δ, hδ, eQ, hu₀, hv₀⟩ := exists_coord_isometry (K := K) Q hodd hQ hdim
  let eG := TauCeti.QuadraticMap.orthogonalGroupCongr eQ
  let R' : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) :=
    Sylow.mapSurjective (f := eG.toMonoidHom) eG.surjective R
  obtain ⟨b', hb'R', hb'central, hb'sq, hb'ne, u', v', hu', hv', huv', hbu', hbv', hfix'⟩ :=
    coord_prescribed (K := K) hodd hδ R'
  have hbmap : b' ∈ Subgroup.map eG.toMonoidHom
      (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [← Sylow.coe_mapSurjective (f := eG.toMonoidHom) eG.surjective R]
    exact hb'R'
  obtain ⟨b, hbR, hbb'⟩ := Subgroup.mem_map.mp hbmap
  have hbb2 : (eG b : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) = b' := hbb'
  have hbCentral : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
      x ∈ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) → x * b = b * x := by
    intro x hx
    apply eG.injective
    have hx' : eG x ∈ (R' : Subgroup
        (TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ))) := by
      rw [show (R' : Subgroup _) = Subgroup.map eG.toMonoidHom
        (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) from
        Sylow.coe_mapSurjective (f := eG.toMonoidHom) eG.surjective R]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    simpa only [map_mul, hbb2] using hb'central (eG x) hx'
  have hbsq : b * b = 1 := by
    apply eG.injective
    simpa only [map_mul, hbb2, hb'sq, map_one]
  have hbne : b ≠ 1 := by
    intro h
    apply hb'ne
    have h1 : (eG b : TauCeti.QuadraticMap.orthogonalGroup (coordForm (K := K) δ)) = 1 := by
      rw [h, map_one]
    exact hbb2.symm.trans h1
  refine ⟨b, hbR, hbCentral, hbsq, hbne, eQ.symm u', eQ.symm v', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    calc Q (eQ.symm u') = (coordForm (K := K) δ) (eQ (eQ.symm u')) := (eQ.map_app _).symm
      _ = (coordForm (K := K) δ) u' := by rw [eQ.apply_symm_apply]
      _ = 1 := hu'
  ·
    calc Q (eQ.symm v') = (coordForm (K := K) δ) (eQ (eQ.symm v')) := (eQ.map_app _).symm
      _ = (coordForm (K := K) δ) v' := by rw [eQ.apply_symm_apply]
      _ = 1 := hv'
  ·
    rw [QuadraticMap.polarBilin_apply_apply]
    simpa using huv'
  ·
    apply eQ.injective
    have h := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply eQ b (eQ (eQ.symm u'))
    rw [hbb2] at h
    simp only [eQ.symm_apply_apply, eQ.apply_symm_apply] at h
    calc eQ.toLinearEquiv ((b : W ≃ₗ[K] W) (eQ.symm u')) =
        (b' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) u' := h.symm
      _ = -u' := hbu'
      _ = eQ.toLinearEquiv (-(eQ.symm u')) := by
        rw [map_neg]
        congr 1
        exact (eQ.apply_symm_apply u').symm
  ·
    apply eQ.injective
    have h := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply eQ b (eQ (eQ.symm v'))
    rw [hbb2] at h
    simp only [eQ.symm_apply_apply, eQ.apply_symm_apply] at h
    calc eQ.toLinearEquiv ((b : W ≃ₗ[K] W) (eQ.symm v')) =
        (b' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) v' := h.symm
      _ = -v' := hbv'
      _ = eQ.toLinearEquiv (-(eQ.symm v')) := by
        rw [map_neg]
        congr 1
        exact (eQ.apply_symm_apply v').symm
  ·
    intro x hx0 hx1
    apply eQ.injective
    have hx0' : (coordForm (K := K) δ).polarBilin u' (eQ x) = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply]
      have h := eQ.polar_apply (eQ.symm u') x
      simp only [eQ.apply_symm_apply] at h
      rw [h]
      simpa [QuadraticMap.polarBilin_apply_apply] using hx0
    have hx1' : (coordForm (K := K) δ).polarBilin v' (eQ x) = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply]
      have h := eQ.polar_apply (eQ.symm v') x
      simp only [eQ.apply_symm_apply] at h
      rw [h]
      simpa [QuadraticMap.polarBilin_apply_apply] using hx1
    have h := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply eQ b (eQ x)
    rw [hbb2] at h
    have h' : (b' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (eQ x) =
        eQ.toLinearEquiv ((b : W ≃ₗ[K] W) x) := by
      calc (b' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (eQ x)
          = eQ.toLinearEquiv ((b : W ≃ₗ[K] W) (eQ.symm (eQ x))) := h
        _ = eQ.toLinearEquiv ((b : W ≃ₗ[K] W) x) := by rw [eQ.symm_apply_apply]
    rw [← h']
    exact hfix' (eQ x) hx0' hx1'

end CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow
