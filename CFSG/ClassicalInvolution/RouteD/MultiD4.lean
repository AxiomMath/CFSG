module

public import CFSG.ClassicalInvolution.RouteD.Multi
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.LieType.Universal.Spin.HypFrame

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

private theorem numOp_mul_numOp_not (m : Fin n) (r : Bool) : F.numOp m r * F.numOp m (!r) = 0 := by
  simp only [numOp, mul_assoc, F.ι_vec_mul_ι_vec_self_mul, mul_zero]

private theorem numOp_add_numOp_not (m : Fin n) (r : Bool) : F.numOp m r + F.numOp m (!r) = 1 := by
  have h := ι_mul_ι_add_swap (Q := Q) (F.vec m r) (F.vec m (!r))
  rw [F.polar_vec_not m r, map_one] at h
  simpa [numOp, Bool.not_not] using h

private theorem coe_longTorus_neg_one {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longTorus hij s t (-1) : CliffordAlgebra Q) =
      1 - (2 : K) • (F.numOp j t * F.numOp i s + F.numOp i (!s) * F.numOp j (!t)) := by
  rw [coe_longTorus, SL2Pair.toFun, F.longPair_X_mul_Y, F.longPair_Y_mul_X]
  simp [coe_diagSL2]
  module

private theorem longTorus_neg_one_mul_flip {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longTorus hij s t (-1) : CliffordAlgebra Q) * F.longTorus hij s (!t) (-1) = -1 := by
  rw [coe_longTorus_neg_one, coe_longTorus_neg_one, Bool.not_not]
  set a := F.numOp i s with ha
  set a' := F.numOp i (!s) with ha'
  set b := F.numOp j t with hb
  set b' := F.numOp j (!t) with hb'
  have haa' : a * a' = 0 := F.numOp_mul_numOp_not i s
  have ha'a : a' * a = 0 := by
    have := F.numOp_mul_numOp_not i (!s)
    rwa [Bool.not_not] at this
  have hbb' : b * b' = 0 := F.numOp_mul_numOp_not j t
  have hb'b : b' * b = 0 := by
    have := F.numOp_mul_numOp_not j (!t)
    rwa [Bool.not_not] at this
  have hsa : a + a' = 1 := F.numOp_add_numOp_not i s
  have hsb : b + b' = 1 := F.numOp_add_numOp_not j t
  have hab' : Commute a b' := F.commute_numOp i s j (!t)
  have ha'b' : Commute a' b' := F.commute_numOp i (!s) j (!t)
  have hsum : b * a + a' * b' + (b' * a + a' * b) = 1 := by
    calc b * a + a' * b' + (b' * a + a' * b) = (b + b') * a + a' * (b' + b) := by noncomm_ring
      _ = a + a' := by rw [hsb, add_comm b' b, hsb, one_mul, mul_one]
      _ = 1 := hsa
  have e1 : b * a * (b' * a) = 0 := by
    calc b * a * (b' * a) = b * (a * b') * a := by simp only [mul_assoc]
      _ = b * (b' * a) * a := by rw [hab'.eq]
      _ = (b * b') * (a * a) := by simp only [mul_assoc]
      _ = 0 := by rw [hbb', zero_mul]
  have e2 : b * a * (a' * b) = 0 := by
    calc b * a * (a' * b) = b * (a * a') * b := by simp only [mul_assoc]
      _ = 0 := by rw [haa', mul_zero, zero_mul]
  have e3 : a' * b' * (b' * a) = 0 := by
    calc a' * b' * (b' * a) = a' * b' * (a * b') := by rw [hab'.eq]
      _ = (a' * (b' * a)) * b' := by simp only [mul_assoc]
      _ = (a' * (a * b')) * b' := by rw [hab'.eq]
      _ = (a' * a) * (b' * b') := by simp only [mul_assoc]
      _ = 0 := by rw [ha'a, zero_mul]
  have e4 : a' * b' * (a' * b) = 0 := by
    calc a' * b' * (a' * b) = a' * (b' * a') * b := by simp only [mul_assoc]
      _ = a' * (a' * b') * b := by rw [ha'b'.symm.eq]
      _ = (a' * a') * (b' * b) := by simp only [mul_assoc]
      _ = 0 := by rw [hb'b, mul_zero]
  have hprod : (b * a + a' * b') * (b' * a + a' * b) = 0 := by
    rw [add_mul, mul_add, mul_add, e1, e2, e3, e4]
    simp
  have hcompl : b' * a + a' * b = 1 - (b * a + a' * b') := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum
  generalize he : b * a + a' * b' = e at hprod hcompl ⊢
  rw [hcompl] at hprod
  have hee : e * e = e := by
    rw [mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  rw [hcompl]
  calc (1 - (2 : K) • e) * (1 - (2 : K) • (1 - e)) = (1 - (2 : K) • e) * (-(1 - (2 : K) • e)) := by
        congr 1
        module
    _ = -((1 - (2 : K) • e) * (1 - (2 : K) • e)) := by rw [mul_neg]
    _ = -1 := by
        have h4 : (1 - (2 : K) • e) * (1 - (2 : K) • e) = 1 - (4 : K) • e + (4 : K) • (e * e) := by
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          module
        rw [h4, hee]
        module

private theorem longTorus_congr {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') {s t s' t' : Bool} (hs : s = s') (ht : t = t') (τ : Kˣ) :
    F.longTorus hij s t τ = F.longTorus hij' s' t' τ := by
  subst hi hj hs ht
  rfl


end CFSG.LieType.Universal.Spin.HypFrame

namespace CFSG.ClassicalInvolution.RouteD

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

variable {K : Type} [Field K]

private theorem torusD_eq_longTorus {n : ℕ} (hn3 : 3 ≤ n) (k : Fin n) {i j : Fin n} (hij : i ≠ j) {t : Bool}
    (hi : rootIdxD n k = i) (hj : rootIdxD' n k = j) (ht : rootSignD n k = t) :
    torusD K hn3 k = (plusFrame n K hn3).longTorus hij true t := by
  subst hi hj ht
  rfl

private noncomputable def zTheta (K : Type) [Field K] (hn3 : 3 ≤ 4) : spinGroup (quadPlus 4 K) :=
  (plusFrame 4 K hn3).longTorus (show (0 : Fin 4) ≠ 1 by decide) true true (-1)

private theorem torusD_neg_one_mul_self (hn3 : 3 ≤ 4) (k : Fin 4) :
    torusD K hn3 k (-1) * torusD K hn3 k (-1) = 1 := by
  rw [← map_mul]
  simp

private theorem four_eq_one {G : Type*} [Group G] {a b c d : G}
    (hbc : Commute b c) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (h : a * d * (b * c) = 1) : d = a * b * c := by
  have h1 : d * (b * c) = a := by
    calc d * (b * c) = (a * a) * d * (b * c) := by rw [ha, one_mul]
      _ = a * (a * d * (b * c)) := by simp only [mul_assoc]
      _ = a := by rw [h, mul_one]
  have h2 : (b * c) * (b * c) = 1 := by
    calc (b * c) * (b * c) = b * (c * b) * c := by simp only [mul_assoc]
      _ = b * (b * c) * c := by rw [hbc.symm.eq]
      _ = (b * b) * (c * c) := by simp only [mul_assoc]
      _ = 1 := by rw [hb, hc, one_mul]
  calc d = d * ((b * c) * (b * c)) := by rw [h2, mul_one]
    _ = (d * (b * c)) * (b * c) := by simp only [mul_assoc]
    _ = a * b * c := by rw [h1]; simp only [mul_assoc]

private theorem zTheta_eq (hn3 : 3 ≤ 4) :
    zTheta K hn3 = torusD K hn3 0 (-1) * torusD K hn3 2 (-1) * torusD K hn3 3 (-1) := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have e0 : torusD K hn3 0 = (plusFrame 4 K hn3).longTorus h01 true false :=
    torusD_eq_longTorus hn3 0 h01 (by simp [rootIdxD]) (by simp [rootIdxD']) (by simp [rootSignD])
  have e2 : torusD K hn3 2 = (plusFrame 4 K hn3).longTorus h23 true false :=
    torusD_eq_longTorus hn3 2 h23 (by simp [rootIdxD]) (by simp [rootIdxD']) (by simp [rootSignD])
  have e3 : torusD K hn3 3 = (plusFrame 4 K hn3).longTorus h23 true true :=
    torusD_eq_longTorus hn3 3 h23 (by simp [rootIdxD]) (by simp [rootIdxD']) (by simp [rootSignD])
  have c01 := (plusFrame 4 K hn3).longTorus_neg_one_mul_flip h01 true false
  have c23 := (plusFrame 4 K hn3).longTorus_neg_one_mul_flip h23 true false
  rw [Bool.not_false] at c01 c23
  have hmain : torusD K hn3 0 (-1) * zTheta K hn3 * (torusD K hn3 2 (-1) * torusD K hn3 3 (-1)) =
      1 := by
    apply Subtype.ext
    rw [e0, e2, e3, zTheta]
    show ((plusFrame 4 K hn3).longTorus h01 true false (-1) : CliffordAlgebra (quadPlus 4 K)) *
      ((plusFrame 4 K hn3).longTorus h01 true true (-1) : CliffordAlgebra (quadPlus 4 K)) *
      (((plusFrame 4 K hn3).longTorus h23 true false (-1) : CliffordAlgebra (quadPlus 4 K)) *
        ((plusFrame 4 K hn3).longTorus h23 true true (-1) : CliffordAlgebra (quadPlus 4 K))) = 1
    rw [c01, c23]
    simp
  have hcomm : ∀ {i j : Fin 4} (hij : i ≠ j) (s t : Bool) {k l : Fin 4} (hkl : k ≠ l) (u v : Bool),
      Commute ((plusFrame 4 K hn3).longTorus hij s t (-1)) ((plusFrame 4 K hn3).longTorus hkl u v (-1)) :=
    by
      intro i j hij s t k l hkl u v
      exact (plusFrame 4 K hn3).commute_longTorus_longTorus hij s t _ hkl u v _
  refine four_eq_one ?_ (torusD_neg_one_mul_self hn3 0) (torusD_neg_one_mul_self hn3 2)
    (torusD_neg_one_mul_self hn3 3) hmain
  rw [e2, e3]
  exact hcomm h23 true false h23 true true

private theorem toStdD_neg_thetaD :
    toStdD 4 (-thetaD 4) =
      Pi.single (1 : Fin 4) (boolSign (!true)) + Pi.single (0 : Fin 4) (boolSign (!true)) := by
  rw [toStdD_neg, toStdD_thetaD (by norm_num)]
  funext a
  fin_cases a <;> simp [boolSign]

private theorem toStdD_thetaD' :
    toStdD 4 (thetaD 4) =
      Pi.single (0 : Fin 4) (boolSign true) + Pi.single (1 : Fin 4) (boolSign true) :=
  toStdD_thetaD (by norm_num)

private theorem zTheta_mem (hn3 : 3 ≤ 4) : zTheta K hn3 ∈ rootθD 4 K hn3 := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hW := (plusFrame 4 K hn3).longWeyl_mul_self h01 true true
  have hn : (plusFrame 4 K hn3).longWeyl h01 true true ∈ rootθD 4 K hn3 := by
    rw [(plusFrame 4 K hn3).longWeyl_eq h01 true true]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact Subgroup.mem_sup_left
        (CFSG.LieType.Universal.Spin.PlusCT.longRoot_mem_plusRootGroup hn3 h01 true true
          toStdD_thetaD' 1)
    · exact Subgroup.mem_sup_right
        (CFSG.LieType.Universal.Spin.PlusCT.longRoot_mem_plusRootGroup hn3 h01.symm (!true)
          (!true) toStdD_neg_thetaD (-1))
    · exact Subgroup.mem_sup_left
        (CFSG.LieType.Universal.Spin.PlusCT.longRoot_mem_plusRootGroup hn3 h01 true true
          toStdD_thetaD' 1)
  rw [zTheta, ← hW]
  exact mul_mem hn hn

private theorem zTheta_central (hn3 : 3 ≤ 4) :
    ∀ x ∈ rootθD 4 K hn3, zTheta K hn3 * x = x * zTheta K hn3 := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h : rootθD 4 K hn3 ≤ Subgroup.centralizer ({zTheta K hn3} : Set (spinGroup (quadPlus 4 K))) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.Spin.PlusCT.mem_plusRootGroup_iff hn3 h01 true true
        toStdD_thetaD').mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := (plusFrame 4 K hn3).longTorus_conj_longRoot h01 true true (-1) h01 true true c
      have e : ((((-1 : Kˣ) ^ (longCoroot (0 : Fin 4) 1 true true 0 true +
          longCoroot (0 : Fin 4) 1 true true 1 true) : Kˣ) : K) * c) = c := by
        simp [longCoroot]
      rw [e] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.Spin.PlusCT.mem_plusRootGroup_iff hn3 h01.symm
        (!true) (!true) toStdD_neg_thetaD).mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := (plusFrame 4 K hn3).longTorus_conj_longRoot h01 true true (-1) h01.symm (!true)
        (!true) c
      have e : ((((-1 : Kˣ) ^ (longCoroot (0 : Fin 4) 1 true true 1 (!true) +
          longCoroot (0 : Fin 4) 1 true true 0 (!true)) : Kˣ) : K) * c) = c := by
        simp [longCoroot]
      rw [e] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h hx)).symm

private theorem torusD_neg_one_ne_one (hn3 : 3 ≤ 4) (h2 : (2 : K) ≠ 0) (k : Fin 4) :
    torusD K hn3 k (-1) ≠ 1 := by
  intro h
  have h1 := spinAction_torusD K hn3 k (-1) (rootIdxD 4 k) true
  rw [h, map_one] at h1
  have hc : longCoroot (rootIdxD 4 k) (rootIdxD' 4 k) true (rootSignD 4 k) (rootIdxD 4 k) true = 1 := by
    simp [longCoroot, rootIdxD_ne 4 (by norm_num) k]
  rw [hc, zpow_one] at h1
  have h3 := congrFun h1 (Sum.inl (rootIdxD 4 k))
  simp [plusVec] at h3
  apply h2
  linear_combination h3

private theorem weylD_one_conj_torusD' (hn3 : 3 ≤ 4) (k : Fin 4) (hk : k ≠ 1) :
    weylD K hn3 1 * torusD K hn3 k (-1) * (weylD K hn3 1)⁻¹ =
      torusD K hn3 1 (-1) * torusD K hn3 k (-1) := by
  rw [weylD_conj_torusD]
  congr 2
  fin_cases k
  · simp [rootIdxD, rootIdxD', rootSignD, longCoroot]
  · exact absurd rfl hk
  · simp [rootIdxD, rootIdxD', rootSignD, longCoroot]
  · simp [rootIdxD, rootIdxD', rootSignD, longCoroot]

private theorem torusD_not_mem_center (hn3 : 3 ≤ 4) (h2 : (2 : K) ≠ 0) (k : Fin 4) (hk : k ≠ 1) :
    torusD K hn3 k (-1) ∉ Subgroup.center (spinGroup (quadPlus 4 K)) := by
  intro hc
  have h1 := weylD_one_conj_torusD' (K := K) hn3 k hk
  have h2' : weylD K hn3 1 * torusD K hn3 k (-1) * (weylD K hn3 1)⁻¹ = torusD K hn3 k (-1) :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp hc _)
  rw [h2'] at h1
  have h3 : torusD K hn3 1 (-1) * torusD K hn3 k (-1) = 1 * torusD K hn3 k (-1) := by
    rw [one_mul]
    exact h1.symm
  exact torusD_neg_one_ne_one hn3 h2 1 (mul_right_cancel h3)

private theorem zTheta_not_mem_center (hn3 : 3 ≤ 4) (h2 : (2 : K) ≠ 0) :
    zTheta K hn3 ∉ Subgroup.center (spinGroup (quadPlus 4 K)) := by
  intro hc
  set e := torusD K hn3 1 (-1) with he
  set a := torusD K hn3 0 (-1) with ha
  set b := torusD K hn3 2 (-1) with hb
  set c := torusD K hn3 3 (-1) with hc'
  have hae : a * e = e * a := (commute_torusD K hn3 0 1 (-1) (-1)).eq
  have hbe : b * e = e * b := (commute_torusD K hn3 2 1 (-1) (-1)).eq
  have hee : e * e = 1 := torusD_neg_one_mul_self hn3 1
  have hconj : weylD K hn3 1 * zTheta K hn3 * (weylD K hn3 1)⁻¹ = e * zTheta K hn3 := by
    rw [zTheta_eq]
    calc weylD K hn3 1 * (a * b * c) * (weylD K hn3 1)⁻¹ =
        (weylD K hn3 1 * a * (weylD K hn3 1)⁻¹) * (weylD K hn3 1 * b * (weylD K hn3 1)⁻¹) *
          (weylD K hn3 1 * c * (weylD K hn3 1)⁻¹) := by group
      _ = (e * a) * (e * b) * (e * c) := by
        rw [weylD_one_conj_torusD' (K := K) hn3 0 (by decide), weylD_one_conj_torusD' (K := K) hn3 2 (by decide),
          weylD_one_conj_torusD' (K := K) hn3 3 (by decide)]
      _ = e * (a * b * c) := by
        have hce : c * e = e * c := (commute_torusD K hn3 3 1 (-1) (-1)).eq
        calc e * a * (e * b) * (e * c) = e * (a * e) * b * (e * c) := by simp only [mul_assoc]
          _ = e * (e * a) * b * (e * c) := by rw [hae]
          _ = (e * e) * a * b * e * c := by simp only [mul_assoc]
          _ = a * b * e * c := by rw [hee, one_mul]
          _ = a * (b * e) * c := by simp only [mul_assoc]
          _ = a * (e * b) * c := by rw [hbe]
          _ = (a * e) * b * c := by simp only [mul_assoc]
          _ = (e * a) * b * c := by rw [hae]
          _ = e * (a * b * c) := by simp only [mul_assoc]
  have hcen : weylD K hn3 1 * zTheta K hn3 * (weylD K hn3 1)⁻¹ = zTheta K hn3 :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp hc _)
  rw [hcen] at hconj
  have h3 : e * zTheta K hn3 = 1 * zTheta K hn3 := by
    rw [one_mul]
    exact hconj.symm
  exact torusD_neg_one_ne_one hn3 h2 1 (mul_right_cancel h3)

private theorem diagSL2_neg_one_mul (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    diagSL2 (-1 : Kˣ) * M = M * diagSL2 (-1 : Kˣ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, coe_diagSL2]

section Group

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

private theorem psi_torusD_eq (hp2 : p ≠ 2) (hf : 0 < f) (hn3 : 3 ≤ 4)
    (h2 : (2 : GaloisField p f) ≠ 0)
    (ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* G)
    (hker : ψ.ker ≤ Subgroup.center _) (k : Fin 4) (hk : k ≠ 1) {M : Subgroup G} {w : G}
    (hM : (rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup k).map ψ = M)
    (hw : IsClassicalMember p f M w) : ψ (torusD (GaloisField p f) hn3 k (-1)) = w := by
  have hmem : torusD (GaloisField p f) hn3 k (-1) ∈
      rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup k := by
    rw [torusD_apply]
    exact CFSG.LieType.Universal.Spin.PlusCT.rankOneD_mem_rankOne hn3 k _
  refine hw.eq_of_isCentralInvolution hp2 hf ⟨?_, ?_, ?_, ?_⟩
  · rw [← hM]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h1
    exact torusD_not_mem_center hn3 h2 k hk (hker (MonoidHom.mem_ker.mpr h1))
  · rw [← map_mul, torusD_neg_one_mul_self, map_one]
  · intro m hm
    rw [← hM] at hm
    obtain ⟨r, hr, rfl⟩ := hm
    have hr' : r ∈ (rankOneD (GaloisField p f) hn3 k).range := by
      rw [← CFSG.LieType.Universal.Spin.PlusCT.rankOne_plusRootGroup hn3 k]
      exact hr
    obtain ⟨M', rfl⟩ := hr'
    rw [← map_mul, ← map_mul, torusD_apply, ← map_mul, ← map_mul, diagSL2_neg_one_mul]

open CFSG.Timmesfeld (edgeD)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

theorem d4Frame_holds : D4Frame p f := by
  intro hp2 hq G _ _ Ω hΩ K a₁ a₂ β z w₁ w₂ hK ha₁ ha₂ hβ hz hw₁ hw₂ hKa₁ hKa₂ ha₁a₂
    ⟨W₀, hpK⟩ ⟨W₁, hp₁⟩ ⟨W₂, hp₂⟩
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 4 := by norm_num
  have hq4 : 4 ≤ p ^ f := by omega
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_rfl⟩
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hF]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  let U : Fin 4 → Subgroup G := ![K, β, a₁, a₂]
  have hcomm : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j) := by
    intro i j hij h1' h2'
    fin_cases i <;> fin_cases j <;> simp [edgeD, U] at hij h1' h2' ⊢
    all_goals first | exact hKa₁ | exact hKa₂ | exact ha₁a₂ | exact hKa₁.symm | exact hKa₂.symm |
      exact ha₁a₂.symm
  have hpair : ∀ i j : Fin 4, edgeD 4 i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeD, U] at hij ⊢
    all_goals first | exact ⟨W₀, hpK⟩ | exact ⟨W₁, hp₁.symm⟩ | exact ⟨W₂, hp₂.symm⟩
  obtain ⟨ψ, hker, hψ⟩ := exists_psi_of_chain_plus hadm hq4 U hcomm hpair
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have hscT : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 4 p f Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) := by
    revert hscT
    rw [e1]
    exact id
  obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum 4 (GaloisField p f) hn3).rootGroup (0 : Fin 4))
    (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (0 : Fin 4)) (rootθD 4 (GaloisField p f) hn3)
    (rootθD_mem_fundamentalSubgroups hn3 le_rfl)
  have ha3 : (rootθD 4 (GaloisField p f) hn3).map ψ = conjSub (ψ g) K := by
    rw [hg, ← conjSub_map, hψ 0]
    rfl
  refine ⟨conjSub (ψ g) K, hΩ _ _ hK, ?_, ?_, ?_, ?_⟩
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 0) (by decide))
    rw [ha3, hψ 0] at this
    exact this
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 2) (by decide))
    rw [ha3, hψ 2] at this
    exact this
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 3) (by decide))
    rw [ha3, hψ 3] at this
    exact this
  · have hcl := hz.conj (ψ g)
    have hz0 := psi_torusD_eq hp2 hf hn3 h2 ψ hker 0 (by decide) (hψ 0) hz
    have hz2 := psi_torusD_eq hp2 hf hn3 h2 ψ hker 2 (by decide) (hψ 2) hw₁
    have hz3 := psi_torusD_eq hp2 hf hn3 h2 ψ hker 3 (by decide) (hψ 3) hw₂
    have hθ : ψ (zTheta (GaloisField p f) hn3) = z * w₁ * w₂ := by
      rw [zTheta_eq, map_mul, map_mul, hz0, hz2, hz3]
    have hcent : IsCentralInvolution (conjSub (ψ g) K) (z * w₁ * w₂) := by
      rw [← ha3, ← hθ]
      refine ⟨Subgroup.mem_map_of_mem _ (zTheta_mem hn3), ?_, ?_, ?_⟩
      · intro h1
        exact zTheta_not_mem_center hn3 h2 (hker (MonoidHom.mem_ker.mpr h1))
      · rw [← map_mul, zTheta, ← map_mul]
        simp
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul, zTheta_central hn3 x hx]
    rw [hcl.eq_of_isCentralInvolution hp2 hf hcent]
    exact hcl


end Group

open CFSG.ClassicalInvolution.Generic.CoreAssembly in
theorem multiPiece_of_multiStar {p f : ℕ} [Fact p.Prime] (hstar : MultiStar p f) :
    MultiPiece p f :=
  multiPiece_of_star hstar d4Frame_holds

end CFSG.ClassicalInvolution.RouteD
