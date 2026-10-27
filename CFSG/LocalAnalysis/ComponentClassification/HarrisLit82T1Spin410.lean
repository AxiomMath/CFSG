module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin412

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

theorem le_of_le_comap_map {G H : Type*} [Group G] [Group H] (θ : G →* H)
    (hker : θ.ker ≤ center G) {J P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hle : P ≤ (J.map θ).comap θ) : P ≤ J := by
  rw [← hP, commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := hle hx
  obtain ⟨b, hb, hby⟩ := hle hy
  have hc : x * a⁻¹ ∈ center G :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel])
  have hd : y * b⁻¹ ∈ center G :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hby, mul_inv_cancel])
  have h := LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hc hd a b
  rw [inv_mul_cancel_right, inv_mul_cancel_right] at h
  rw [h, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem isTwoQuasisimple_range_sl2 {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) : IsTwoQuasisimple ↥ρ.range := by
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have : Finite ↥ρ.range := Finite.of_equiv _ (MonoidHom.ofInjective hρ).toEquiv
  let _ := Fintype.ofFinite K
  obtain ⟨hq, -, -, hO⟩ := Lemma47.sl2_facts hp hp2 hf h5
    ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
      ⟨(MonoidHom.ofInjective hρ).symm⟩⟩
  exact ⟨hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem map_center_range_sl2 {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) :
    (center ↥ρ.range).map ρ.range.subtype = zpowers (ρ (-1)) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have : Finite ↥ρ.range := Finite.of_equiv _ (MonoidHom.ofInjective hρ).toEquiv
  have : Finite ↥((center ↥ρ.range).map ρ.range.subtype) :=
    Finite.of_equiv _ ((center ↥ρ.range).equivMapOfInjective _ ρ.range.subtype_injective).toEquiv
  let _ := Fintype.ofFinite K
  obtain ⟨-, hc2, -, -⟩ := Lemma47.sl2_facts hp hp2 hf h5
    ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
      ⟨(MonoidHom.ofInjective hρ).symm⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (ρ (-1)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, neg_one_sq, map_one]
    · intro h
      exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd (hρ (h.trans (map_one _).symm))
  have hle : zpowers (ρ (-1)) ≤ (center ↥ρ.range).map ρ.range.subtype := by
    rw [zpowers_le, Subgroup.mem_map]
    refine ⟨⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩⟩, ?_, rfl⟩
    rw [mem_center_iff]
    rintro ⟨_, A, rfl⟩
    apply Subtype.ext
    show ρ A * ρ (-1) = ρ (-1) * ρ A
    rw [← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hord, Subgroup.card_map_of_injective ρ.range.subtype_injective, hc2]

section LongRoot

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ} (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)

theorem toFrame_not (s t : Bool) : F.toFrame hij s (!t) = (F.toFrame hij s t).swap := by
  cases t <;> rfl

theorem normal_range_longSL2 [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hQ : Q ≠ 0) (s t : Bool) :
    ((F.longSL2 hij s t).range.subgroupOf (centralizer {F.longSL2 hij s t (-1)})).Normal := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set ρ := F.longSL2 hij s t with hρ
  set ρ' := F.longSL2 hij s (!t) with hρ'
  set fr := F.toFrame hij s t with hfr
  have hθ : ∀ A, spinAction Q (ρ A) = fr.La A := spinAction_longSL2 F hij s t
  have hθ' : ∀ A, spinAction Q (ρ' A) = fr.swap.La A := fun A => by
    rw [hρ', spinAction_longSL2, toFrame_not]
  have hmapJ : ρ.range.map (spinAction Q) = fr.La.range := map_longSL2_range F hij s t
  have hmapJ' : ρ'.range.map (spinAction Q) = fr.swap.La.range := by
    rw [hρ', map_longSL2_range, toFrame_not]
  have hperf : ⁅ρ.range, ρ.range⁆ = ρ.range :=
    Subgroup.isPerfect_iff.mp (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4
      (MonoidHom.ofInjective (longSL2_injective F hij s t)).symm)
  rw [normal_subgroupOf_iff (range_longSL2_le_centralizer F hij s t)]
  intro a g ha hg
  have hgt : g * ρ (-1) = ρ (-1) * g := mem_centralizer_singleton_iff.mp hg
  set P := ρ.range.map (MulAut.conj g).toMonoidHom with hP
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← map_commutator, hperf]
  have hgO : spinAction Q g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q g)
  have hconj : spinAction Q g * fr.La (-1) * (spinAction Q g)⁻¹ = fr.La (-1) := by
    rw [← hθ, ← map_inv, ← map_mul, ← map_mul, hgt, mul_inv_cancel_right]
  have hfundP : IsFundamental Q (P.map (spinAction Q)) (fr.La (-1)) := by
    have h := (IsFundamental.of_frame fr).conj hgO
    rw [hconj] at h
    rwa [hP, map_conj_map, hmapJ]
  obtain ⟨L', -, -, -, huniq⟩ := (IsFundamental.of_frame fr).exists_twin hodd
  have hmem : g * a * g⁻¹ ∈ P := ⟨a, ha, rfl⟩
  rcases huniq _ hfundP with h | h
  · refine le_of_le_comap_map (spinAction Q) (ker_spinAction_le_center Q) hPperf ?_ hmem
    rw [hmapJ, ← h]
    exact le_comap_map _ P
  · exfalso
    have hfund' : IsFundamental Q (ρ'.range.map (spinAction Q)) (fr.La (-1)) := by
      rw [hmapJ']
      exact IsFundamental.of_frame_swap fr
    have hJ' : ρ'.range.map (spinAction Q) = L' := by
      rcases huniq _ hfund' with h' | h'
      · exact absurd (hmapJ'.symm.trans h') (Frame.La_range_ne_swap_La_range fr).symm
      · exact h'
    have hPJ' : P ≤ ρ'.range := le_of_le_comap_map (spinAction Q) (ker_spinAction_le_center Q)
      hPperf (by rw [hJ', ← h]; exact le_comap_map _ P)
    have htP : ρ (-1) ∈ P := by
      refine ⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩, ?_⟩
      show g * ρ (-1) * g⁻¹ = ρ (-1)
      rw [hgt, mul_inv_cancel_right]
    obtain ⟨A, hA⟩ := hPJ' htP
    have hA1 : A = -1 := by
      apply fr.swap.La_injective
      rw [← hθ', hA, hθ, Frame.La_swap_neg_one]
    rw [hA1, hρ', longSL2_neg_one_not F hij hQ s t] at hA
    exact spinGroup.negOne_ne_one Q hQ (mul_right_cancel (hA.trans (one_mul _).symm))

end LongRoot

section Short

variable {K : Type} [Field K]

theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide

abbrev frame01 (K : Type) [Field K] : Frame (quadOdd 3 K) :=
  (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true true

theorem coords_frame01 (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    (frame01 K).coords v =
      !![polar (quadOdd 3 K) v (oddVec 3 K 0 false), -polar (quadOdd 3 K) v (oddVec 3 K 1 false);
        polar (quadOdd 3 K) v (oddVec 3 K 1 true), polar (quadOdd 3 K) v (oddVec 3 K 0 true)] :=
  rfl

theorem La_neg_one_apply_of_perp {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : ∀ m : Fin 3, m ≠ 2 → ∀ r, polar (quadOdd 3 K) v (oddVec 3 K m r) = 0) :
    (frame01 K).La (-1) v = v := by
  rw [Frame.La_neg_one_apply]
  have hc : (frame01 K).coords v = 0 := by
    rw [coords_frame01, hv 0 (by decide) false, hv 1 (by decide) false, hv 1 (by decide) true,
      hv 0 (by decide) true, neg_zero]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hc, map_zero, smul_zero, sub_zero]

theorem eq_of_La_neg_one_apply_eq (h2 : (2 : K) ≠ 0) {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : (frame01 K).La (-1) v = v) :
    v = v (.inl 2) • oddVec 3 K 2 true + v (.inr (.inl 2)) • oddVec 3 K 2 false +
      v (.inr (.inr ())) • oddZ 3 K := by
  rw [Frame.La_neg_one_apply, sub_eq_self, smul_eq_zero] at hv
  have hc : (frame01 K).coords v = 0 := by
    rcases hv with h | h
    · exact absurd h h2
    · rw [← (frame01 K).coords_incl ((frame01 K).coords v), h, map_zero]
  rw [coords_frame01] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, neg_eq_zero, oddVec_true,
    oddVec_false, polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl] at e00 e01 e10 e11
  ext σ
  rcases σ with k | k | ⟨⟩
  · fin_cases k <;> simp [oddZ, e00, e01]
  · fin_cases k <;> simp [oddZ, e10, e11]
  · simp [oddZ]

abbrev pair2 (K : Type) [Field K] : SL2Pair (CliffordAlgebra (quadOdd 3 K)) :=
  (oddFrame 3 K).shortPair 2 true

theorem pair2_X_mul_Y : (pair2 K).X * (pair2 K).Y =
    ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddVec 3 K 2 false) :=
  (oddFrame 3 K).shortPair_X_mul_Y 2 true

theorem pair2_Y_mul_X : (pair2 K).Y * (pair2 K).X =
    ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddVec 3 K 2 true) :=
  (oddFrame 3 K).shortPair_Y_mul_X 2 true

theorem ι_e2_mul_ι_f2_add :
    ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddVec 3 K 2 false) +
      ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddVec 3 K 2 true) = 1 :=
  (oddFrame 3 K).ι_vec_mul_ι_vec_not_add 2 true

theorem toFun_pair2 (M : Matrix (Fin 2) (Fin 2) K) :
    (pair2 K).toFun M =
      M 0 0 • (ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddVec 3 K 2 false)) +
      M 0 1 • (ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddVec 3 K 2 true)) +
      M 1 0 • (ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddZ 3 K)) +
      M 1 1 • (ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddVec 3 K 2 true)) := by
  rw [SL2Pair.toFun, pair2_X_mul_Y, pair2_Y_mul_X, sub_sub, ι_e2_mul_ι_f2_add, sub_self,
    add_zero]
  rfl

theorem toFun_pair2_smul_add (c : K) (M N : Matrix (Fin 2) (Fin 2) K) :
    (pair2 K).toFun (c • M + N) = c • (pair2 K).toFun M + (pair2 K).toFun N := by
  simp only [toFun_pair2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    smul_add]
  abel

theorem toFun_pair2_smul (c : K) (M : Matrix (Fin 2) (Fin 2) K) :
    (pair2 K).toFun (c • M) = c • (pair2 K).toFun M := by
  simp only [toFun_pair2, Matrix.smul_apply, smul_eq_mul, mul_smul, smul_add]

@[expose] def prodMat (a b c a' b' c' : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a * b' + c * c', c * a' - a * c'; b * c' - c * b', b * a' + c * c']

theorem ι_mul_ι_eq_toFun (a b c a' b' c' : K) :
    ι (quadOdd 3 K) (a • oddVec 3 K 2 true + b • oddVec 3 K 2 false + c • oddZ 3 K) *
        ι (quadOdd 3 K) (a' • oddVec 3 K 2 true + b' • oddVec 3 K 2 false + c' • oddZ 3 K) =
      (pair2 K).toFun (prodMat a b c a' b' c') := by
  have hee : ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddVec 3 K 2 true) = 0 :=
    ι_mul_ι_self_eq_zero _ (quadOdd_oddVec 3 K 2 true)
  have hff : ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddVec 3 K 2 false) = 0 :=
    ι_mul_ι_self_eq_zero _ (quadOdd_oddVec 3 K 2 false)
  have hzz : ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddZ 3 K) = 1 :=
    (oddFrame 3 K).ι_z_mul_ι_z
  have hez : ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddZ 3 K) =
      -(ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddVec 3 K 2 true)) :=
    (oddFrame 3 K).ι_vec_mul_ι_z 2 true
  have hzf : ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddVec 3 K 2 false) =
      -(ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddZ 3 K)) :=
    (oddFrame 3 K).ι_z_mul_ι_vec 2 false
  have h1 : (1 : CliffordAlgebra (quadOdd 3 K)) =
      ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddVec 3 K 2 false) +
        ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddVec 3 K 2 true) :=
    ι_e2_mul_ι_f2_add.symm
  rw [toFun_pair2]
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hee, hff, hzz,
    hez, hzf]
  rw [h1]
  simp only [prodMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  module

theorem det_eq_one_of_mem {N : Matrix (Fin 2) (Fin 2) K}
    (hN : (pair2 K).toFun N ∈ spinGroup (quadOdd 3 K)) : N.det = 1 := by
  have hstar := spinGroup.star_mul_self_of_mem hN
  have hst : star ((pair2 K).toFun N) = (pair2 K).toFun !![N 1 1, -N 0 1; -N 1 0, N 0 0] := by
    have hez : ι (quadOdd 3 K) (oddVec 3 K 2 true) * ι (quadOdd 3 K) (oddZ 3 K) =
        -(ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddVec 3 K 2 true)) :=
      (oddFrame 3 K).ι_vec_mul_ι_z 2 true
    have hzf : ι (quadOdd 3 K) (oddZ 3 K) * ι (quadOdd 3 K) (oddVec 3 K 2 false) =
        -(ι (quadOdd 3 K) (oddVec 3 K 2 false) * ι (quadOdd 3 K) (oddZ 3 K)) :=
      (oddFrame 3 K).ι_z_mul_ι_vec 2 false
    rw [toFun_pair2, toFun_pair2]
    simp only [star_add, CliffordAlgebra.star_smul, star_mul, star_ι, neg_mul_neg, hez, hzf,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    module
  rw [hst, ← SL2Pair.toFun_mul] at hstar
  have hadj : !![N 1 1, -N 0 1; -N 1 0, N 0 0] * N = N.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Matrix.adjugate_fin_two, Matrix.adjugate_mul]
  rw [hadj, toFun_pair2] at hstar
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by
    decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one,
    mul_zero, zero_smul, add_zero, ← smul_add, ι_e2_mul_ι_f2_add] at hstar
  apply algebraMap_injective' (quadOdd 3 K)
  rw [Algebra.algebraMap_eq_smul_one, hstar, map_one]

abbrev tSeven (K : Type) [Field K] : spinGroup (quadOdd 3 K) :=
  (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (-1)

theorem spinAction_tSeven : spinAction (quadOdd 3 K) (tSeven K) = (frame01 K).La (-1) :=
  spinAction_longSL2 _ _ true true (-1)

theorem La_neg_one_apply_spinAction {g : spinGroup (quadOdd 3 K)}
    (hg : g ∈ centralizer {tSeven K}) {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : (frame01 K).La (-1) v = v) :
    (frame01 K).La (-1) (spinAction (quadOdd 3 K) g v) = spinAction (quadOdd 3 K) g v := by
  have hgt : g * tSeven K = tSeven K * g := mem_centralizer_singleton_iff.mp hg
  have h := congrArg (spinAction (quadOdd 3 K)) hgt
  rw [map_mul, map_mul, spinAction_tSeven] at h
  have h' := LinearEquiv.congr_fun h v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hv] at h'
  exact h'.symm

theorem La_neg_one_apply_e2 : (frame01 K).La (-1) (oddVec 3 K 2 true) = oddVec 3 K 2 true :=
  La_neg_one_apply_of_perp fun m hm r => by
    rw [polar_quadOdd_oddVec, ite_eq_right_iff]
    exact fun h => absurd h.1.symm hm

theorem La_neg_one_apply_f2 : (frame01 K).La (-1) (oddVec 3 K 2 false) = oddVec 3 K 2 false :=
  La_neg_one_apply_of_perp fun m hm r => by
    rw [polar_quadOdd_oddVec, ite_eq_right_iff]
    exact fun h => absurd h.1.symm hm

theorem La_neg_one_apply_z : (frame01 K).La (-1) (oddZ 3 K) = oddZ 3 K :=
  La_neg_one_apply_of_perp fun m _ r => by
    rw [polar_comm]
    exact polar_quadOdd_oddVec_oddZ 3 K m r

@[expose] def matOf (u u' : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : Matrix (Fin 2) (Fin 2) K :=
  prodMat (u (.inl 2)) (u (.inr (.inl 2))) (u (.inr (.inr ()))) (u' (.inl 2))
    (u' (.inr (.inl 2))) (u' (.inr (.inr ())))

theorem ι_mul_ι_eq_toFun_of_fixed (h2 : (2 : K) ≠ 0) {u u' : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hu : (frame01 K).La (-1) u = u) (hu' : (frame01 K).La (-1) u' = u') :
    ι (quadOdd 3 K) u * ι (quadOdd 3 K) u' = (pair2 K).toFun (matOf u u') := by
  conv_lhs => rw [eq_of_La_neg_one_apply_eq h2 hu, eq_of_La_neg_one_apply_eq h2 hu']
  exact ι_mul_ι_eq_toFun _ _ _ _ _ _

theorem conj_toFun_shortPair (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 K)}
    (hg : g ∈ centralizer {tSeven K}) (M : Matrix (Fin 2) (Fin 2) K) :
    ∃ N : Matrix (Fin 2) (Fin 2) K,
      (g : CliffordAlgebra (quadOdd 3 K)) * (pair2 K).toFun M * ↑g⁻¹ = (pair2 K).toFun N := by
  have he := La_neg_one_apply_spinAction hg La_neg_one_apply_e2
  have hf := La_neg_one_apply_spinAction hg La_neg_one_apply_f2
  have hz := La_neg_one_apply_spinAction hg La_neg_one_apply_z
  refine ⟨M 0 0 • matOf (spinAction _ g (oddVec 3 K 2 true)) (spinAction _ g (oddVec 3 K 2 false)) +
    (M 0 1 • matOf (spinAction _ g (oddZ 3 K)) (spinAction _ g (oddVec 3 K 2 true)) +
    (M 1 0 • matOf (spinAction _ g (oddVec 3 K 2 false)) (spinAction _ g (oddZ 3 K)) +
    M 1 1 • matOf (spinAction _ g (oddVec 3 K 2 false)) (spinAction _ g (oddVec 3 K 2 true)))),
    ?_⟩
  rw [toFun_pair2 M, toFun_pair2_smul_add, toFun_pair2_smul_add, toFun_pair2_smul_add,
    toFun_pair2_smul, ← ι_mul_ι_eq_toFun_of_fixed h2 he hf, ← ι_mul_ι_eq_toFun_of_fixed h2 hz he,
    ← ι_mul_ι_eq_toFun_of_fixed h2 hf hz, ← ι_mul_ι_eq_toFun_of_fixed h2 hf he,
    ← coe_mul_ι_mul_ι_mul_coe_inv, ← coe_mul_ι_mul_ι_mul_coe_inv, ← coe_mul_ι_mul_ι_mul_coe_inv,
    ← coe_mul_ι_mul_ι_mul_coe_inv]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, add_assoc]

abbrev shortSeven (K : Type) [Field K] : SL(2, K) →* spinGroup (quadOdd 3 K) :=
  (oddFrame 3 K).shortSL2 2 true

theorem commute_ι_mul_ι_numOp {p q : Fin 3 ⊕ Fin 3 ⊕ Unit → K} {m : Fin 3}
    (hp : ∀ r, polar (quadOdd 3 K) p (oddVec 3 K m r) = 0)
    (hq : ∀ r, polar (quadOdd 3 K) q (oddVec 3 K m r) = 0) (r : Bool) :
    Commute (ι (quadOdd 3 K) p * ι (quadOdd 3 K) q) ((oddFrame 3 K).numOp m r) :=
  commute_ι_mul_ι _ (hp r) (hp (!r)) (hq r) (hq (!r))

theorem commute_toFun_pair2_numOp (M : Matrix (Fin 2) (Fin 2) K) {m : Fin 3} (hm : m ≠ 2)
    (r : Bool) : Commute ((pair2 K).toFun M) ((oddFrame 3 K).numOp m r) := by
  have hv : ∀ s r, polar (quadOdd 3 K) (oddVec 3 K 2 s) (oddVec 3 K m r) = 0 := fun s r => by
    rw [polar_quadOdd_oddVec, ite_eq_right_iff]
    exact fun h => absurd h.1.symm hm
  have hz : ∀ r, polar (quadOdd 3 K) (oddZ 3 K) (oddVec 3 K m r) = 0 := fun r => by
    rw [polar_comm]
    exact polar_quadOdd_oddVec_oddZ 3 K m r
  rw [toFun_pair2]
  exact ((((commute_ι_mul_ι_numOp (hv true) (hv false) r).smul_left _).add_left
    ((commute_ι_mul_ι_numOp hz (hv true) r).smul_left _)).add_left
    ((commute_ι_mul_ι_numOp (hv false) hz r).smul_left _)).add_left
    ((commute_ι_mul_ι_numOp (hv false) (hv true) r).smul_left _)

theorem range_shortSeven_le_centralizer : (shortSeven K).range ≤ centralizer {tSeven K} := by
  rintro _ ⟨M, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, OddFrame.coe_shortSL2]
  have hc : ∀ m : Fin 3, m ≠ 2 → ∀ r, Commute ((pair2 K).toFun (M : Matrix (Fin 2) (Fin 2) K))
      ((oddFrame 3 K).numOp m r) := fun m hm r => commute_toFun_pair2_numOp _ hm r
  have h01 : Commute ((pair2 K).toFun (M : Matrix (Fin 2) (Fin 2) K))
      ((oddFrame 3 K).numOp 1 true * (oddFrame 3 K).numOp 0 true +
        (oddFrame 3 K).numOp 0 (!true) * (oddFrame 3 K).numOp 1 (!true)) :=
    ((hc 1 (by decide) true).mul_right (hc 0 (by decide) true)).add_right
      ((hc 0 (by decide) (!true)).mul_right (hc 1 (by decide) (!true)))
  have ht : (tSeven K : CliffordAlgebra (quadOdd 3 K)) =
      1 - ((oddFrame 3 K).numOp 1 true * (oddFrame 3 K).numOp 0 true +
        (oddFrame 3 K).numOp 0 (!true) * (oddFrame 3 K).numOp 1 (!true)) -
      ((oddFrame 3 K).numOp 1 true * (oddFrame 3 K).numOp 0 true +
        (oddFrame 3 K).numOp 0 (!true) * (oddFrame 3 K).numOp 1 (!true)) := by
    rw [HypFrame.coe_longSL2, sl2Pair_toFun_neg_one, HypFrame.longPair_X_mul_Y,
      HypFrame.longPair_Y_mul_X]
  rw [ht]
  exact (((Commute.one_right _).sub_right h01).sub_right h01).eq

theorem normal_range_shortSeven (h2 : (2 : K) ≠ 0) :
    ((shortSeven K).range.subgroupOf (centralizer {tSeven K})).Normal := by
  rw [normal_subgroupOf_iff range_shortSeven_le_centralizer]
  rintro _ g ⟨M, rfl⟩ hg
  obtain ⟨N, hN⟩ := conj_toFun_shortPair h2 hg (M : Matrix (Fin 2) (Fin 2) K)
  have hmem : (pair2 K).toFun N ∈ spinGroup (quadOdd 3 K) := by
    have h := (g * shortSeven K M * g⁻¹).2
    rwa [Submonoid.coe_mul, Submonoid.coe_mul, OddFrame.coe_shortSL2, hN] at h
  refine ⟨(⟨N, det_eq_one_of_mem hmem⟩ : SL(2, K)), Subtype.ext ?_⟩
  have hR : (((g * shortSeven K M * g⁻¹ : ↥(spinGroup (quadOdd 3 K))) :
      CliffordAlgebra (quadOdd 3 K))) = (g : CliffordAlgebra (quadOdd 3 K)) *
        (pair2 K).toFun (M : Matrix (Fin 2) (Fin 2) K) * ↑g⁻¹ := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, OddFrame.coe_shortSL2]
  exact (OddFrame.coe_shortSL2 _ _ _ _).trans (hN.symm.trans hR.symm)

theorem shortSeven_neg_one (hQ : quadOdd 3 K ≠ 0) :
    shortSeven K (-1) = spinGroup.negOne (quadOdd 3 K) hQ := by
  apply Subtype.ext
  rw [OddFrame.coe_shortSL2, spinGroup.coe_negOne, sl2Pair_toFun_neg_one, pair2_X_mul_Y,
    pair2_Y_mul_X, ι_e2_mul_ι_f2_add]
  abel

theorem spinSeven_lemma410c {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    ∃ (z t : spinGroup (quadOdd 3 K)) (J₁ J₂ J₃ : Subgroup (spinGroup (quadOdd 3 K))),
      orderOf z = 2 ∧ center (spinGroup (quadOdd 3 K)) = zpowers z ∧
      orderOf t = 2 ∧ t ∉ center (spinGroup (quadOdd 3 K)) ∧
      IsTwoComponentIn J₁ (centralizer {t}) ∧ IsTwoComponentIn J₂ (centralizer {t}) ∧
      IsTwoComponentIn J₃ (centralizer {t}) ∧
      (J₁.subgroupOf (centralizer {t})).Normal ∧ (J₂.subgroupOf (centralizer {t})).Normal ∧
      (J₃.subgroupOf (centralizer {t})).Normal ∧
      IsSLTwoOver (p ^ f) ↥J₁ ∧ IsSLTwoOver (p ^ f) ↥J₂ ∧ IsSLTwoOver (p ^ f) ↥J₃ ∧
      (center ↥J₁).map J₁.subtype = zpowers z ∧ (center ↥J₂).map J₂.subtype = zpowers t ∧
      (center ↥J₃).map J₃.subtype = zpowers (t * z) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  set z := spinGroup.negOne (quadOdd 3 K) hQ with hz
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact spinGroup.negOne_mul_self _ hQ)
      (spinGroup.negOne_ne_one _ hQ)
  have hZ := center_spinGroup_quadOdd h2 (le_refl 3)
  have hzc : z ∈ center (spinGroup (quadOdd 3 K)) := hZ ▸ mem_zpowers z
  set F := (oddFrame 3 K).toHypFrame with hF
  have hrange : (spinAction (quadOdd 3 K)).range ≤ elementaryGroup (quadOdd 3 K) :=
    (range_spinAction_quadOdd h2 (le_refl 3)).le
  have h1 : F.longSL2 fin3_zero_ne_one true false (-1) = z * tSeven K :=
    longSL2_neg_one_not F fin3_zero_ne_one hQ true true
  have ht' : F.longSL2 fin3_zero_ne_one true false (-1) = tSeven K * z := by
    rw [h1]
    exact (mem_center_iff.mp hzc (tSeven K)).symm
  have hCt : centralizer ({F.longSL2 fin3_zero_ne_one true false (-1)} :
      Set (spinGroup (quadOdd 3 K))) = centralizer {tSeven K} := by
    rw [h1]
    exact centralizer_mul_of_mem_center hzc
  have hsinj : Function.Injective (shortSeven K) :=
    LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true
  have hsn := normal_range_shortSeven (K := K) h2
  refine ⟨z, tSeven K, (shortSeven K).range, (F.longSL2 fin3_zero_ne_one true true).range,
    (F.longSL2 fin3_zero_ne_one true false).range, hz2, hZ,
    orderOf_longSL2_neg_one F fin3_zero_ne_one hodd true true, ?_,
    ⟨range_shortSeven_le_centralizer, hsn.isSubnormal,
      isTwoQuasisimple_range_sl2 hp hp2 hK h5 _ hsinj⟩,
    isTwoComponentIn_range_longSL2 F fin3_zero_ne_one hp hp2 hK h5 hrange true true,
    hCt ▸ isTwoComponentIn_range_longSL2 F fin3_zero_ne_one hp hp2 hK h5 hrange true false,
    hsn, normal_range_longSL2 F fin3_zero_ne_one hodd (by omega) hQ true true,
    hCt ▸ normal_range_longSL2 F fin3_zero_ne_one hodd (by omega) hQ true false,
    ?_, isSLTwoOver_range_longSL2 F fin3_zero_ne_one hK true true,
    isSLTwoOver_range_longSL2 F fin3_zero_ne_one hK true false, ?_,
    map_center_range_longSL2 F fin3_zero_ne_one hp hp2 hK h5 true true,
    ht' ▸ map_center_range_longSL2 F fin3_zero_ne_one hp hp2 hK h5 true false⟩
  · rw [center_spinGroup_quadOdd_eq_ker h2 (le_refl 3), MonoidHom.mem_ker]
    exact spinAction_longSL2_neg_one_ne_one F fin3_zero_ne_one hodd true true
  · let _ := Fintype.ofFinite K
    exact ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
      ⟨(MonoidHom.ofInjective hsinj).symm⟩⟩
  · rw [map_center_range_sl2 hp hp2 hK h5 _ hsinj, shortSeven_neg_one hQ]

end Short

end CFSG.ComponentClassification.HarrisLit.T1
