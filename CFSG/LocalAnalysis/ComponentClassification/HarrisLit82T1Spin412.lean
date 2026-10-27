module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

theorem sl2Pair_toFun_neg_one {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
    (P : SL2Pair A) :
    P.toFun ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      1 - (P.X * P.Y + P.Y * P.X) - (P.X * P.Y + P.Y * P.X) := by
  simp only [SL2Pair.toFun, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), neg_zero, zero_smul, add_zero,
    neg_smul, one_smul]
  abel

theorem centralizer_mul_of_mem_center {G : Type*} [Group G] {z t : G} (hz : z ∈ center G) :
    centralizer ({z * t} : Set G) = centralizer {t} := by
  ext x
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have hzx : x * z = z * x := mem_center_iff.mp hz x
  constructor
  · intro h
    have h' : z * (t * x) = z * (x * t) := by
      rw [← mul_assoc, h, ← mul_assoc, hzx, mul_assoc]
    exact mul_left_cancel h'
  · intro h
    rw [mul_assoc, h, ← mul_assoc, ← hzx, mul_assoc]

section LongRoot

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ} (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)

theorem numOp_add_numOp_not (k : Fin m) (r : Bool) : F.numOp k r + F.numOp k (!r) = 1 := by
  simp only [HypFrame.numOp, Bool.not_not]
  exact ι_mul_ι_add_ι_mul_ι_eq_one Q (F.polar_vec_not k r)

theorem coe_longSL2_neg_one_add (s t : Bool) :
    (F.longSL2 hij s t (-1) : CliffordAlgebra Q) + F.longSL2 hij s (!t) (-1) = 0 := by
  rw [HypFrame.coe_longSL2, HypFrame.coe_longSL2, sl2Pair_toFun_neg_one, sl2Pair_toFun_neg_one,
    HypFrame.longPair_X_mul_Y, HypFrame.longPair_X_mul_Y, HypFrame.longPair_Y_mul_X,
    HypFrame.longPair_Y_mul_X, Bool.not_not]
  have hsum : F.numOp j t * F.numOp i s + F.numOp i (!s) * F.numOp j (!t) +
      (F.numOp j (!t) * F.numOp i s + F.numOp i (!s) * F.numOp j t) = 1 := by
    calc _ = (F.numOp j t + F.numOp j (!t)) * F.numOp i s +
          F.numOp i (!s) * (F.numOp j t + F.numOp j (!t)) := by noncomm_ring
      _ = 1 := by
        rw [numOp_add_numOp_not F j t, one_mul, mul_one, numOp_add_numOp_not F i s]
  calc _ = (1 + 1) - (F.numOp j t * F.numOp i s + F.numOp i (!s) * F.numOp j (!t) +
        (F.numOp j (!t) * F.numOp i s + F.numOp i (!s) * F.numOp j t)) -
        (F.numOp j t * F.numOp i s + F.numOp i (!s) * F.numOp j (!t) +
        (F.numOp j (!t) * F.numOp i s + F.numOp i (!s) * F.numOp j t)) := by abel
    _ = 0 := by rw [hsum]; abel

theorem longSL2_neg_one_not (hQ : Q ≠ 0) (s t : Bool) :
    F.longSL2 hij s (!t) (-1) = spinGroup.negOne Q hQ * F.longSL2 hij s t (-1) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, eq_neg_iff_add_eq_zero, add_comm]
  exact coe_longSL2_neg_one_add F hij s t

theorem spinAction_longSL2 (s t : Bool) (A : SL(2, K)) :
    spinAction Q (F.longSL2 hij s t A) = (F.toFrame hij s t).La A :=
  DFunLike.congr_fun (spinAction_comp_longSL2 F hij s t) A

theorem longSL2_injective (s t : Bool) : Function.Injective (F.longSL2 hij s t) := by
  intro A B h
  have h' := congrArg (spinAction Q) h
  rw [spinAction_longSL2, spinAction_longSL2] at h'
  exact (F.toFrame hij s t).La_injective h'

theorem range_longSL2_le_centralizer (s t : Bool) :
    (F.longSL2 hij s t).range ≤ centralizer {F.longSL2 hij s t (-1)} := by
  rintro _ ⟨A, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ rfl
  rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]

variable [Finite K]

theorem orderOf_longSL2_neg_one (hodd : Odd (Nat.card K)) (s t : Bool) :
    orderOf (F.longSL2 hij s t (-1)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, neg_one_sq, map_one]
  · intro h
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
      (longSL2_injective F hij s t (h.trans (map_one _).symm))

theorem spinAction_longSL2_neg_one_ne_one (hodd : Odd (Nat.card K)) (s t : Bool) :
    spinAction Q (F.longSL2 hij s t (-1)) ≠ 1 := by
  rw [spinAction_longSL2]
  exact IsFundamental.ne_one hodd (IsFundamental.of_frame _)

theorem isSubnormal_range_longSL2 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) (s t : Bool) :
    ((F.longSL2 hij s t).range.subgroupOf
      (centralizer {F.longSL2 hij s t (-1)})).IsSubnormal := by
  set ρ := F.longSL2 hij s t with hρ
  set C := centralizer ({ρ (-1)} : Set (spinGroup Q)) with hC
  set fr := F.toFrame hij s t with hfr
  have hθ : ∀ A, spinAction Q (ρ A) = fr.La A := spinAction_longSL2 F hij s t
  have hmapC : ∀ x : C, spinAction Q x ∈ centralizerΩ Q (fr.La (-1)) := by
    intro x
    rw [centralizerΩ, Subgroup.mem_inf]
    refine ⟨hrange ⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ rfl
    have hx : ρ (-1) * (x : spinGroup Q) = x * ρ (-1) :=
      (mem_centralizer_iff.mp x.2) _ (Set.mem_singleton _)
    rw [← hθ, ← map_mul, hx, map_mul]
  let φ : C →* centralizerΩ Q (fr.La (-1)) :=
    ((spinAction Q).comp C.subtype).codRestrict _ hmapC
  set H := (fr.La.range.subgroupOf (centralizerΩ Q (fr.La (-1)))).comap φ with hH
  have hHs : H.IsSubnormal := ((IsFundamental.of_frame fr).isSubnormal hodd h4).comap φ
  have hle : ρ.range.subgroupOf C ≤ H := by
    rintro x ⟨A, hA⟩
    show spinAction Q x ∈ fr.La.range
    exact ⟨A, by rw [← hθ, hA]; rfl⟩
  have hnorm : ((ρ.range.subgroupOf C).subgroupOf H).Normal := by
    rw [normal_subgroupOf_iff hle]
    intro a b ha hb
    obtain ⟨A, hA⟩ : spinAction Q b ∈ fr.La.range := hb
    have hc : (ρ A)⁻¹ * (b : spinGroup Q) ∈ center (spinGroup Q) := by
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, hA, inv_mul_cancel]
    obtain ⟨B, hB⟩ := ha
    have hca : (a : spinGroup Q) * ((ρ A)⁻¹ * (b : spinGroup Q)) =
        ((ρ A)⁻¹ * (b : spinGroup Q)) * a := mem_center_iff.mp hc a
    have hB' : ρ B = (a : spinGroup Q) := hB
    refine ⟨A * B * A⁻¹, ?_⟩
    show ρ (A * B * A⁻¹) = ((b * a * b⁻¹ : C) : spinGroup Q)
    rw [map_mul, map_mul, map_inv, hB', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc ρ A * (a : spinGroup Q) * (ρ A)⁻¹ =
          ρ A * ((a : spinGroup Q) * ((ρ A)⁻¹ * (b : spinGroup Q))) *
            ((ρ A)⁻¹ * (b : spinGroup Q))⁻¹ * (ρ A)⁻¹ := by group
      _ = (b : spinGroup Q) * a * (b : spinGroup Q)⁻¹ := by rw [hca]; group
  exact Subgroup.IsSubnormal.step _ H hle hHs hnorm

theorem finite_range_longSL2 (s t : Bool) : Finite ↥(F.longSL2 hij s t).range :=
  Finite.of_equiv _ (MonoidHom.ofInjective (longSL2_injective F hij s t)).toEquiv

theorem isSLTwoOver_range_longSL2 {q : ℕ} (hK : Nat.card K = q) (s t : Bool) :
    IsSLTwoOver q ↥(F.longSL2 hij s t).range := by
  let _ := Fintype.ofFinite K
  exact ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
    ⟨(MonoidHom.ofInjective (longSL2_injective F hij s t)).symm⟩⟩

theorem isTwoComponentIn_range_longSL2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (s t : Bool) :
    IsTwoComponentIn (F.longSL2 hij s t).range (centralizer {F.longSL2 hij s t (-1)}) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have := finite_range_longSL2 F hij s t
  refine ⟨range_longSL2_le_centralizer F hij s t,
    isSubnormal_range_longSL2 F hij hodd (by omega) hrange s t, ?_⟩
  obtain ⟨hq, -, -, hO⟩ :=
    Lemma47.sl2_facts hp hp2 hf h5 (isSLTwoOver_range_longSL2 F hij hK s t)
  exact ⟨hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem map_center_range_longSL2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (s t : Bool) :
    (center ↥(F.longSL2 hij s t).range).map (F.longSL2 hij s t).range.subtype =
      zpowers (F.longSL2 hij s t (-1)) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have := finite_range_longSL2 F hij s t
  have : Finite ↥((center ↥(F.longSL2 hij s t).range).map (F.longSL2 hij s t).range.subtype) :=
    Finite.of_equiv _ ((center ↥(F.longSL2 hij s t).range).equivMapOfInjective _
      (F.longSL2 hij s t).range.subtype_injective).toEquiv
  obtain ⟨-, hc2, -, -⟩ :=
    Lemma47.sl2_facts hp hp2 hf h5 (isSLTwoOver_range_longSL2 F hij hK s t)
  have hord := orderOf_longSL2_neg_one F hij hodd s t
  have hle : zpowers (F.longSL2 hij s t (-1)) ≤
      (center ↥(F.longSL2 hij s t).range).map (F.longSL2 hij s t).range.subtype := by
    rw [zpowers_le, Subgroup.mem_map]
    refine ⟨⟨F.longSL2 hij s t (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩⟩, ?_, rfl⟩
    rw [mem_center_iff]
    rintro ⟨_, A, rfl⟩
    apply Subtype.ext
    show F.longSL2 hij s t A * F.longSL2 hij s t (-1) =
      F.longSL2 hij s t (-1) * F.longSL2 hij s t A
    rw [← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hord,
    Subgroup.card_map_of_injective (F.longSL2 hij s t).range.subtype_injective, hc2]

end LongRoot

section Odd

variable {n : ℕ} {K : Type} [Field K]

theorem center_spinGroup_quadOdd_eq_ker (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    center (spinGroup (quadOdd n K)) = (spinAction (quadOdd n K)).ker := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadOdd h2 hn
  have hodd : Odd (Fintype.card (Fin n ⊕ Fin n ⊕ Unit)) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    exact ⟨n, by ring⟩
  refine le_antisymm ?_ (ker_spinAction_le_center _)
  rw [← hZ, hcomap, ← ker_spinMatrix]
  exact LieType.Steinberg.comap_statedScalars_le_ker_of_odd hodd h2 (coe_quadOdd n K)
    (exists_map_ne_zero_of_hypPair _ (oddPair K (⟨0, by omega⟩ : Fin n)))
    (range_spinMatrix_quadOdd h2 hn)

theorem center_spinGroup_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    center (spinGroup (quadOdd n K)) =
      zpowers (spinGroup.negOne (quadOdd n K) (nondegenerate_quadOdd n K).ne_zero) := by
  rw [center_spinGroup_quadOdd_eq_ker h2 hn, ← ker_spinMatrix]
  refine le_antisymm (fun x hx => ?_) ?_
  · have hx' : x ∈ ((spinMatrix (quadOdd n K)).ker : Set (spinGroup (quadOdd n K))) := hx
    rw [coe_ker_spinMatrix_quadOdd h2] at hx'
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · rw [zpowers_le, ← SetLike.mem_coe, coe_ker_spinMatrix_quadOdd h2]
    exact Set.mem_insert_of_mem _ rfl

variable [Finite K]

theorem spinOdd_lemma412 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) (hn : 3 ≤ n) :
    ∃ z : spinGroup (quadOdd n K), orderOf z = 2 ∧ center (spinGroup (quadOdd n K)) = zpowers z ∧
      ∃ (t : spinGroup (quadOdd n K)) (J₁ J₂ : Subgroup (spinGroup (quadOdd n K))),
        orderOf t = 2 ∧ t ∉ center (spinGroup (quadOdd n K)) ∧
        IsTwoComponentIn J₁ (centralizer {t}) ∧ IsTwoComponentIn J₂ (centralizer {t}) ∧
        IsSLTwoOver (p ^ f) ↥J₁ ∧ IsSLTwoOver (p ^ f) ↥J₂ ∧
        (center ↥J₁).map J₁.subtype = zpowers t ∧
        (center ↥J₂).map J₂.subtype = zpowers (t * z) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : quadOdd n K ≠ 0 := (nondegenerate_quadOdd n K).ne_zero
  set z := spinGroup.negOne (quadOdd n K) hQ with hz
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [sq]; exact spinGroup.negOne_mul_self _ hQ)
      (spinGroup.negOne_ne_one _ hQ)
  have hZ := center_spinGroup_quadOdd h2 hn
  have hzc : z ∈ center (spinGroup (quadOdd n K)) := hZ ▸ mem_zpowers z
  set F := (oddFrame n K).toHypFrame with hF
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hrange : (spinAction (quadOdd n K)).range ≤ elementaryGroup (quadOdd n K) :=
    (range_spinAction_quadOdd h2 hn).le
  set t := F.longSL2 hij true true (-1) with ht
  have h1 : F.longSL2 hij true false (-1) = z * t := longSL2_neg_one_not F hij hQ true true
  have ht' : F.longSL2 hij true false (-1) = t * z := by
    rw [h1]
    exact (mem_center_iff.mp hzc t).symm
  have hCt : centralizer ({F.longSL2 hij true false (-1)} : Set (spinGroup (quadOdd n K))) =
      centralizer {t} := by
    rw [h1]
    exact centralizer_mul_of_mem_center hzc
  refine ⟨z, hz2, hZ, t, (F.longSL2 hij true true).range, (F.longSL2 hij true false).range,
    orderOf_longSL2_neg_one F hij hodd true true, ?_,
    isTwoComponentIn_range_longSL2 F hij hp hp2 hK h5 hrange true true,
    hCt ▸ isTwoComponentIn_range_longSL2 F hij hp hp2 hK h5 hrange true false,
    isSLTwoOver_range_longSL2 F hij hK true true, isSLTwoOver_range_longSL2 F hij hK true false,
    map_center_range_longSL2 F hij hp hp2 hK h5 true true,
    ht' ▸ map_center_range_longSL2 F hij hp hp2 hK h5 true false⟩
  rw [center_spinGroup_quadOdd_eq_ker h2 hn, MonoidHom.mem_ker]
  exact spinAction_longSL2_neg_one_ne_one F hij hodd true true

end Odd

end CFSG.ComponentClassification.HarrisLit.T1
