module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3DDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Twin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DA
public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Raw

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup CliffordAlgebra Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

theorem nonempty_sl2_equiv_zmod_three {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nonempty (SL(2, F) ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
  let σ := FiniteField.ringEquivOfCardEq hcard
  exact ⟨{ toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
           invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
           left_inv := fun A => by
             ext i j
             simp [Matrix.SpecialLinearGroup.map_apply_coe]
           right_inv := fun A => by
             ext i j
             simp [Matrix.SpecialLinearGroup.map_apply_coe]
           map_mul' := (Matrix.SpecialLinearGroup.map σ.toRingHom).map_mul }⟩

theorem mem_center_of_coe_eq_neg_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {t : spinGroup Q} (ht : (t : CliffordAlgebra Q) = -1) :
    t ∈ center (spinGroup Q) := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ht, mul_neg_one, neg_one_mul]

section Frame

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {m : ℕ} (F : HypFrame Q m)

omit [Finite K] in
theorem range_longSL2_inf_center {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (hZ : F.longSL2 hij s t (-1) ∉ center (spinGroup Q)) :
    (F.longSL2 hij s t).range ⊓ center (spinGroup Q) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [mem_inf] at ha
  obtain ⟨⟨A, rfl⟩, haZ⟩ := ha
  have hA : A ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro B
    apply T1.longSL2_injective F hij s t
    rw [map_mul, map_mul]
    exact mem_center_iff.mp haZ _
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff A).mp hA with rfl | rfl
  · rw [map_one]
    exact one_mem _
  · exact absurd haZ hZ

include F in
theorem rawF3_of_frame (hm : 3 ≤ m) (hK3 : Nat.card K = 3)
    (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (hZ : ∀ x ∈ center (spinGroup Q), ∃ c : K, ∀ v, spinAction Q x v = c • v) (hQ : Q ≠ 0)
    {t : spinGroup Q} (ht : (t : CliffordAlgebra Q) = -1) : RawF3 (spinGroup Q) t := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hki : (⟨2, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have hkj : (⟨2, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have htZ := mem_center_of_coe_eq_neg_one ht
  have hx : F.longSL2 hij true false (-1) = t * F.longSL2 hij true true (-1) := by
    have h1 : F.longSL2 hij true false (-1) =
        spinGroup.negOne Q hQ * F.longSL2 hij true true (-1) :=
      T1.longSL2_neg_one_not F hij hQ true true
    have h2 : spinGroup.negOne Q hQ = t := Subtype.ext (by rw [spinGroup.coe_negOne, ht])
    rw [h1, h2]
  have huZ := DA.longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true true
  have hxZ := DA.longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true false
  have hCt : centralizer ({F.longSL2 hij true false (-1)} : Set (spinGroup Q)) =
      centralizer {F.longSL2 hij true true (-1)} := by
    rw [hx]
    exact T1.centralizer_mul_of_mem_center htZ
  obtain ⟨eK⟩ := nonempty_sl2_equiv_zmod_three hK3
  have h₂C := T1.range_longSL2_le_centralizer F hij true false
  have h₂s := isSubnormal_range_longSL2_of_odd F hij hodd hrange true false
  rw [hCt] at h₂C h₂s
  refine ⟨F.longSL2 hij true true (-1), T1.orderOf_longSL2_neg_one F hij hodd true true, huZ,
    (F.longSL2 hij true true).range, (F.longSL2 hij true false).range,
    T1.range_longSL2_le_centralizer F hij true true,
    isSubnormal_range_longSL2_of_odd F hij hodd hrange true true,
    MonoidHom.mem_range.mpr ⟨-1, rfl⟩, range_longSL2_inf_center F hij true true huZ,
    ⟨(MonoidHom.ofInjective (T1.longSL2_injective F hij true true)).symm.trans eK⟩,
    .inr ⟨h₂C, h₂s, range_longSL2_inf_center F hij true false hxZ,
      ⟨(MonoidHom.ofInjective (T1.longSL2_injective F hij true false)).symm.trans eK⟩⟩, .inr ?_⟩
  rw [← hx]
  exact MonoidHom.mem_range.mpr ⟨-1, rfl⟩

end Frame

theorem rowDAThree : RowDAThree := by
  constructor
  · intro K _ _ m hK3 hm Y _ _ α hα hk t ht ht2
    have : NeZero m := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus m K)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := m))
    obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) (by omega : 3 ≤ m)
    exact (rawF3_of_frame (plusFrame m K (by omega)) (by omega) hK3
      (range_spinAction_quadPlus (by omega)).le (DA.smul_of_le_comap (hZ.symm.trans hcomap).le)
      (nondegenerate_quadPlus m K).ne_zero ht).concl3
      (isQuasisimple_spinGroup_quadPlus (by omega)) hα hk ht2 (mem_center_of_coe_eq_neg_one ht)
  · intro K _ _ m b c hirr hK3 hm Y _ _ α hα hk t ht ht2
    have : Finite (spinGroup (quadMinus m K b c)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := m) hirr)
    obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hm hirr
    exact (rawF3_of_frame (Twisted.minusFrame m b c).toHypFrame (by omega) hK3
      (range_spinAction_quadMinus hm hirr).le (DA.smul_of_le_comap (hZ.symm.trans hcomap).le)
      (nondegenerate_quadMinus_of_finite m K hirr).ne_zero ht).concl3
      (isQuasisimple_spinGroup_quadMinus hm hirr) hα hk ht2 (mem_center_of_coe_eq_neg_one ht)

theorem rowBThree :
    RowBThree := by
  intro Y _ _ hq hZ τ n hτ hlie hc t ht htZ
  subst hτ
  rcases hlie with ⟨-, ⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := LieType.BorelTits.charP_of_natCard_eq (f := 1) (by rw [hK3, pow_one])
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd (n := n) h2)
  obtain ⟨hβs, -, hβk⟩ := spinToStatedProj_quadOdd h2 hn
  obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover hβs
    (fun E _ _ π hπ hcen h2k => by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2k
      exact LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_coprime
        (p := 3) h2 hn hπ hcen (by rw [hk]; exact Nat.Coprime.pow_right k (by norm_num)))
    hq hZ e
  rw [hβk] at hαZ hαk
  obtain ⟨t', ht'Z, rfl⟩ := (show t ∈ (center (spinGroup (quadOdd n K))).map α from
    hαZ ▸ htZ)
  have hQ : quadOdd n K ≠ 0 := (nondegenerate_quadOdd n K).ne_zero
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hz2 : orderOf (spinGroup.negOne (quadOdd n K) hQ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact spinGroup.negOne_mul_self _ hQ)
      (spinGroup.negOne_ne_one _ hQ)
  rw [T1.center_spinGroup_quadOdd h2 hn] at ht'Z
  have ht'1 : t' ≠ 1 := fun h1 => by
    rw [h1, map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht' : (t' : CliffordAlgebra (quadOdd n K)) = -1 := by
    rcases eq_one_or_eq_of_mem_zpowers hz2 ht'Z with h1 | h1
    · exact absurd h1 ht'1
    · rw [h1, spinGroup.coe_negOne]
  have hZodd : ∀ x ∈ center (spinGroup (quadOdd n K)),
      ∃ c : K, ∀ v, spinAction (quadOdd n K) x v = c • v := by
    intro x hx
    rw [T1.center_spinGroup_quadOdd_eq_ker h2 hn, MonoidHom.mem_ker] at hx
    exact ⟨1, fun v => by rw [hx, one_smul]; rfl⟩
  exact (rawF3_of_frame (oddFrame n K).toHypFrame hn hK3 (range_spinAction_quadOdd h2 hn).le
    hZodd hQ ht').concl3 (isQuasisimple_spinGroup_quadOdd h2 hn) hαs hαk ht
    (mem_center_of_coe_eq_neg_one ht')

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
