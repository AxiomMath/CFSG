module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)

section SL2

variable {k : Type} [Field k] {K : Type} [Field K]

theorem eq_one_of_ne_zero_of_natCard_eq_two' [Finite k] (hk : Nat.card k = 2) {x : k}
    (hx : x ≠ 0) : x = 1 := by
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hk, show 2 - 1 = 1 from rfl, pow_one] at h

theorem pow_three_eq_one_of_natCard_eq_four' [Finite K] (hK : Nat.card K = 2 ^ 2) (l : Kˣ) :
    l ^ 3 = 1 := by
  have := Fintype.ofFinite K
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h := FiniteField.pow_card_sub_one_eq_one (l : K) l.ne_zero
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem exists_conj_HSL_of_orderOf_eq_three [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {A : SL2 k}
    (hA : orderOf A = 3) :
    ∃ P : SL2 K, ∃ l : Kˣ, 3 ≤ orderOf l ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map ι A * P = HSL l := by
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  have hc := F4Pilot.apply_one_zero_ne_zero_of_orderOf_eq (A := A) (by rw [hA, hk])
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) k) = 1 := by
    refine eq_one_of_ne_zero_of_natCard_eq_two' hk fun ht => ?_
    have hA2 : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [F4Pilot.sq_eq_trace_smul_sub_one, ht, zero_smul, zero_sub, Matrix.neg_apply,
        CharTwo.neg_eq, Matrix.SpecialLinearGroup.coe_one]
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hA2
    omega
  obtain ⟨l, hl⟩ := F4Pilot.exists_three_le_orderOf (K := K) (by rw [hK]; norm_num)
  have hl3 : (l : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_eq_one_of_natCard_eq_four' hK l, Units.val_one]
  obtain ⟨hl1, hl2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hq : (l : K) ^ 2 - (1 : K) * l + 1 = 0 := by
    have h1 : ((l : K) - 1) * ((l : K) ^ 2 + l + 1) = 0 := by linear_combination hl3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)) hl1
    · linear_combination h + (-(l : K)) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hll : (l : K) ≠ ((l⁻¹ : Kˣ) : K) := by
    intro h
    refine hl2 (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    conv_lhs => rhs; rw [h]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc' :
      ((Matrix.SpecialLinearGroup.map ι A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (_root_.map_ne_zero _).2 hc
  have htr' : Matrix.trace ((Matrix.SpecialLinearGroup.map ι A : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.trace_fin_two,
      Matrix.map_apply, Matrix.map_apply, ← map_add, ← Matrix.trace_fin_two, htr, map_one]
  obtain ⟨P, hP⟩ := F4Pilot.exists_inv_mul_mul_eq_HSL _ hc' l (by rw [htr']; exact hq) hll
  exact ⟨P, l, hl, hP⟩

end SL2

section Theta


variable {k : Type} [Field k] {K : Type} [Field K]

theorem exists_conj_baseChangeGL_eq_highDiag_E6 [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {x : ModGL .E6 k}
    (hxJ : x ∈ EPilot.highRootSL2 .E6 k) (hx : orderOf x = 3) :
    ∃ n ∈ EPilot.highRootSL2 .E6 K, ∃ l : Kˣ, 3 ≤ orderOf l ∧
      n⁻¹ * baseChangeGL ι x * n = rootDiagUnit .E6 (EPilot.highDiag .E6 l) := by
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  rw [← range_rootSL2_highRoot] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = 3 := by
    rw [← hx, orderOf_injective _ rootSL2_highRoot_injective]
  obtain ⟨P, l, hl, hP⟩ := exists_conj_HSL_of_orderOf_eq_three hk hK ι hA
  refine ⟨rootSL2 .E6 K (highRoot .E6) P, rootSL2_highRoot_mem_highRootSL2 P, l, hl, ?_⟩
  rw [baseChangeGL_rootSL2_highRoot, ← map_inv, ← map_mul, ← map_mul, hP,
    rootSL2_highRoot_HSL (Or.inl rfl)]

theorem le_rootSpan_perpRoots_of_perfect_of_le_centralizer_E6 [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {x : ModGL .E6 k}
    (hxJ : x ∈ EPilot.highRootSL2 .E6 k) (hx : orderOf x = 3) {Q : Subgroup (ModGL .E6 K)}
    (hQ : ⁅Q, Q⁆ = Q) (hQC : Q ≤ adjointGroup .E6 K)
    (hQx : Q ≤ centralizer ({baseChangeGL ι x} : Set (ModGL .E6 K))) :
    Q ≤ rootSpan .E6 K (EPilot.perpRoots .E6) := by
  obtain ⟨n, hnJ, l, hl, hn⟩ := exists_conj_baseChangeGL_eq_highDiag_E6 hk hK ι hxJ hx
  obtain ⟨hl1, hl2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hnC : n ∈ adjointGroup .E6 K := EPilot.highRootSL2_le_adjointGroup hnJ
  set Q' := Q.map (MulAut.conj n⁻¹).toMonoidHom with hQ'
  have hQ'le : Q' ≤ torusGroup .E6 K ⊔ rootSpan .E6 K (EPilot.perpRoots .E6) := by
    rw [← EPilot.toralCentralizer_highDiag (Or.inl rfl) hl1 hl2]
    rintro _ ⟨q, hq, rfl⟩
    have hqx : q * baseChangeGL ι x = baseChangeGL ι x * q :=
      mem_centralizer_singleton_iff.1 (hQx hq)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (inv_mem hnC) (hQC hq)) hnC, ?_⟩
    rw [← hn]
    calc n⁻¹ * baseChangeGL ι x * n * (n⁻¹ * q * n) * (n⁻¹ * baseChangeGL ι x * n)⁻¹ =
        n⁻¹ * (baseChangeGL ι x * q) * (baseChangeGL ι x)⁻¹ * n := by group
      _ = n⁻¹ * q * n := by rw [← hqx]; group
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQ]
  have hQ'D : Q' ≤ rootSpan .E6 K (EPilot.perpRoots .E6) := by
    rw [← hQ'perf]
    exact (Subgroup.commutator_mono hQ'le hQ'le).trans
      (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer
        (fun x hx y hy => (triangular_borel_structure.{0, 0} .E6 K).1 x hx y hy)
        (torusGroup_le_normalizer_rootSpan fun α hα => hα.1))
  intro q hq
  have h1 : n⁻¹ * q * n ∈ rootSpan .E6 K (EPilot.perpRoots .E6) :=
    hQ'D ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have h2 : n * (n⁻¹ * q * n) * n⁻¹ = n⁻¹ * q * n := by
    rw [commute_of_mem_highRootSL2_of_mem_perpLevi (Or.inl rfl) hnJ h1, mul_inv_cancel_right]
  have h3 : q = n⁻¹ * q * n := by
    rw [← h2]
    group
  rw [h3]
  exact h1

end Theta

end CFSG.SeitzReduction.E6Pilot
