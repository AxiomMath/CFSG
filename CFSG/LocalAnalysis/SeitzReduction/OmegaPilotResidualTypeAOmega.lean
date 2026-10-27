module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviCard
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinatePlusIsometry regular_coordinateQuadPlus)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.LieType.Universal.Spin (quadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Simple

theorem simple_perfect_orthDerived_coordinateQuadPlus {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup ↥(orthDerived (coordinateQuadPlus m K)) ∧
      Group.IsPerfect ↥(orthDerived (coordinateQuadPlus m K)) ∧
      ∃ a b : ↥(orthDerived (coordinateQuadPlus m K)), a * b ≠ b * a := by
  obtain ⟨hR, hT⟩ := regular_coordinateQuadPlus m K hm
  obtain ⟨hperf, hc, -, hsimple, ⟨a, b, hab⟩, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
  have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  have hbot := center_orthDerived_eq_bot' hR hT
    (CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hR)
  let e : ↥(orthDerived (coordinateQuadPlus m K)) ≃* ProjOrthDerived (coordinateQuadPlus m K) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq (hbot.symm.trans hc))
  exact ⟨MulEquiv.isSimpleGroup e, hperf, e.symm a, e.symm b,
    fun h => hab (by simpa using congrArg e h)⟩

theorem isSimpleGroup_orthDerived_coordinateQuadPlus {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup ↥(orthDerived (coordinateQuadPlus m K)) :=
  (simple_perfect_orthDerived_coordinateQuadPlus hm).1

omit [CharP K 2] in
theorem commutator_orthDerived_coordinateQuadPlus {m : ℕ} (hm : 3 ≤ m) :
    ⁅orthDerived (coordinateQuadPlus m K), orthDerived (coordinateQuadPlus m K)⁆ =
      orthDerived (coordinateQuadPlus m K) := by
  obtain ⟨hR, hT⟩ := regular_coordinateQuadPlus m K hm
  obtain ⟨hperf, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
  refine (Subgroup.map_subtype_commutator _).symm.trans ?_
  rw [hperf.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [CharP K 2] in
theorem exists_mul_ne_orthDerived_coordinateQuadPlus {m : ℕ} (hm : 3 ≤ m) :
    ∃ a b : ↥(orthDerived (coordinateQuadPlus m K)), a * b ≠ b * a := by
  obtain ⟨hR, hT⟩ := regular_coordinateQuadPlus m K hm
  obtain ⟨-, -, -, -, ⟨a, b, hab⟩, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

end Simple

section Order

open CFSG.ClassicalGroups.Orthogonal in
theorem card_elementaryGroup_quadPlus_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (Nat.card (elementaryGroup (quadPlus n K)) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : 0 < m + 1 := by omega
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (m + 1) K
  have hidx := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (regular_quadPlus (by omega)).2
    (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega))
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) m).2
  rw [hidx] at hO
  push_cast at hO
  rw [Nat.add_sub_cancel, show (m + 1) * m = m * (m + 1) by ring]
  linarith

theorem card_orthDerived_coordinateQuadPlus {m : ℕ} (hm : 3 ≤ m) :
    (Nat.card ↥(orthDerived (coordinateQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hE : orthDerived (quadPlus m K) = elementaryGroup (quadPlus m K) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hm
  rw [← Nat.card_congr (orthDerivedCongr (coordinatePlusIsometry m K)).toEquiv, hE]
  exact card_elementaryGroup_quadPlus_of_three_le hm

theorem card_orthDerived_coordinateQuadPlus_eq_mul_odd {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) {m : ℕ} (hm : 3 ≤ m) : ∃ O, Odd O ∧
      Nat.card ↥(orthDerived (coordinateQuadPlus m K)) = Nat.card K ^ (m * (m - 1)) * O := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow' (by omega)).mpr even_two
  refine ⟨(Nat.card K ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1),
    (odd_pow_sub_one hq hq1 (by omega)).mul
      (odd_prod_pow_sub_one hq hq1 _ _ fun i hi => by simp only [Finset.mem_Icc] at hi; omega), ?_⟩
  have h := card_orthDerived_coordinateQuadPlus (K := K) hm
  have e1 : ((Nat.card K ^ m - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
    push_cast
    ring
  have e2 : ((∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
    push_cast
    ring
  have key : (Nat.card ↥(orthDerived (coordinateQuadPlus m K)) : ℤ) =
      ((Nat.card K ^ (m * (m - 1)) * ((Nat.card K ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1)) : ℕ) : ℤ) := by
    rw [h, Nat.cast_mul, Nat.cast_mul, e1, e2]
    push_cast
    ring
  exact_mod_cast key

end Order

section Charts

theorem isEmpty_mulEquiv_statedSp_of_mulEquiv_orthDerived {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) {m : ℕ} (hm : 3 ≤ m) {G : Type*} [Group G]
    (e : G ≃* ↥(orthDerived (coordinateQuadPlus m K))) (r : ℕ) :
    IsEmpty (G ≃* StatedProj (StatedSp r K)) := by
  obtain ⟨O, hO, hcard⟩ := card_orthDerived_coordinateQuadPlus_eq_mul_odd hK hf hm
  exact isEmpty_mulEquiv_statedSp_of_card hK hf ((Nat.card_congr e.toEquiv).trans hcard) hO
    (mul_pred_ne_sq (by omega)) r

theorem spLeviSection_of_mulEquiv_orthDerived {C : Type*} [Group C] [Finite C]
    (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) (N : Subgroup ↥X) [N.Normal] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {m : ℕ} (hm : 3 ≤ m)
    (e : ↥X ⧸ N ≃* ↥(orthDerived (coordinateQuadPlus m K))) : SpLeviSection fp X N :=
  Or.inl fun r _ => isEmpty_mulEquiv_statedSp_of_mulEquiv_orthDerived hK hf hm e r

end Charts

end CFSG.SeitzReduction.OmegaPilot
