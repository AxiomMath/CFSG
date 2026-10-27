module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RF
public import CFSG.ClassicalInvolution.Asc77.AscMuTabHub

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub.Sys
open scoped MatrixGroups

section Std

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (S : Sys Q)

theorem stdFrame_incl (h2 : (2 : K) ≠ 0) {h : K} (hh : 2 * h = 1) (Y : Matrix (Fin 2) (Fin 2) K) :
    (S.stdFrame h2 hh).incl Y =
      S.dm ![h * (Y 0 0 + Y 1 1), h * (Y 1 0 - Y 0 1), 0, 0, h * (Y 0 0 - Y 1 1),
        h * (-Y 0 1 - Y 1 0)] := by
  rw [Frame.incl_apply]
  show Y 0 0 • S.dm (stdE1 h) + Y 1 1 • S.dm (stdF1 h) + (-Y 0 1) • S.dm (stdE2 h) +
    Y 1 0 • S.dm (stdF2 h) = _
  rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add]
  congr 1
  funext i
  fin_cases i <;> simp [stdE1, stdF1, stdE2, stdF2] <;> ring

@[expose] def swapMat (a b : K) (hab : a * a + b * b = -1) : SL(2, K) :=
  ⟨!![a, -b; -b, -a], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : K) * hab⟩

theorem coe_swapMat (a b : K) (hab : a * a + b * b = -1) :
    ((swapMat a b hab : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![a, -b; -b, -a] := rfl

theorem ovm_eq_incl_std (h2 : (2 : K) ≠ 0) {h : K} (hh : 2 * h = 1) (c : Fin 2 → K) :
    S.ovm c = (S.stdFrame h2 hh).incl !![c 0, -c 1; c 1, c 0] := by
  rw [stdFrame_incl, S.ovm_apply]
  congr 1
  funext i
  fin_cases i <;> simp [pad] <;>
    first | linear_combination (-(c 0)) * hh | linear_combination (-(c 1)) * hh

theorem La_std_ovm (h2 : (2 : K) ≠ 0) {h : K} (hh : 2 * h = 1) {a b : K}
    (hab : a * a + b * b = -1) (c : Fin 2 → K) :
    (S.stdFrame h2 hh).La (swapMat a b hab) (S.ovm c) =
      S.dm ![0, 0, 0, 0, a * c 0 - b * c 1, b * c 0 + a * c 1] := by
  rw [ovm_eq_incl_std S h2 hh, Frame.La_apply_incl, stdFrame_incl, coe_swapMat]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | (right; ring)
    | linear_combination (a * c 0 - b * c 1) * hh
    | linear_combination (b * c 0 + a * c 1) * hh

end Std

section Main

open CFSG.ClassicalInvolution.Balance.StrongBalance.Orth in
theorem elementaryGroup_le_normE_sup_hub {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (S : Sys Q)
    (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (h7 : 7 ≤ Module.finrank K V) {a b q h : K} (hab : a * a + b * b = -1) (hq : 4 * q = 1)
    (hh : 2 * h = 1) :
    elementaryGroup Q ≤ normE Q (S.hubFrame (two_ne_zero_of_odd_card' hodd) hab hq).La.range ⊔
      normE Q (S.stdFrame (two_ne_zero_of_odd_card' hodd) hh).La.range := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have hc := S.La_neg_one_comm h2 hab hq hh
  have hdim2 : Module.finrank K ↥((S.hubFrame h2 hab hq).span ⊓ (S.stdFrame h2 hh).span) = 2 := by
    rw [← negSpace_La_neg_one h2, ← negSpace_La_neg_one h2, S.inf_negSpace_eq h2 hab hq hh,
      LinearMap.finrank_range_of_inj (S.ovm_injective h2)]
    simp
  have hpd := Frame.pairDecomposition h2 hc.symm hdim2
  refine elementaryGroup_le_normE_sup_of_dim hQ hodd h5 h7 _ _ hc
    (hpd.finrank_U₂.trans hpd.finrank_U₃.symm) (swapMat a b hab) ?_
  intro x hx
  rw [S.inf_negSpace_eq h2 hab hq hh] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [La_std_ovm S h2 hh hab c]
  refine ⟨mem_posSpace_iff'.mpr ?_, mem_negSpace_iff'.mpr ?_⟩
  · rw [S.hub_La_neg_one h2 hab hq, D_dm, one_smul]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [S.std_La_neg_one h2 hh, D_dm, neg_one_smul, ← map_neg]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring

end Main

section Pair

open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

theorem unitaryPair_hub {K V K' : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]
    {Q : QuadraticForm K V} (S : Sys Q) (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K)) (hneg : ¬ IsSquare (-1 : K))
    {a b q h : K} (hab : a * a + b * b = -1) (hq : 4 * q = 1) (hh : 2 * h = 1) :
    UnitaryBlockStandardPair K' p f
      ((S.hubFrame (IsFundamental.two_ne_zero_of_odd hodd) hab hq).La.range ⊔
        (S.stdFrame (IsFundamental.two_ne_zero_of_odd hodd) hh).La.range)
      (S.hubFrame (IsFundamental.two_ne_zero_of_odd hodd) hab hq).La.range
      (S.stdFrame (IsFundamental.two_ne_zero_of_odd hodd) hh).La.range := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  refine unitaryPair_of_frames hK hK' hodd _ _ (S.La_neg_one_comm h2 hab hq hh) ?_ ?_
  · rw [S.inf_negSpace_eq h2 hab hq hh, LinearMap.finrank_range_of_inj (S.ovm_injective h2)]
    simp
  · rintro ⟨v, hv, hv0, hQ⟩
    rw [S.inf_negSpace_eq h2 hab hq hh] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [S.Q_ovm h2] at hQ
    apply hv0
    have h1 : c 1 = 0 := by
      by_contra h1
      exact hneg ⟨c 0 / c 1, by field_simp; linear_combination (-1 : K) * hQ⟩
    have h0 : c 0 = 0 := by
      rw [h1] at hQ
      simpa using hQ
    have : c = 0 := funext fun k => by fin_cases k <;> simp [h0, h1]
    rw [this, map_zero]

end Pair

end CFSG.ClassicalInvolution.Asc77.T7S2R
