module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter CFSG.Glauberman.Dickson
open CFSG.ShultStronglyClosedTI
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem psl2UpperUnipotentHom_injective_of_charTwo [CharP K 2] :
    Function.Injective (psl2UpperUnipotentHom K) :=
  (LinearModel.psl2QuotientMap_injective (K := K)).comp sl2UpperUnipotentHom_injective

theorem involutionSubgroup_psl2UpperUnipotentSubgroup [CharP K 2] :
    involutionSubgroup (psl2UpperUnipotentSubgroup K) = (psl2UpperUnipotentHom K).range := by
  refine involutionSubgroup_eq fun x => ⟨fun ⟨hx, h2⟩ => ⟨hx, ?_⟩, fun ⟨hx, h1⟩ =>
    ⟨hx, LinearModel.orderOf_eq_two_of_mem_rootGroup hx h1⟩⟩
  rintro rfl
  rw [orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem psl2Borel_le_rootScalarSubgroup :
    psl2Borel K ≤ rootScalarSubgroup (psl2UpperUnipotentHom K) := by
  intro g hg
  rw [psl2Borel_eq_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rwa [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
  refine ⟨Units.mk0 (A.val 0 0 ^ 2) (pow_ne_zero 2 (left_ne_zero_of_mul_eq_one hdet)),
    fun b => ?_⟩
  change psl2QuotientMap K A * psl2QuotientMap K (sl2UpperUnipotent b) *
      (psl2QuotientMap K A)⁻¹ = psl2QuotientMap K (sl2UpperUnipotent (A.val 0 0 ^ 2 * b))
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]

theorem exists_conj_psl2UpperUnipotentHom [Finite K] {f : ℕ} (hf : f ≠ 0)
    (hcard : Nat.card K = 2 ^ f) (c : Kˣ) :
    ∃ g : PSL2 K, ∀ b : K, g * psl2UpperUnipotentHom K (Multiplicative.ofAdd b) * g⁻¹ =
      psl2UpperUnipotentHom K (Multiplicative.ofAdd (c * b)) := by
  have hcop : (Nat.card Kˣ).Coprime 2 := by
    rw [Nat.card_units, hcard, Nat.coprime_two_right]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hf⟩) odd_one
  obtain ⟨a, ha⟩ := (Nat.Coprime.pow_left_bijective hcop).2 c
  have ha' : a ^ 2 = c := ha
  have hA : splitTorusSLHom K a ∈ sl2Borel K :=
    (sl2_mem_stabilizer_infinity_iff _).mpr (by simp)
  refine ⟨psl2QuotientMap K (splitTorusSLHom K a), fun b => ?_⟩
  change psl2QuotientMap K (splitTorusSLHom K a) * psl2QuotientMap K (sl2UpperUnipotent b) *
      (psl2QuotientMap K (splitTorusSLHom K a))⁻¹ =
    psl2QuotientMap K (sl2UpperUnipotent (c * b))
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA, ← ha']
  simp

theorem isSingerAction_psl2 [Finite K] {f : ℕ} (hf : f ≠ 0) (hcard : Nat.card K = 2 ^ f)
    (Q : Sylow 2 (PSL2 K)) :
    IsSingerAction (involutionSubgroup (Q : Subgroup (PSL2 K))) (2 ^ f) := by
  have : CharP K 2 := LinearModel.charP_two_of_card hcard
  obtain ⟨Q₀, hQ₀⟩ := LinearModel.exists_sylow_eq_rootGroup hcard
  rw [← hcard]
  exact isSingerAction_sylow_of_range (psl2UpperUnipotentHom K)
    psl2UpperUnipotentHom_injective_of_charTwo Q₀
    (by rw [hQ₀]; exact involutionSubgroup_psl2UpperUnipotentSubgroup)
    ((psl2UpperUnipotent_normalizer_eq_borel K).le.trans psl2Borel_le_rootScalarSubgroup)
    (exists_conj_psl2UpperUnipotentHom hf hcard) Q

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
