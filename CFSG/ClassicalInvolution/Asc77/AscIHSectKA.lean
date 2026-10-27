module

public import CFSG.ClassicalInvolution.Phan.TorusAgree
public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem exists_orderOf_eq_two_part (C : Type*) [Group C] [Finite C] [IsCyclic C] :
    ∃ x : C, orderOf x = 2 ^ (Nat.card C).factorization 2 := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have hd : 2 ^ (Nat.card C).factorization 2 ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.ordProj_dvd _ _
  have h := IsCyclic.card_orderOf_eq_totient hd
  have hpos : 0 <
      (Finset.univ.filter fun a : C => orderOf a = 2 ^ (Nat.card C).factorization 2).card := by
    rw [h]
    exact Nat.totient_pos.mpr (by positivity)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

section TwoPart

theorem factorization_two_succ_of_mod_four (q : ℕ) (h : q % 4 = 1) :
    (q + 1).factorization 2 = 1 := by
  have hm : q + 1 = 2 * ((q + 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (q + 1) / 2 := by omega
  have hne : (q + 1) / 2 ≠ 0 := by omega
  rw [hm, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]

theorem factorization_two_pred_of_mod_four (q : ℕ) (h : q % 4 = 3) :
    (q - 1).factorization 2 = 1 := by
  have hm : q - 1 = 2 * ((q - 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (q - 1) / 2 := by omega
  have hne : (q - 1) / 2 ≠ 0 := by omega
  rw [hm, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]

theorem card_sl2_eq_mul (F : Type) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * ((Nat.card F - 1) * (Nat.card F + 1)) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  congr 1
  zify [hq, Nat.one_le_pow 2 (Nat.card F) hq]
  ring

theorem two_pow_sl2_of_one_mod_four (F : Type) [Field F] [Finite F] (hq : Nat.card F % 4 = 1) :
    2 ^ (Nat.card SL(2, F)).factorization 2 = 2 * 2 ^ (Nat.card F - 1).factorization 2 := by
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hq1 : Nat.card F - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ Nat.card F := by omega
  rw [card_sl2_eq_mul, Nat.factorization_mul (by omega) (Nat.mul_ne_zero hq1 (by omega)),
    Nat.factorization_mul hq1 (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, factorization_two_succ_of_mod_four _ hq]
  rw [zero_add, pow_add, pow_one, mul_comm]

theorem two_pow_sl2_of_three_mod_four (F : Type) [Field F] [Finite F] (hq : Nat.card F % 4 = 3) :
    2 ^ (Nat.card SL(2, F)).factorization 2 = 2 * 2 ^ (Nat.card F + 1).factorization 2 := by
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hq1 : Nat.card F - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ Nat.card F := by omega
  rw [card_sl2_eq_mul, Nat.factorization_mul (by omega) (Nat.mul_ne_zero hq1 (by omega)),
    Nat.factorization_mul hq1 (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, factorization_two_pred_of_mod_four _ hq]
  rw [zero_add, pow_add, pow_one]

end TwoPart

section Linear

variable {F : Type} [Field F] {X : Type} [Group X]

theorem LinearBlockStandardPair.exists_torus_elt {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) (x : Fˣ) :
    ∃ v ∈ V, v ∈ Subgroup.normalizer (U : Set X) ∧ orderOf v = orderOf x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  set c : SL(3, F) := WeakCT.blockSL F 3 2 1 (by omega) (WeakCT.torusHom F x) with hc
  have hcD : c ∈ WeakCT.D23 F := WeakCT.mem_D23_iff.mpr ⟨x, rfl⟩
  have key : ∀ d ∈ WeakCT.D23 F, ∀ u ∈ U, θ d * u * (θ d)⁻¹ ∈ U := by
    intro d hd u hu
    rw [← hU] at hu
    obtain ⟨m, hm, rfl⟩ := hu
    rw [← hU]
    refine ⟨d * m * d⁻¹, WeakCT.D23_conj_mem_B12 hd hm, ?_⟩
    simp [map_mul, map_inv]
  refine ⟨θ c, ?_, ?_, ?_⟩
  · rw [← hV]
    exact ⟨c, WeakCT.D23_le_B23 hcD, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => key c hcD u hu, fun hu => ?_⟩
    have := key c⁻¹ (inv_mem hcD) _ hu
    simpa [map_inv, mul_assoc] using this
  · have hinj : Function.Injective (θ.comp (WeakCT.blockSL F 3 2 1 (by omega))) :=
      WeakCT.comp_blockSL_injective hker (by omega) (by omega)
    calc orderOf (θ c) = orderOf ((θ.comp (WeakCT.blockSL F 3 2 1 (by omega)))
          (WeakCT.torusHom F x)) := rfl
      _ = orderOf (WeakCT.torusHom F x) := orderOf_injective _ hinj _
      _ = orderOf x := orderOf_injective _ (WeakCT.torusHom_injective (K := F)) x

end Linear

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem UnitaryBlockStandardPair.exists_torus_elt (hK : Nat.card K = (p ^ f) ^ 2)
    {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V)
    (u : normOne (unitaryInvolution K p f)) :
    ∃ v ∈ V, v ∈ Subgroup.normalizer (U : Set X) ∧ orderOf v = orderOf u := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  set c : Phan.Su K p f 3 := embSUid (unitaryInvolution K p f) 0
    (torusTwo (unitaryInvolution K p f) u) with hc
  have hcD : c ∈ Phan.D23 K p f := Phan.mem_D23_iff.mpr ⟨u, rfl⟩
  have key : ∀ d ∈ Phan.D23 K p f, ∀ w ∈ U, θ d * w * (θ d)⁻¹ ∈ U := by
    intro d hd w hw
    rw [← hU] at hw
    obtain ⟨m, hm, rfl⟩ := hw
    rw [← hU]
    refine ⟨d * m * d⁻¹, Phan.D23_conj_mem_B12 hK hd hm, ?_⟩
    simp [map_mul, map_inv]
  refine ⟨θ c, ?_, ?_, ?_⟩
  · rw [← hV]
    exact ⟨c, Phan.D23_le_B23 hcD, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key c hcD w hw, fun hw => ?_⟩
    have := key c⁻¹ (inv_mem hcD) _ hw
    simpa [map_inv, mul_assoc] using this
  · have hinj : Function.Injective (θ.comp (embSUid (unitaryInvolution K p f) 0)) :=
      Phan.comp_embSUid_injective hK hker 0
    calc orderOf (θ c) = orderOf ((θ.comp (embSUid (unitaryInvolution K p f) 0))
          (torusTwo (unitaryInvolution K p f) u)) := rfl
      _ = orderOf (torusTwo (unitaryInvolution K p f) u) := orderOf_injective _ hinj _
      _ = orderOf u := orderOf_injective _ (torusTwo_injective (unitaryInvolution K p f)) u

end Unitary

end CFSG.ClassicalInvolution.Asc77
