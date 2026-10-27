module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015E6Cen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015E6Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015
open CFSG.Blueprint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
open CFSG.RankThree.PerfectCover (hopfMultiplier)

namespace CatB.I1015

section Field

theorem exists_field {n : ℕ} (hn : 0 < n) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nat.card k = (2 ^ n) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, inferInstance, by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]⟩

theorem field_data_of_card {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ} (hn : Odd n)
    (hk : Nat.card k = (2 ^ n) ^ 2) :
    ∃ (θ : k →+* k) (t : kˣ), (∀ c, θ c = c ^ 2 ^ n) ∧ (∀ c, θ (θ c) = c) ∧ t ^ 3 = 1 ∧ t ≠ 1 ∧
      Units.map (θ : k →* k) t = t ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype k := Fintype.ofFinite k
  have hK : Fintype.card k = 2 ^ n * 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hk, sq]
  obtain ⟨c, hc⟩ := three_dvd_two_pow_add_one hn
  have h2n : 2 ^ n = 3 * (c - 1) + 2 := by
    generalize 2 ^ n = m at hc ⊢
    omega
  refine ⟨iterateFrobenius k 2 n, ?_⟩
  have hθq : ∀ x : k, iterateFrobenius k 2 n x = x ^ 2 ^ n := fun x => rfl
  have h3 : 3 ∣ Nat.card kˣ := by
    rw [Nat.card_units, hk]
    have h1 : (2 ^ n) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : 2 ^ n % 3 = 2 := by omega
      rw [this]
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) 3 h3
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht3' : (t : k) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ht3, Units.val_one]
  refine ⟨t, hθq, fun x => ?_, ht3, ?_, ?_⟩
  · rw [hθq, hθq, ← pow_mul, ← hK, FiniteField.pow_card]
  · intro h
    rw [h, orderOf_one] at ht
    omega
  · apply Units.ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    change iterateFrobenius k 2 n (t : k) = (t : k) ^ 2
    rw [hθq]
    rw [h2n, pow_add, pow_mul, ht3', one_pow, one_mul]

end Field

section Fixed


theorem finite_fixedGroup {k : Type} [Field k] [Finite k] (θ : k →+* k) :
    Finite (fixedGroup k θ) := by
  haveI : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  haveI : Finite (e6Data_valid.minGroup k) := inferInstance
  infer_instance

end Fixed

section Bridge


set_option linter.unusedSectionVars false in
theorem fixedGroup_equiv_tauCeti {k : Type} [Field k] [Finite k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hk : Nat.card k = (q.p ^ q.exponent) ^ 2) (hθq : ∀ c, θ c = c ^ q.p ^ q.exponent) :
    Nonempty (↥(fixedGroup k θ) ⧸ Subgroup.center ↥(fixedGroup k θ) ≃*
      ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
  have hlie := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieModel_twistedE6_fixed θ hθ
    q.prime_p q.exponent_pos hk hθq
  rcases hlie with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, PrimePower.card_def]) σ (fun x => by rw [hσ, PrimePower.card_def])
    exact ⟨e.trans b⟩
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

end Bridge

end CatB.I1015

section Holds


theorem te6Rank_holds : TE6Rank := by
  intro Q _ _ hQ hZ n₀ hn hcat
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨q, hv, hp, hf, ⟨e⟩⟩ := lieIndex_isTE6n hcat
  obtain ⟨p, n, hp', hex'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : n = n₀ := hf
  obtain ⟨k, _, _, _, hk⟩ := exists_field hex'
  obtain ⟨θ, t, hθq, hθ, ht3, ht1, hθt⟩ := field_data_of_card hn hk
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  haveI := finite_fixedGroup θ
  have hU : Group.IsPerfect (fixedGroup k θ) := fixedGroup_isPerfect_of_four_le_card θ hθ hk4
  obtain ⟨e1⟩ := fixedGroup_equiv_tauCeti θ hθ ⟨2, n, hp', hex'⟩ hv hk hθq
  have hm : CFSG.Models.LieModel
      (↥(fixedGroup k θ) ⧸ Subgroup.center ↥(fixedGroup k θ)) .twistedE6 0 2 n :=
    CFSG.Models.lieModel_of_namesTag ⟨hp', hex', rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e1
  obtain ⟨hfin, hcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hm
  haveI := hfin
  have hord : Nat.card (hopfMultiplier
      (↥(fixedGroup k θ) ⧸ Subgroup.center ↥(fixedGroup k θ))) ∣ 24 := by
    rw [hcard]
    exact orders_twistedE6_dvd n
  obtain ⟨Y, u, z, hY, hYc, hu2, hu, hYu, hz, hz3, hz1, hzY⟩ := e6_exists_Y θ hθ ht3 ht1 hθt
  exact te6_assembly hU ⟨hQ.1⟩ hZ (e.trans e1.symm) hord hY hYc hu2 hu hYu hz hz3 hz1 hzY

theorem i1015twoAt_holds (G : Type) [Group G] [Finite G] : I1015twoAt G :=
  i1015twoAt_of_TE6Rank te6Rank_holds G

theorem i1015coverAt_holds (G : Type) [Group G] [Finite G] : I1015coverAt G :=
  i1015coverAt_of_TE6Rank te6Rank_holds G

end Holds

end CFSG.LocalAnalysis.GLTheoremA
