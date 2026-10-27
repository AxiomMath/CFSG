module

public import CFSG.GH74.GLS.LU.Local.L3Facts
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK CFSG.RankThree.PerfectCover
open scoped MatrixGroups

theorem exists_surjective_of_card_hopfMultiplier_le
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀]
    [Finite (hopfMultiplier J)] (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (hcard : Nat.card (hopfMultiplier J) ≤ Nat.card p₀.ker) :
    ∃ α : S₀ →* E, Function.Surjective α := by
  have := hS₀
  have := hE
  have : Group.IsPerfect J := Group.IsPerfect.ofSurjective hp₀
  set h₀ : HopfCover J →* S₀ := hopfLift p₀ hp₀ hk₀
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hmap : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hcomp : ∀ u, p₀ (h₀ u) = hopfCoverMap J u := fun u =>
    DFunLike.congr_fun (comp_hopfLift p₀ hp₀ hk₀) u
  let ψ : hopfMultiplier J →* p₀.ker :=
    (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun m => by
      rw [← hmap]
      exact ⟨m, m.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨⟨m, hm⟩, rfl⟩
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le hcard
  have h₀i : Function.Injective h₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hum : u ∈ hopfMultiplier J := by
      change hopfCoverMap J u = 1
      rw [← hcomp, hu, map_one]
    have h1 : ψ ⟨u, hum⟩ = 1 := Subtype.ext hu
    exact congrArg Subtype.val (hψb.1 (h1.trans (map_one ψ).symm))
  let e : HopfCover J ≃* S₀ := MulEquiv.ofBijective h₀ ⟨h₀i, h₀s⟩
  refine ⟨(hopfLift p hp hk).comp e.symm.toMonoidHom, ?_⟩
  exact (hopfLift_surjective p hp hk).comp e.symm.surjective

theorem lieModel_psl_three {J : Type} [Group J] {p n : ℕ} (hp : p.Prime) (h5 : 5 ≤ p ^ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ n)
    (e : J ≃* StatedProj (StatedSL 3 F)) : CFSG.Models.LieModel J .PSL 3 p n := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  have hadm : StatedLieAdmissible .PSL 3 p n :=
    ⟨hp, hn, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  exact ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩

theorem lieModel_psu_three {J : Type} [Group J] {p n : ℕ} (hp : p.Prime) (h5 : 5 ≤ p ^ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ n) ^ 2)
    (e : J ≃* StatedProj (StatedSU 3 (p ^ n) F)) : CFSG.Models.LieModel J .PSU 3 p n := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  have hadm : StatedLieAdmissible .PSU 3 p n :=
    ⟨hp, hn, le_rfl, fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩

open CFSG.Blueprint in
theorem card_hopfMultiplier_psl_three
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] {p n : ℕ} (hp2 : p ≠ 2) (hm : CFSG.Models.LieModel J .PSL 3 p n) :
    Nat.card (hopfMultiplier J) = Nat.gcd 3 (p ^ n - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA J .PSL 3 p n hm
  have hgen : Multiplier.genericOrders .PSL 3 p n = (Nat.gcd 3 (p ^ n - 1), 1) := rfl
  have hexc : Multiplier.exceptionalOrders .PSL 3 p n = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold Multiplier.generic Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

open CFSG.Blueprint in
theorem card_hopfMultiplier_psu_three
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] {p n : ℕ} (hm : CFSG.Models.LieModel J .PSU 3 p n) :
    Nat.card (hopfMultiplier J) = Nat.gcd 3 (p ^ n + 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA J .PSU 3 p n hm
  have hgen : Multiplier.genericOrders .PSU 3 p n = (Nat.gcd 3 (p ^ n + 1), 1) := rfl
  have hexc : Multiplier.exceptionalOrders .PSU 3 p n = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold Multiplier.generic Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

theorem exists_cover_psl_three {J : Type} [Group J] {F : Type} [Field F]
    (e : J ≃* StatedProj (StatedSL 3 F)) :
    ∃ p₀ : SL(3, F) →* J, Function.Surjective p₀ ∧ p₀.ker = center SL(3, F) := by
  let φ := specialLinearGroupEquivStatedSL 3 F
  refine ⟨(e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom,
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)).comp φ.surjective, ?_⟩
  ext x
  have h1 : x ∈ ((e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom).ker ↔
      φ x ∈ (e.symm.toMonoidHom.comp (QuotientGroup.mk'
        ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)))).ker := Iff.rfl
  rw [h1, CFSG.LieType.Steinberg.ker_comp_mk' _ e.symm, ← map_center_eq_statedScalars]
  exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem exists_cover_psu_three {J : Type} [Group J] {q : ℕ} {F : Type} [Field F]
    (e : J ≃* StatedProj (StatedSU 3 q F)) :
    ∃ p₀ : ↥(StatedSU 3 q F) →* J, Function.Surjective p₀ ∧
      p₀.ker = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F) :=
  ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _),
    CFSG.LieType.Steinberg.ker_comp_mk' _ e.symm⟩

theorem card_scalars_statedSU_three {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) {F : Type} [Field F]
    (hF : Nat.card F = (p ^ n) ^ 2) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ n) F)) =
      Nat.gcd 3 (p ^ n + 1) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F :=
    ⟨hp, hn, by rw [hF, ← pow_mul, mul_comm]⟩
  have h1 := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars h (n := 3) (by norm_num)
  rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by norm_num)] at h1
  exact h1

theorem l3Cover (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    L3Cover := by
  intro J _ _ δ p n hp hp2 hδ h5 hJ E _ _ hE π hπ hker
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  rcases hJ with ⟨rfl, F, _, _, hF, ⟨e⟩⟩ | ⟨rfl, F, _, _, hF, ⟨e⟩⟩
  · refine ⟨fun _ => ⟨F, inferInstance, inferInstance, hF, ?_⟩, fun h => absurd h (by norm_num)⟩
    obtain ⟨p₀, hp₀, hk₀⟩ := exists_cover_psl_three e
    have hcardM := card_hopfMultiplier_psl_three hGA hp2 (lieModel_psl_three hp h5 hF e)
    have : Finite (hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hS₀ : Group.IsPerfect SL(3, F) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    refine exists_surjective_of_card_hopfMultiplier_le hS₀ hE p₀ hp₀ hk₀.le π hπ hker ?_
    rw [hcardM, hk₀, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num),
      hF]
  · refine ⟨fun h => absurd h (by norm_num), fun _ => ⟨F, inferInstance, inferInstance, hF, ?_⟩⟩
    obtain ⟨p₀, hp₀, hk₀⟩ := exists_cover_psu_three e
    have hcardM := card_hopfMultiplier_psu_three hGA (lieModel_psu_three hp h5 hF e)
    have : Finite (hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have : Fact p.Prime := ⟨hp⟩
    have hS₀ : Group.IsPerfect (StatedSU 3 (p ^ n) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        omega)
    refine exists_surjective_of_card_hopfMultiplier_le hS₀ hE p₀ hp₀ (by
      rw [hk₀]
      exact CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ n)) π hπ
      hker ?_
    rw [hcardM, hk₀, card_scalars_statedSU_three hp hn hF]

end CFSG.GH74.GLS.LU.Local
