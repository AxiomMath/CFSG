module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Gen
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeAutCore
public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeCosetPoints

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model CFSG.ComponentClassification.LiteratureLocal.SmallRee

theorem reeTitsModel_of_lieModel {Y : Type} [Group Y] {f : ℕ}
    (hm : LieModel Y .twistedG2 0 3 f) : ReeTitsModel Y .twistedG2 3 f :=
  (CFSG.Blueprint.LieModel.reeTitsModel hm (by decide)).2


section Gamma

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem ree_fieldAut_uIn (σ : K ≃+* K) (t b c : K) :
    ReeTag.G2.reeGammaFieldAut K a σ (uIn hK t b c) = uIn hK (σ t) (σ b) (σ c) := by
  apply Subtype.ext
  rw [ReeTag.coe_reeGammaFieldAut, uIn_val, uIn_val]
  exact entrywise_smallReeCoord σ.toRingHom t b c

theorem ree_fieldAut_map_U (σ : K ≃+* K) :
    ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom =
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hle : ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)).map
      (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom ≤
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, b, c, rfl⟩ := exists_uIn_eq hK (Subgroup.mem_subgroupOf.1 hu)
    change ReeTag.G2.reeGammaFieldAut K a σ (uIn hK t b c) ∈ _
    rw [ree_fieldAut_uIn hK]
    exact Subgroup.mem_subgroupOf.2 (uIn_mem hK _ _ _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom)
    (ReeTag.G2.reeGammaFieldAut K a σ).injective]

theorem ree_U_ne_bot :
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ≠ ⊥ := by
  intro h
  have h1 : uIn hK (1 : K) 0 0 ∈
      (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) :=
    Subgroup.mem_subgroupOf.2 (uIn_mem hK _ _ _)
  rw [h, Subgroup.mem_bot, ← uIn_zero hK] at h1
  exact one_ne_zero (uIn_inj hK h1).1

theorem ree_U_isPGroup :
    IsPGroup 3 ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)) :=
  (ReeTag.isPGroup_reeFixedPosUnipotent hK).of_equiv
    (Subgroup.subgroupOfEquivOfLe ReeTag.reeFixedPosUnipotent_le_reeGamma).symm

theorem ree_fieldAut_hNeg (σ : K ≃+* K) :
    ReeTag.G2.reeGammaFieldAut K a σ ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ =
      ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ := by
  apply Subtype.ext
  rw [ReeTag.coe_reeGammaFieldAut]
  have h1 : Units.map σ.toRingHom.toMonoidHom (-1 : Kˣ) = -1 := Units.ext (by simp)
  change Units.map (entrywiseHom σ.toRingHom) (smallReeTorusElt a K (-1)) =
    smallReeTorusElt a K (-1)
  rw [smallReeTorusElt, map_mul, entrywise_torusElt, entrywise_torusElt, map_pow, h1]

theorem ree_hNeg_orderOf :
    orderOf (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : ReeTag.G2.reeGamma K a) = 2 := by
  refine orderOf_eq_prime ?_ fun h => smallReeH_neg_one_ne_one (a := a) (K := K) ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, pow_two, OneMemClass.coe_one]
    exact smallReeH_neg_one_mul_self
  · exact congrArg Subtype.val h

omit hK in
theorem ree_core (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (α : MulAut (ReeTag.G2.reeGamma K a)) (hα : orderOf α = p)
    (hout : α ∉ (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range) :
    NormalizesPSub 3 α ∧ FixesInvolution α := by
  obtain ⟨-, δ, σ, -, hδ, -⟩ :=
    CFSG.RankThree.small_Ree_large_prime_field_coset_descent a ha K hK hp hp3 α hα hout
  refine ⟨normalizesPSub_of_conj δ ?_, fixesInvolution_of_conj δ ?_⟩
  · rw [hδ]
    exact ⟨_, ree_U_ne_bot hK, ree_U_isPGroup hK, ree_fieldAut_map_U hK σ⟩
  · rw [hδ]
    exact ⟨_, ree_hNeg_orderOf hK, ree_fieldAut_hNeg hK σ⟩

end Gamma

theorem ree_model_data {Y : Type} [Group Y] {f : ℕ} (h : ReeTitsModel Y .twistedG2 3 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      1 ≤ a ∧ Nat.card K = 3 ^ (2 * a + 1) ∧ Nonempty (Y ≃* ↥(ReeTag.G2.reeGamma K a)) := by
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier Y 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  exact ⟨a', K, inferInstance, inferInstance, this, ha, by rw [hK, hfa], ⟨E⟩⟩

theorem ree_ordP_noninner {Y : Type} [Group Y] {f : ℕ} (hm : ReeTitsModel Y .twistedG2 3 f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (α : MulAut Y) (hα : orderOf α = p)
    (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    NormalizesPSub 3 α ∧ FixesInvolution α := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data hm
  obtain ⟨h1, h2⟩ := ree_core ha hK hp hp3 (MulAut.congr e α) (by rw [orderOf_congr, hα])
    (congr_not_mem_range_conj e hout)
  exact ⟨normalizesPSub_of_congr e h1, fixesInvolution_of_congr e h2⟩

theorem ree_ordP_noninner_of_lieModel {Y : Type} [Group Y] {f : ℕ}
    (hm : LieModel Y .twistedG2 0 3 f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (α : MulAut Y)
    (hα : orderOf α = p) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    NormalizesPSub 3 α ∧ FixesInvolution α :=
  ree_ordP_noninner (reeTitsModel_of_lieModel hm) hp hp3 α hα hout

end CFSG.OddStandard.GH71.S55
