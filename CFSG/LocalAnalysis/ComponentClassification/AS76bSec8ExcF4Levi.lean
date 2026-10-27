module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassesC3Levi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenT
public import CFSG.GH74.Generic.Context

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction CFSG.SeitzReduction.F4Pilot
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped commutatorElement

theorem exists_mul_of_mem_sup_of_commute_F4 {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [one_mul]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)).symm }
  exact (sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩) : A ⊔ B ≤ P) hx

variable {K : Type} [Field K]

theorem commutator_rootSL2R_subgroupOf
    [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    ⁅(rootSL2R K).subgroupOf (adjointGroup .F4 K), (rootSL2R K).subgroupOf (adjointGroup .F4 K)⁆ =
      (rootSL2R K).subgroupOf (adjointGroup .F4 K) := by
  have hP : Group.IsPerfect (SL2 K) := CFSG.ComponentClassification.RankTwoL3Even.isPerfect_SL2 h4
  have hmap : ((rootSL2R K).subgroupOf (adjointGroup .F4 K)).map (adjointGroup .F4 K).subtype =
      rootSL2R K := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 rootSL2R_le_adjointGroup]
  apply map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_commutator, hmap, ← range_rootSL2_rootR, MonoidHom.range_eq_map, ← map_commutator,
    ← commutator_def, hP.commutator_eq_top]


theorem torusLineR_subgroupOf_ne_bot
    [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    (torusLineR K).subgroupOf (adjointGroup .F4 K) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := exists_three_le_orderOf h4
  intro hbot
  have hmem : (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) ∈ (torusLineR K).subgroupOf (adjointGroup .F4 K) :=
    mem_subgroupOf.2 ⟨c, rfl⟩
  rw [hbot, mem_bot] at hmem
  have h1 : rootDiagUnit .F4 (rDiag c) = 1 := congrArg Subtype.val hmem
  have h := rootDiagUnit_conj_pinnedX (rDiag c) isRoot_rootR (1 : K)
  rw [h1, one_mul, inv_one, mul_one, mul_one, rootChar_rDiag] at h
  have h2 := pinnedX_injective .F4 K rootR h
  have h3 : c ^ (2 : ℕ) = 1 := Units.ext (by simpa [rootR] using h2.symm)
  have := orderOf_le_of_pow_eq_one (by norm_num) h3
  omega

theorem odd_card_torusLineR_subgroupOf
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card ((torusLineR K).subgroupOf (adjointGroup .F4 K))) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
  exact odd_card_torusLineR hm hK

theorem leviData_levi
    [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) {m : ℕ}
    (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) :
    ∀ x ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]],
      LeviData (zx x) ((rootSL2R K).subgroupOf (adjointGroup .F4 K))
        ((torusLineR K).subgroupOf (adjointGroup .F4 K))
        ((torusLineR K).subgroupOf (adjointGroup .F4 K)) (C3Levi K) := by
  intro x hx
  have hxD : (x : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact f4Rep_mem_C3 _ (by simp)
    · exact f4Rep_mem_C3 _ (by simp)
    · exact f4Rep_mem_C3 _ (by simp)
    · exact f4Rep_mem_C3 _ (by simp)
  have hJx : ∀ j ∈ (rootSL2R K).subgroupOf (adjointGroup .F4 K), j ∈ cent x := fun j hj => by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_iff.1 (rootSpan_C3Set_le_centralizer_rootSL2R hxD) _
      (mem_subgroupOf.1 hj))
  have hTD : ∀ a ∈ (torusLineR K).subgroupOf (adjointGroup .F4 K), ∀ b ∈ C3Levi K,
      a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (torusLineR_subgroupOf_le_centralizer ha) b hb).symm
  exact
    { D_perfect := commutator_rootSL2R_subgroupOf h4
      D_le := fun j hj => mem_centralizer_iff.2 fun w hw => hw.2.1 j (hJx j hj)
      Q_le := fun t ht => mem_subgroupOf.2 (torusLineR_le_rootSL2R (mem_subgroupOf.1 ht))
      Q_ne_bot := torusLineR_subgroupOf_ne_bot h4
      odd_Q := odd_card_torusLineR_subgroupOf hm hK
      Q_le_H := le_rfl
      H_comm := fun a ha b hb =>
        (mem_centralizer_iff.1 (torusLineR_subgroupOf_le_centralizer_self hb) a ha)
      H_le := fun t ht => centralizer_le_normalizer _ (torusLineR_subgroupOf_le_centralizer ht)
      L_le := le_centralizer_iff.1 torusLineR_subgroupOf_le_centralizer
      cent_eq := fun c hc => by
        rw [centralizer_torusLineR_eq h4] at hc
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute_F4 hTD hc
        exact ⟨a, ha, by rwa [inv_mul_cancel_left]⟩
      quasisimple := isQuasisimple_open_C3Levi
      odd_center := by rw [center_C3Levi_eq_bot, Subgroup.card_bot]; exact odd_one
      Z_le := fun w hw => by
        rw [← centralizer_rootSL2R_eq_C3Levi h4]
        exact mem_centralizer_iff.2 fun j hj => (hw.2.1 j (hJx j hj)).symm }

theorem autFix_levi
    [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) :
    AutFix ((torusLineR K).subgroupOf (adjointGroup .F4 K)) (C3Levi K) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rintro α ⟨k, hk⟩ hQ hL
  obtain ⟨g, rfl, hg⟩ := exists_eq_conj_highestRootRankOne_of_fix_c3PerpLevi hm hK α fun x hx =>
    hL x (mem_C3Levi_iff.2 (by rw [← C3Set_eq_c3LeviRoots, C3Set_eq_c3PerpRoots]; exact hx))
  rw [highestRootRankOne_eq_rootSL2R] at hg
  have hgc : g ∈ centralizer ((torusLineR K).subgroupOf (adjointGroup .F4 K) :
      Set (adjointGroup .F4 K)) := mem_centralizer_iff.2 fun t ht => by
    have h := hQ t ht
    rw [MulAut.conj_apply] at h
    calc t * g = g * t * g⁻¹ * g := by rw [h]
      _ = g * t := by group
  rw [centralizer_torusLineR_eq h4] at hgc
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute_F4 (fun a ha b hb =>
    (mem_centralizer_iff.1 (torusLineR_subgroupOf_le_centralizer ha) b hb).symm) hgc
  have hbJ : (b : ModGL .F4 K) ∈ rootSL2R K := by
    have e : b = a⁻¹ * g := by rw [hab]; group
    rw [e, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem (torusLineR_le_rootSL2R (mem_subgroupOf.1 ha))) hg
  have hbD : (b : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
    rw [C3Set_eq_c3LeviRoots]
    exact mem_C3Levi_iff.1 hb
  have hb1 : b = 1 := Subtype.ext (Subgroup.disjoint_def.1 disjoint_rootSL2R_rootSpan_C3Set hbJ hbD)
  rw [hb1, mul_one] at hab
  have hgT : g ∈ (torusLineR K).subgroupOf (adjointGroup .F4 K) := hab ▸ ha
  have hgk : g ^ 2 ^ k = 1 := by
    rw [← map_pow] at hk
    have hc : g ^ 2 ^ k ∈ center (adjointGroup .F4 K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun β : MulAut (adjointGroup .F4 K) => β z) hk
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * g ^ 2 ^ k = g ^ 2 ^ k * z * (g ^ 2 ^ k)⁻¹ * g ^ 2 ^ k := by rw [this]
        _ = g ^ 2 ^ k * z := by group
    rw [center_adjointGroup_eq_bot] at hc
    exact Subgroup.mem_bot.1 hc
  have hodd : Odd (orderOf (⟨g, hgT⟩ : (torusLineR K).subgroupOf (adjointGroup .F4 K))) :=
    Odd.of_dvd_nat (odd_card_torusLineR_subgroupOf (by omega) hK) (orderOf_dvd_natCard _)
  have hdvd : orderOf (⟨g, hgT⟩ : (torusLineR K).subgroupOf (adjointGroup .F4 K)) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hgk))
  have h1 : orderOf (⟨g, hgT⟩ : (torusLineR K).subgroupOf (adjointGroup .F4 K)) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rcases j with _ | j
    · simpa using hj
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.2 (even_two.mul_left _))
  have hg1 : g = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  rw [hg1, map_one]

theorem statedClassicalModel_of_mulEquiv_C3Levi
    [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m) {L : Type} [Group L]
    (e : L ≃* rankTwoQuot (C3Levi K)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSp 3 2 m := by
  have h := CFSG.GH74.Generic.stated_of_lieModel_PSp (lieModel_C3Levi hK)
  have e₂ : rankTwoQuot (C3Levi K) ≃* ↥(C3Levi K) :=
    (QuotientGroup.quotientMulEquivOfEq center_C3Levi_eq_bot).trans QuotientGroup.quotientBot
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv (e.trans e₂).symm h

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
