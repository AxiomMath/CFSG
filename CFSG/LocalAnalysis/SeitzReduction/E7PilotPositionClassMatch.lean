module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF3Core
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOrder
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVF3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

local instance e7PositionClassMatchNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem fortytwo_le_card_filter_e7 :
    42 ≤ ((rootFinset Tag.E7).filter fun α : Fin Tag.E7.rank → ℤ =>
      0 < height α ∧ α 1 ≠ 0).card := by
  decide +kernel

theorem fortytwo_le_ncard_parabolicRadicalRoots_vNodes :
    42 ≤ (parabolicRadicalRoots .E7 vNodes).ncard := by
  have hi : (1 : Fin Tag.E7.rank) ∉ vNodes := fun h => h.1 rfl
  have hsub : (↑((rootFinset Tag.E7).filter fun α : Fin Tag.E7.rank → ℤ =>
      0 < height α ∧ α 1 ≠ 0) :
      Set (Fin Tag.E7.rank → ℤ)) ⊆ parabolicRadicalRoots .E7 vNodes := by
    intro α hα
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_rootFinset] at hα
    exact mem_parabolicRadicalRoots_iff.2 ⟨hα.1, hα.2.1, 1, hi, hα.2.2⟩
  have hfin : (parabolicRadicalRoots .E7 vNodes).Finite :=
    (rootFinset .E7).finite_toSet.subset fun α hα => mem_rootFinset.2 hα.1.1
  calc 42 ≤ _ := fortytwo_le_card_filter_e7
    _ = _ := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

variable {K : Type} [Field K]


theorem pow_le_card_radicalV [Finite K] : Nat.card K ^ 42 ≤ Nat.card (radicalV K) := by
  have hQC : parabolicRadical .E7 K vNodes ≤ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  rw [radicalV, card_map_of_injective (MulAut.conj _).injective, card_subgroupOf_of_le hQC,
    card_parabolicRadical]
  exact Nat.pow_le_pow_right Nat.card_pos fortytwo_le_ncard_parabolicRadicalRoots_vNodes

theorem vCoreRadical_sup_vLevi_le_normalizer [Finite K] [CharP K 2] :
    vCoreRadical K ⊔ vLevi K ≤ normalizer (radicalV K : Set (adjointGroup .E7 K)) :=
  sup_le (inf_le_right.trans le_normalizer) vLevi_le_normalizer_radicalV

theorem false_of_mulEquiv_f4_of_le_normalizer_radicalV [Finite K] [CharP K 2]
    {H : Subgroup (adjointGroup .E7 K)} (e : adjointGroup .F4 K ≃* H)
    (hHN : H ≤ normalizer (radicalV K : Set (adjointGroup .E7 K))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .E7 K) := finite_modGL
  set Q := radicalV K with hQ
  have hQp : IsPGroup 2 Q := isPGroup_radicalV
  have hO2 : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥ :=
    forall_normal_isPGroup_eq_bot_of_mulEquiv_symm e.symm
      forall_normal_isPGroup_eq_bot_adjointGroup_f4
  have hHQ : H ⊓ Q = ⊥ := by
    have hN : (Q.subgroupOf H).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.1 (hHN g.2) n).1 hn⟩
    have hbot := hO2 _ hN hQp.comap_subtype
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (mem_inf.1 hx).1⟩ : H) ∈ Q.subgroupOf H := mem_subgroupOf.2 (mem_inf.1 hx).2
    rw [hbot, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')
  set S : Subgroup (adjointGroup .E7 K) :=
    ((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)).map (H.subtype.comp e.toMonoidHom)
    with hS
  have hinj : Function.Injective (H.subtype.comp e.toMonoidHom) :=
    H.subtype_injective.comp e.injective
  have hScard : Nat.card S = Nat.card K ^ 24 := by
    rw [hS, card_map_of_injective hinj, card_posUnipotent_subgroupOf_f4]
  have hSH : S ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have hSp : IsPGroup 2 S := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact IsPGroup.of_card (n := (n : ℕ) * 24)
      (by rw [hScard, Nat.card_eq_fintype_card, hn, ← pow_mul])
  have hSQ : S ⊓ Q = ⊥ := eq_bot_iff.2 ((inf_le_inf_right _ hSH).trans hHQ.le)
  have hSQp : IsPGroup 2 (S ⊔ Q : Subgroup (adjointGroup .E7 K)) :=
    hSp.to_sup_of_normal_right' hQp (hSH.trans hHN)
  have hle := natCard_le_of_isPGroup_E7 hSQp
  have hge := card_mul_card_le_card_sup_of_inf_eq_bot hSQ
  have hQcard := pow_le_card_radicalV (K := K)
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h66 : Nat.card K ^ 66 ≤ Nat.card K ^ 63 :=
    calc Nat.card K ^ 66 = Nat.card K ^ 24 * Nat.card K ^ 42 := by rw [← pow_add]
      _ ≤ Nat.card S * Nat.card Q := by rw [hScard]; exact Nat.mul_le_mul_left _ hQcard
      _ ≤ _ := hge.trans hle
  have := (Nat.pow_le_pow_iff_right hq).1 h66
  omega

theorem not_nonempty_mulEquiv_uCore_vCore [Finite K] [CharP K 2] :
    ¬ Nonempty ((uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (vCoreRadical K ⊔ vLevi K : Subgroup (adjointGroup .E7 K))) := by
  rintro ⟨ψ⟩
  set Λu := uCoreRadical K ⊔ uLevi K with hΛu
  set Λv := vCoreRadical K ⊔ vLevi K with hΛv
  have hFu : uF4 K ≤ Λu := uF4_le_uLevi.trans le_sup_right
  set H : Subgroup (adjointGroup .E7 K) :=
    (((uF4 K).subgroupOf Λu).map ψ.toMonoidHom).map Λv.subtype with hH
  have eH : adjointGroup .F4 K ≃* H :=
    (uF4Equiv K).symm.trans ((subgroupOfEquivOfLe hFu).symm.trans
      ((((uF4 K).subgroupOf Λu).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
        ((((uF4 K).subgroupOf Λu).map ψ.toMonoidHom).equivMapOfInjective Λv.subtype
          Λv.subtype_injective)))
  have hHv : H ≤ Λv := map_subtype_le _
  exact false_of_mulEquiv_f4_of_le_normalizer_radicalV eH
    (hHv.trans vCoreRadical_sup_vLevi_le_normalizer)

end CFSG.SeitzReduction.E7Pilot
