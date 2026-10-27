module

public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LieType.Simplicity.ReeLargeModel

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.LieType.BorelTits.Weighted

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeFixed_F4_center_eq_bot
    (a : ℕ) : Subgroup.center (reeFixed ReeTag.F4 K a) = ⊥ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hnorm : z ∈ Subgroup.normalizer
      (((nativeData ReeTag.F4.tag K).U.comap (reeFixed ReeTag.F4 K a).subtype :
        Subgroup (reeFixed ReeTag.F4 K a)) : Set (reeFixed ReeTag.F4 K a)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]
  have hzB : (z : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).B :=
    normalizer_le_of_fixedData (nrep ReeTag.F4.tag K) (nativeData ReeTag.F4.tag K).B
      (nativeData ReeTag.F4.tag K).U (reeFixed ReeTag.F4 K a) ReeTag.F4.relWeylRee
      (reeFixed_bruhat ReeTag.F4 K a) (nativeRootSubgroups ReeTag.F4.tag K).B_le_normalizer_U
      (by rw [CFSG.LieType.Chevalley.nrep_one]; exact one_mem _) (reeFixed_hUw ReeTag.F4 K a) hnorm
  have hc : nrep ReeTag.F4.tag K ((coxeterSystem ReeTag.F4.tag).wordProd ReeTag.F4.longWord) *
      (z : adjointGroup ReeTag.F4.tag K) *
      (nrep ReeTag.F4.tag K ((coxeterSystem ReeTag.F4.tag).wordProd ReeTag.F4.longWord))⁻¹ =
      z := by
    have h' := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz (reeLongRep ReeTag.F4 K a))
    simp only [Subgroup.coe_mul] at h'
    rw [h', mul_inv_cancel_right]
  exact Subtype.ext (eq_one_of_mem_B_of_commute_nrep
    (fun α => congrArg Subtype.val (wordProd_longWord_smul ReeTag.F4 α)) hzB hc)

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem exists_mulEquiv_reeFixed_of_model
    {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime) (a : ℕ),
      1 ≤ a ∧ Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) ∧
        Nonempty (S ≃* reeFixed ReeTag.F4 K a) := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hc' : CharP K ReeTag.F4.prime := hc
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := by
    rw [hK, hf]
    rfl
  have ha : 1 ≤ a := by omega
  have hperf := commutator_reeFixed_F4 a ha hK'
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  have e' := (e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm))).trans
    (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))
  exact ⟨K, inferInstance, inferInstance, hc', a, ha, hK', ⟨e'.trans
    ((QuotientGroup.quotientMulEquivOfEq (reeFixed_F4_center_eq_bot a)).trans
      QuotientGroup.quotientBot)⟩⟩

end CFSG.SectionRank
