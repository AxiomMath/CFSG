module

public import CFSG.LieType.ChevTwo.OppositeFixedExcReeInner
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeStd
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
public import CFSG.LieType.ChevTwo.OppositeFixedExcF4Dual
public import CFSG.LieType.ChevTwo.OppositeFixedExcTits
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Open

section Cert


theorem ree_hstd_F4 {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (Q : Subgroup ↥(ReeTag.F4.reeGamma K a)) (hQ : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q) :
    ∃ (g : ↥(ReeTag.F4.reeGamma K a)) (j : Option (Fin ReeTag.F4.fixedOrbitCount)),
      (∀ x ∈ Subgroup.normalizer (Q : Set ↥(ReeTag.F4.reeGamma K a)),
        g⁻¹ * x * g ∈
          (parabolicSubgroup Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a)) ∧
      ∀ q ∈ Q, g⁻¹ * q * g ∈
        (parabolicRadical Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a) := by
  obtain ⟨g, j, h1, h2⟩ := ree_standard_position (t := ReeTag.F4) Q hQ hQ2
  have e : reeAset j = reeStdSet ReeTag.F4 j := by cases j <;> rfl
  refine ⟨g, j, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem ringAut_eq_one_of_card_two {K : Type} [Field K] (hK2 : Nat.card K = 2) (δ : RingAut K) :
    δ = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK2
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · subst hx
    simp
  · have hδx : δ x ≠ 0 := fun h0 => hx ((map_eq_zero_iff δ δ.injective).1 h0)
    have h1 : δ x = y := huniq (δ x) hδx
    have h2 : x = y := huniq x hx
    change δ x = x
    rw [h1, h2]

theorem oppositeFixedInner_reeGamma_zero {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK2 : Nat.card K = 2) :
    OppositeFixedInner ↥(ReeTag.F4.reeGamma K 0) := by
  have hK : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK2
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma K 0) = ⊥ :=
    large_Ree_fixed_group_center_trivial 0 K hK
  intro p hp hp2 R hR hRinn Q hQ hQ2 hcore hne hRQ hC
  have key := oppositeFixedAt_reeGamma_inner hK
    (fun {A} {S} hS hodd {u} hu hu1 hfix => exists_fixed_mem_oppRadical_F4 hS hodd hu hu1 hfix)
    reeAset reeAset_perm ree_hstd_F4
    (fun p hp hp2 R hR hRinn =>
      uniqueNormalFormRee_of_inner hZ (ringAut_eq_one_of_card_two hK2) hRinn)
    p hp hp2 R hR hRinn Q
  exact key hQ hQ2 hcore hne hRQ hC

theorem oppositeFixed_of_reeTitsModel_twistedF4 {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a)
    (h : ReeTitsModel S .twistedF4 2 (2 * a + 1)) : OppositeFixed S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma ha h
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact oppositeFixed_of_mulEquiv e (oppositeFixed_reeGamma ha hK
    (fun {A} {S} hS hodd {u} hu hu1 hfix => exists_fixed_mem_oppRadical_F4 hS hodd hu hu1 hfix)
    ree_hstd_F4)

end Cert

section TitsCert


theorem oppositeFixed_of_titsModel_cert {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1) :
    OppositeFixed S :=
  CFSG.LieType.ChevTwo.oppositeFixed_of_titsModel h fun K _ _ _ hK2 =>
    CFSG.LieType.ChevTwo.oppositeFixedInner_of_mulEquiv (reeFixedEquivReeGamma K 0)
      (oppositeFixedInner_reeGamma_zero hK2)

end TitsCert

end CFSG.LieType.ChevTwo.Semi
