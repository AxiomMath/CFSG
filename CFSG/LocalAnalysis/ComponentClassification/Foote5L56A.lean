module

public import CFSG.LocalAnalysis.OddStandard.Harada75Main
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

theorem gen4_twoGroup_of_e8 (hMW : MacWilliamsStatement) {S : Type} [Group S] [Finite S]
    (hS : IsPGroup 2 S) {A : Subgroup S} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hA8 : Nat.card A = 8)
    (hcent : ∀ x : S, (∀ a ∈ A, x * a = a * x) → x ∈ A) (P : Subgroup S) :
    ∃ s : Finset S, s.card ≤ 4 ∧ closure (s : Set S) = P := by
  by_cases hex : ∃ E : Subgroup S, E.Normal ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8
  · obtain ⟨E, hEn, hEab, hE8⟩ := hex
    have hcfg : OddStandard.Harada75.Cfg S A E :=
      { A_comm := hcomm
        A_sq := hsq
        A_card := hA8
        A_cent := hcent
        E_comm := fun a ha b hb =>
          congrArg (fun x : E => (x : S)) (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        E_sq := fun a ha => by
          rw [← pow_two]
          exact hEab.2 a ha
        E_card := hE8
        E_norm := fun s e he => hEn.conj_mem e he s }
    exact OddStandard.Harada75.gen4_of_noE32 hS (OddStandard.Harada75.noE32_of_cfg hS hcfg) P
  · push Not at hex
    exact hMW S hS (fun E hEn hEab => hex E hEn hEab) P

variable {G : Type} [Group G] [Finite G]

theorem gen4_of_selfCentralizing_e8 (hMW : MacWilliamsStatement) {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) {E : Subgroup G} (hET : E ≤ T)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hE8 : Nat.card E = 8) (hcent : ∀ y ∈ T, (∀ a ∈ E, y * a = a * y) → y ∈ E) :
    GH74.Gen4 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup T := E.subgroupOf T with hA
  have hA8 : Nat.card A = 8 := by
    rw [hA, show Nat.card (E.subgroupOf T) = Nat.card E from
      Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv, hE8]
  have hgen := gen4_twoGroup_of_e8 hMW hT.isPGroup (A := A)
    (fun a ha b hb => Subtype.ext (hcomm _ (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hb)))
    (fun a ha => Subtype.ext (hsq _ (mem_subgroupOf.mp ha))) hA8
    (fun x hx => mem_subgroupOf.mpr (hcent x x.2 fun a ha => by
      have h1 := hx ⟨a, hET ha⟩ (mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val h1))
  refine gen4_of_isSylowOf hT fun U hU => ?_
  obtain ⟨s, hs, hsU⟩ := hgen (U.subgroupOf T)
  refine ⟨s.image Subtype.val, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image]
  change closure ((T.subtype : T → G) '' (s : Set T)) = U
  rw [← MonoidHom.map_closure T.subtype s, hsU, subgroupOf_map_subtype, inf_of_le_left hU]

end CFSG.ComponentClassification.Foote5
