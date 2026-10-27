module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyNorm
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open Certificates.A5GL42 (Mat4 GroupFacts NormFacts NoInvCent)
open scoped commutatorElement Matrix

theorem m2_of_model {G : Type} [Group G] [Finite G] {L P S : Subgroup G} {H NH T0 : Finset Mat4}
    (hP : A5Par L P) (hS : IsSylowTwoOf S P) (hQS : pCoreOf 2 P ≤ S) (hG : GroupFacts H)
    (hN : NormFacts H NH T0) (hC : NoInvCent H)
    (hpre : A5Pre P L (pCoreOf 2 P) (dsFrattini (pCoreOf 2 P)))
    (hfaith : ∀ p ∈ P, (∀ q ∈ pCoreOf 2 P, ⁅p, q⁆ ∈ dsFrattini (pCoreOf 2 P)) → p ∈ pCoreOf 2 P)
    (M : A5Model P L (pCoreOf 2 P) (dsFrattini (pCoreOf 2 P)) H) :
    (pCoreOf 2 P).relIndex S ∣ 8 ∧
      Odd ((pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P))) ∧
      (∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → (pCoreOf 2 P).relIndex S = 4) := by
  have hker : ∀ p : ↥P, M.F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P := by
    intro p
    refine ⟨fun hp => hfaith p p.2 fun q hq => ?_, M.core p⟩
    exact ElemFrame.comm_mem_of_M_eq_one M.F hpre.norm_E p hp hq
  have h4 : 4 ∣ Nat.card M.F.M.range := by
    have h60 : Nat.card ((L.subgroupOf P).map M.F.M) = 60 := by
      rw [M.card_map]; exact hG.2.2.2.1
    have hle : (L.subgroupOf P).map M.F.M ≤ M.F.M.range := Subgroup.map_le_range _ _
    have := Subgroup.card_dvd_of_le hle
    rw [h60] at this
    exact (show 4 ∣ 60 by norm_num).trans this
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P
  have hcore := m2_core hN hQ2 hS hQS M.F.M hker M.normP h4
  exact ⟨hcore.1, m2_odd hC M.F.M hker M.surjL, hcore.2⟩

theorem leafM2
    [DSLeaf LeafFrattiniChief] [DSLeaf LeafFrattiniFaithful] : LeafM2 := by
  intro G _ _ L P S h hS hQS
  have hC := frattini_chief h
  have hpre := hC.toPre
  have hF := a5Facts
  have hF2 := a5Facts2
  have hfaith := frattini_faithful h.charTwo
  rcases hpre.exists_model hF with ⟨_, ⟨M⟩⟩ | ⟨_, ⟨M⟩⟩
  · exact m2_of_model h hS hQS hF.groupN hF2.normN hF2.centN hpre hfaith M
  · exact m2_of_model h hS hQS hF.groupO hF2.normO hF2.centO hpre hfaith M

end CFSG.GH74.QTGen4.DSGen4
