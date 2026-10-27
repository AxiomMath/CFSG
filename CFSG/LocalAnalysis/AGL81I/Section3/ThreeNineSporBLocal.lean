module

import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveCentral
public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import CFSG.RankThree.Native.FiveLocalBasic
import CFSG.RankThree.Native.FiveLocalForms
import CFSG.RankThree.Native.FiveLocalInterface

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint
open CFSG.Monster.B.Pinned
open CFSG.RankThree.Native CFSG.RankThree.Native.FiveLocal

variable {G : Type*} [Group G]

private theorem card_center_P_eq {x h z : G} {q : Fin 4 → G} [Finite G]
    (hR : Rel x h q z) : Nat.card (Subgroup.center ↥(P x q)) = 5 := by
  have hzP : z ∈ P x q := Subgroup.mem_sup_left hR.z_mem
  have hcomm : ∀ y : P x q, Commute z (y : G) := fun y =>
    ((hR.mem_H0.1 (hR.P_le_H0 y.2)).2).symm
  have hle : Subgroup.center (P x q) ≤ (Subgroup.zpowers z).subgroupOf (P x q) := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.mem_zpowers_of_commute_P hR s.2
      fun g hg => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨g, hg⟩)).symm
  have hge : (Subgroup.zpowers z).subgroupOf (P x q) ≤ Subgroup.center (P x q) := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * (s : G) = (s : G) * (y : G)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [← hk]
    exact ((hcomm y).zpow_left k).eq.symm
  have hcenter : Subgroup.center (P x q) = (Subgroup.zpowers z).subgroupOf (P x q) :=
    le_antisymm hle hge
  calc Nat.card (Subgroup.center ↥(P x q))
      = Nat.card ((Subgroup.zpowers z).subgroupOf (P x q)) := by rw [hcenter]
    _ = Nat.card (Subgroup.zpowers z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hzP)).toEquiv
    _ = 5 := by rw [Nat.card_zpowers, hR.orderOf_z]

section ExponentB


theorem exists_exponent_five_B {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .B) :
    ∃ F : Subgroup L, Nat.card F = 5 ^ 5 ∧ ∀ g ∈ F, g ^ 5 = 1 := by
  let q : Fin 4 → L := e.symm ∘ qFive
  have hR : Rel (e.symm xFive) (e.symm hFive) q (e.symm zFive) := bFiveRel.map e.symm
  exact ⟨Q q, hR.card_Q, fun g hg => hR.pow_five_of_mem hg⟩

end ExponentB

section CenterSylowB


theorem card_center_sylow_B {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .B) :
    ∀ Q : Sylow 5 L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = 5 := by
  have h5L : (Nat.card L).factorization 5 = 6 := by
    rw [Nat.card_congr (e : L ≃* NativeSporadic.Carrier .B).toEquiv]
    exact factorization_card_B_five
  let q : Fin 4 → L := e.symm ∘ qFive
  have hR : Rel (e.symm xFive) (e.symm hFive) q (e.symm zFive) := bFiveRel.map e.symm
  intro S
  obtain ⟨T, hT⟩ := hR.P_sylow h5L
  let φ := Sylow.equiv T S
  rw [← Subgroup.map_center_eq φ, Subgroup.card_map_of_injective φ.injective, hT]
  exact card_center_P_eq hR

end CenterSylowB

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
