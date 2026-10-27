module

public import CFSG.LargeExtraspecial.AS35ZMOdd
public import CFSG.LargeExtraspecial.AS35ZMPGMix
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.AS35DFinal
public import CFSG.LargeExtraspecial.AS35HInd
public import CFSG.LargeExtraspecial.AS35LMain
public import CFSG.LargeExtraspecial.AS35MSixEightC
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Certificate10091Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary

namespace AS35ZM

variable {X : Type} [Group X] {H : Subgroup X}

theorem commute_coe_iff {x y : H} : x * y = y * x ↔ (x : X) * y = y * x := by
  rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]

end AS35ZM

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem pg_data_ZM (h65 : S.SixFiveConcl) {k : ℕ} (hk : S.width = k + 2) {a b : S.O}
    (ha : a ∈ S.DbarAsc) (hb : b ∈ S.DbarAsc) (hab : a * b ≠ b * a) :
    (∀ f ∈ S.DbarAsc, ∀ f' ∈ S.DbarAsc, f * a = a * f → f * b = b * f → f' * a = a * f' →
      f' * b = b * f' → f * f' = f' * f → f ≠ f' →
        ∃ c ∈ S.DbarAsc, c * a = a * c ∧ c * b = b * c ∧ c * f' = f' * c ∧ c * f ≠ f * c) ∧
    (∃ F G : Fin (k / 2) → S.O, (∀ i, F i ∈ S.DbarAsc ∧ G i ∈ S.DbarAsc) ∧
      (∀ i, F i * a = a * F i ∧ F i * b = b * F i ∧ G i * a = a * G i ∧ G i * b = b * G i) ∧
      (∀ i, F i * G i ≠ G i * F i) ∧
      ∀ i j, i ≠ j → F i * F j = F j * F i ∧ F i * G j = G j * F i ∧
        G i * F j = F j * G i ∧ G i * G j = G j * G i) ∧
    (∃ e ∈ S.DbarAsc, ∃ d ∈ S.DbarAsc, d * a = a * d ∧ d * b = b * d ∧
      e * (a * b * e * (a * b)⁻¹) * (a * b) = a * b * (e * (a * b * e * (a * b)⁻¹)) ∧
      e * (a * b * e * (a * b)⁻¹) * a ≠ a * (e * (a * b * e * (a * b)⁻¹)) ∧
      e * (a * b * e * (a * b)⁻¹) * d ≠ d * (e * (a * b * e * (a * b)⁻¹))) := by
  have hk2 : 2 ≤ k := by have := h65.four_le_width; omega
  have hyp := S.hyp_L h65 hk
  have hD := hyp.isTClass ha
  obtain ⟨ψ₀⟩ := hyp.psu
  have hmem : ∀ {d : S.O}, d ∈ S.DbarAsc → d ∈ closure S.DbarAsc := fun hd => subset_closure hd
  have ha' : (⟨a, hmem ha⟩ : closure S.DbarAsc) ∈
      (Subtype.val ⁻¹' S.DbarAsc : Set (closure S.DbarAsc)) := ha
  have hb' : (⟨b, hmem hb⟩ : closure S.DbarAsc) ∈
      (Subtype.val ⁻¹' S.DbarAsc : Set (closure S.DbarAsc)) := hb
  have hab' : (⟨a, hmem ha⟩ : closure S.DbarAsc) * ⟨b, hmem hb⟩ ≠
      ⟨b, hmem hb⟩ * ⟨a, hmem ha⟩ := fun h => hab (AS35ZM.commute_coe_iff.1 h)
  obtain ⟨ψ, hψa, hψb⟩ := AS35ZM.exists_normalized hD hk2 ψ₀ ha' hb' hab'
  refine ⟨?_, ?_, ?_⟩
  · intro f hf f' hf' hfa hfb hf'a hf'b hff' hne
    obtain ⟨c, hc, hca, hcb, hcf', hcf⟩ := AS35ZM.exists_sep hD hk2 ψ ha' hb' hψa hψb
      (f := ⟨f, hmem hf⟩) (f' := ⟨f', hmem hf'⟩) hf hf'
      (AS35ZM.commute_coe_iff.2 hfa) (AS35ZM.commute_coe_iff.2 hfb)
      (AS35ZM.commute_coe_iff.2 hf'a) (AS35ZM.commute_coe_iff.2 hf'b)
      (AS35ZM.commute_coe_iff.2 hff') (fun h => hne (congrArg Subtype.val h))
    exact ⟨c, hc, AS35ZM.commute_coe_iff.1 hca, AS35ZM.commute_coe_iff.1 hcb,
      AS35ZM.commute_coe_iff.1 hcf', fun h => hcf (AS35ZM.commute_coe_iff.2 h)⟩
  · obtain ⟨F, G, hFG, hFGc, hFGn, hFGo⟩ := AS35ZM.exists_frame hD hk2 ψ ha' hb' hψa hψb
    refine ⟨fun i => (F i : S.O), fun i => (G i : S.O), fun i => hFG i, fun i => ?_,
      fun i h => hFGn i (AS35ZM.commute_coe_iff.2 h), fun i j hij => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hFGc i
      exact ⟨AS35ZM.commute_coe_iff.1 h1, AS35ZM.commute_coe_iff.1 h2,
        AS35ZM.commute_coe_iff.1 h3, AS35ZM.commute_coe_iff.1 h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hFGo i j hij
      exact ⟨AS35ZM.commute_coe_iff.1 h1, AS35ZM.commute_coe_iff.1 h2,
        AS35ZM.commute_coe_iff.1 h3, AS35ZM.commute_coe_iff.1 h4⟩
  · obtain ⟨e, he, d, hd, hda, hdb, hy, hya, hyd⟩ :=
      AS35ZM.exists_mix hD hk2 ψ ha' hb' hψa hψb
    refine ⟨e, he, d, hd, AS35ZM.commute_coe_iff.1 hda, AS35ZM.commute_coe_iff.1 hdb, ?_,
      fun h => hya ?_, fun h => hyd ?_⟩
    · have := congrArg Subtype.val hy
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    · apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    · apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

end Setting

end CFSG.LargeExtraspecial
