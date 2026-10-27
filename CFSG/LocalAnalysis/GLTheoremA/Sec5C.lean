module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5A
public import CFSG.LocalAnalysis.GLTheoremA.PCompJoin
public import CFSG.LocalAnalysis.GLTheoremA.PartIInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma54 {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) (h113 : I113UsedAt G p)
    {B L : Subgroup G} {x : G} (hBxL : IsS0Max p B x L) (K : Subgroup G)
    (hK : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  have hp := hc.prime
  by_contra hBK
  have hxS : IsSTriple p B x L := hBxL.1.1
  have hB : GLAIsBmax p B := hxS.1
  have hxB : x ∈ B := hxS.2.1.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hxS.2.2
  have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB.1 hxB
  obtain ⟨A, hA, hBA, -, hdecA, hAnc⟩ := h113 B x K hB hxS.2.1 hK hBK
  have hxK : x ∈ centModSubgroup p K := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
  have hxA : x ∈ A := hBA ⟨hxB, hxK⟩
  have hcl : closureIn K B ≤ centModSubgroup p L :=
    closureIn_le_centModSubgroup hp hBCx hK hL hBxL.2.2 hBK
  have hdec : ∀ a ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ a = u * v := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := hdecA a ha
    exact ⟨u, ⟨hu.2, hu.1⟩, v, hv.1, centMod_iff.2 (hcl hv.2), rfl⟩
  have h52 := lemma52 hc h51 hBxL hA hxA hdec
  apply hAnc
  have hle : (A ⊓ closureIn K B ⊓ centModSubgroup p K : Subgroup G) ≤ Subgroup.zpowers x :=
    fun v hv => (h52 v hv.1.1).1 (centMod_iff.2 (hcl hv.1.2))
  exact Subgroup.isCyclic_of_le hle

end CFSG.LocalAnalysis.GLTheoremA
