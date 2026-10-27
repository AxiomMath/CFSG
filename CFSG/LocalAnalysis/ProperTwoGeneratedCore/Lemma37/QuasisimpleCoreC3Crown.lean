module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3QuotientCent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CrownLemma
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem CaseC3.false_of_sylow {G : Type} [Group G] [Finite G] {T Q P₁ : Subgroup G} {e u y : G}
    (h : CaseC3 T Q P₁ e u y) (hperf : Group.IsPerfect G) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (S : Sylow 2 G) (hST : (S : Subgroup G) = T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := h.quaternion_right
  have hc := h.partC
  set S' := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hS' : (S' : Subgroup (G ⧸ Z)) = T.map (QuotientGroup.mk' Z) := by
    rw [Sylow.coe_mapSurjective, hST]
  obtain ⟨hyT, hyW, hy2⟩ := h.mk_facts Z hZ
  have hperf' : commutator (G ⧸ Z) = ⊤ := Group.isPerfect_def.mp inferInstance
  refine crown_lemma_of_perfect hperf' S' (W := (Q ⊔ P₁).map (QuotientGroup.mk' Z)) ?_ ?_
    (fun w hw => hc.pow_two_eq_one_of_mem_map_sup Z φ hZ hw) (hc.card_map_sup Z φ hZ)
    (y := (y : G ⧸ Z)) ?_ hyW hy2 (h.card_map_sup_inf_centralizer Z hZ)
  · rw [hS']
    exact Subgroup.map_mono hc.sup_le
  · rw [hS']
    exact hc.relIndex_map_sup Z hZ h.mem h.not_mem
  · change (y : G ⧸ Z) ∈ (S' : Subgroup (G ⧸ Z))
    rw [hS']
    exact hyT

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

omit [Finite J] in
theorem partCSylow_le_normalizer (T : Sylow 2 (quasiNormalizer u)) :
    partCSylow T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set J) :=
  Subgroup.map_subtype_le _

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
