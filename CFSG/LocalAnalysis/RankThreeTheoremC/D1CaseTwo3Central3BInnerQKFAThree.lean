module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28Group
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.HallHigman
open CFSG.ComponentClassification.OuterAutomorphisms

open scoped commutatorElement

namespace InnerQ.KFAThree

variable {X : Type} [Group X] [Finite X] {T : Sylow 3 X} {X₀ : Subgroup X} {x : X}

theorem not_isCyclic_sup (hxo : orderOf x = 3) {K D : Subgroup X} (hxK : x ∉ K)
    (hDK : D ≤ K) (hD1 : D ≠ ⊥) (hDp : IsPGroup 3 D) : ¬ IsCyclic (D ⊔ zpowers x : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcyc
  obtain ⟨n, hn⟩ := hDp.exists_card_eq
  have h3D : 3 ∣ Nat.card D := by
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hD1
    · rw [hn]
      exact dvd_pow_self 3 (Nat.succ_ne_zero n)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3D
  set C := D ⊔ zpowers x
  have hdC : (d : X) ∈ C := mem_sup_left d.2
  have hxC : x ∈ C := mem_sup_right (mem_zpowers x)
  have heq : zpowers (⟨d, hdC⟩ : C) = zpowers (⟨x, hxC⟩ : C) := by
    refine (IsCyclic.subgroup_eq_iff_card_eq).mpr ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk,
      Subgroup.orderOf_coe, hd, hxo]
  have hxd : (⟨x, hxC⟩ : C) ∈ zpowers (⟨d, hdC⟩ : C) := heq ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := hxd
  have hxk : x = (d : X) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  exact hxK (hxk ▸ zpow_mem (hDK d.2) k)

end InnerQ.KFAThree

end CFSG.LocalAnalysis.RankThreeTheoremC
