module

public import CFSG.Assembly.DichotomyDefs
import CFSG.Assembly.InvolutionGraph
import CFSG.Milestones.CLS_component_free_involution_odd_cores_trivial
import CFSG.Milestones.CLS_involution_centralizers_characteristic_two_transfer

public section

namespace CFSG.Assembly
namespace Dichotomy

theorem involutionGraph_disconnected_iff_stronglyEmbedded (G : Type) [Group G] [Finite G]
    (heven : Even (Nat.card G)) :
    ¬ (involutionGraph G).Preconnected ↔ ∃ M : Subgroup G, dichotomyStronglyEmbedded M := by
  constructor
  · intro hdisc
    obtain ⟨u, v, huv⟩ : ∃ u v, ¬ (involutionGraph G).Reachable u v := by
      simpa [SimpleGraph.Preconnected] using hdisc
    let Δ := (involutionGraph G).connectedComponentMk u
    let M : Subgroup G :=
      { carrier := {g | (fun t => g⁻¹ * t * g) '' InvolutionGraph.compSet Δ =
          InvolutionGraph.compSet Δ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at *
          have : (fun t => (a * b)⁻¹ * t * (a * b)) =
              (fun t => b⁻¹ * t * b) ∘ (fun t => a⁻¹ * t * a) := by
            funext t; simp [mul_assoc]
          rw [this, Set.image_comp, ha, hb]
        inv_mem' := by
          intro g hg
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hg]
          rw [Set.image_image]
          simp [mul_assoc] }
    have hne : (involutionGraph G).connectedComponentMk v ≠ Δ := fun h =>
      huv (SimpleGraph.ConnectedComponent.exact h.symm)
    exact ⟨M, InvolutionGraph.stronglyEmbedded_of_ne (fun _ => Iff.rfl) hne⟩
  · rintro ⟨M, hM⟩
    exact InvolutionGraph.not_preconnected_of_stronglyEmbedded M hM

theorem component_free_oddCore_eq_bot (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hcomp : ¬ IsComponentType G) (hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M)
    (t : G) (ht : orderOf t = 2) :
    oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
  _root_.CFSG.Milestones.cls_component_free_involution_odd_cores_trivial G hnonab hrank hcomp hse t ht

theorem component_free_centralizer_quotient_charTwo (G : Type) [Group G] [Finite G]
    (hcomp : ¬ IsComponentType G) (t : G) (ht : orderOf t = 2) :
    dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G) ⧸
        oddCore (Subgroup.centralizer ({t} : Set G))) ∧
      (oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ →
        dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G))) :=
  _root_.CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two G hcomp t ht

theorem charTwoType_of_involution_centralizers (G : Type) [Group G] [Finite G]
    (hC : ∀ t : G, orderOf t = 2 → dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G))) :
    IsCharTwoType G :=
  _root_.CFSG.Milestones.cls_involution_centralizers_characteristic_two_transfer G hC

theorem even_card_of_three_le_twoRank (G : Type) [Group G] [Finite G]
    (hrank : 3 ≤ twoRank G) : Even (Nat.card G) := by
  have hpos : 0 < twoRank G := by omega
  obtain ⟨k, ⟨E, -, -, hE⟩, hk⟩ := exists_lt_of_lt_csSup' hpos
  rw [even_iff_two_dvd]
  have h2 : 2 ∣ Nat.card E := by rw [hE]; exact dvd_pow_self 2 hk.ne'
  exact h2.trans (Subgroup.card_subgroup_dvd_card E)

end Dichotomy

open Dichotomy in
theorem component_dichotomy (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hconn : (involutionGraph G).Connected) : IsComponentType G ∨ IsCharTwoType G := by
  by_cases hcomp : IsComponentType G
  · exact Or.inl hcomp
  right
  have heven := even_card_of_three_le_twoRank G hrank
  have hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M := fun M hM =>
    (involutionGraph_disconnected_iff_stronglyEmbedded G heven).2 ⟨M, hM⟩ hconn.preconnected
  refine charTwoType_of_involution_centralizers G fun t ht => ?_
  exact (component_free_centralizer_quotient_charTwo G hcomp t ht).2
    (component_free_oddCore_eq_bot G hnonab hrank hcomp hse t ht)

end CFSG.Assembly
