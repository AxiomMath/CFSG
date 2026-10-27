module

public import CFSG.GH74.GLS.Stage2.Local.Prop28Basic
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G]

theorem compsGood_of_sporadic {z : G} {S : Subgroup G} {n : ℕ} (h : Stage1Sporadic G z S n)
    (hn : 7 ≤ n ∧ n ≤ 11) : CompsGood z := by
  intro K hK
  have htop := isComponent_eq_top_of_isQuasisimple h.cover.1 hK
  subst htop
  exact Or.inr ⟨hK.1, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn.1, hn.2,
    TwoThin.isDoubleCoverOfAlt_of_mulEquiv Subgroup.topEquiv.symm h.cover⟩)))⟩

theorem compsGood_of_pair {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (h : Stage1Pair G z S q L₁ L₂) : CompsGood z := by
  intro K hK
  have hmem : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← h.comps]
    exact hK
  have hsl : HasSL2Model ↥K (fun r => r = q) := by
    rcases hmem with rfl | hmem
    · exact h.sl₁
    · rw [Set.mem_singleton_iff.mp hmem]
      exact h.sl₂
  obtain ⟨F, hF, hfin, hP, e⟩ := hsl
  exact Or.inr ⟨hK.1, Or.inr (Or.inl ⟨F, hF, hfin, hP ▸ h.odd, e⟩)⟩

theorem not_l2Meets_inG2_of_sporadic {z : G} {S : Subgroup G} {n : ℕ} (h : Stage1Sporadic G z S n)
    (hn : 7 ≤ n ∧ n ≤ 11) (hz : orderOf z = 2) : ¬ L2Meets G InG2 :=
  not_l2Meets_inG2_of_oneClass (compsGood_of_sporadic h hn) fun u hu => h.one_class z u hz hu

theorem not_l2Meets_inG2_of_pair_oneClass {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) : ¬ L2Meets G InG2 :=
  not_l2Meets_inG2_of_oneClass (compsGood_of_pair h) fun u hu => hone z u hz hu

end CFSG.GH74.GLS.Stage2.Local.Prop28
