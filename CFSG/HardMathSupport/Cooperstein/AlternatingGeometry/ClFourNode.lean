module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClFourPairs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSRange
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TransitiveSupport
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem false_of_four_isoPairs {X S L : Subgroup G}
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm : 8 < m) {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ)
    (hθS : ∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S)
    (hfour : Nat.card {x : Fin m // ∃ y, x < y ∧
      IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 4) : False := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  obtain ⟨a, a', hIso⟩ := exists_isoBlocks (((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
  have hι : Fintype.card {x : Fin m // ∃ y, x < y ∧
      IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hfour
  obtain ⟨U, D, hU2, hUN, hUnorm, hUsign, hD5, hΓ, hUfix, hUtrans⟩ :=
    PairFrame.exists_normal_two_group_of_fourPairs hIso hι (by simpa using hm)
  obtain ⟨π, hπ, hker, hAθ, hequiv, hf⟩ := hNS
  have hUr : U ≤ θ.range := by
    intro u hu
    obtain ⟨l, hl⟩ := hAθ u (mem_alternatingGroup.2 (hUsign u hu))
    exact ⟨⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩
  have hUS : U ≤ (S.subgroupOf (L ⊔ S)).map θ :=
    le_theta_S_of_normal_two hA' le_sup_right θ hθS _ rfl U hUN hU2 hUr
      (fun h hh _ u hu => hUnorm h hh u hu)
  have hPS : ∀ p ∈ U, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p := by
    intro p hp
    obtain ⟨s, hs, hsp⟩ := hUS hp
    obtain ⟨l, hl⟩ := hAθ p (mem_alternatingGroup.2 (hUsign p hp))
    refine ⟨l, ?_, hl⟩
    have h1 : θ (s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩) = 1 := by
      rw [map_mul, map_inv, hsp, hl, inv_mul_cancel]
    have h2 := hθS _ h1
    have h3 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have h4 : (l : G) = (s : G) * ((s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ : ↥(L ⊔ S)) : G) := by
      simp
    rw [h4]
    exact S.mul_mem h3 h2
  exact false_of_transitive_support hA hL hSL (by omega) ⟨π, hπ, hker, hAθ, hequiv, hf⟩ D hD5 hΓ U
    hPS hUfix hUtrans

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
