module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.FiveE

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem theta_adj (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h29 : Segev29) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y : G}
    (hx : IsConj a x) (hy : y ∈ orb2A a x) : θ y ∈ orb2A a' (θ x) := by
  have hmem : x ∈ gammaSet a z a := h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hmem
  have key : x ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪ orb5A a a ∪
      orb6A a a → θ y ∈ orb2A a' (θ x) := fun hx' =>
    ⟨hθ.typed h h' hα hy.1, (theta_clique_of_not_five_E hC hW hG h h' hα hθ hx' hy).1.2⟩
  rcases hmem with (((((((hxa | hx2A) | hx2B) | hx3A) | hx4A) | hx4B) | hx5A) | hx5E) | hx6A
  · rw [hxa] at hy ⊢
    exact theta_adj_self h h' hα hθ hy
  · exact key (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx2A))))))
  · exact key (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx2B))))))
  · exact key (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx3A)))))
  · exact key (Or.inl (Or.inl (Or.inl (Or.inr hx4A))))
  · exact key (Or.inl (Or.inl (Or.inr hx4B)))
  · exact key (Or.inl (Or.inr hx5A))
  · exact theta_five_E hC hW hG h29 h h' hα hθ hx5E hy
  · exact key (Or.inr hx6A)

end CFSG.EvenSporadicStandard.HNRecog.Section4
