module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.Open

theorem heis_isComponentOf_top {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    IsComponentOf (⊤ : Subgroup L) ⊤ :=
  ⟨le_rfl, IsSubnormal.refl _,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hq⟩

theorem isRestTwoOrG2_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsRestTwoOrG2 A) : IsRestTwoOrG2 B := by
  have hLie : ∀ P : TauCeti.LieTypeIndex → Prop, IsLieOf P A → IsLieOf P B := by
    rintro P ⟨d, hd, ⟨f⟩⟩
    exact ⟨d, hd, ⟨e.symm.trans f⟩⟩
  rcases h with h | h | h | h | h
  · exact Or.inl (hLie _ h)
  · exact Or.inr (Or.inl (hLie _ h))
  · exact Or.inr (Or.inr (Or.inl (hLie _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hLie _ h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem heis_not_dvd_center_rest (hZ : OddCenterRest) {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (h : IsRestTwoOrG2 (L ⧸ Subgroup.center L)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Subgroup.center L) := by
  let e₀ : (⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
  have hmap : (Subgroup.center ↥(⊤ : Subgroup L)).map e₀.toMonoidHom = Subgroup.center L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Subgroup.center ↥(⊤ : Subgroup L) := hy
      rw [Subgroup.mem_center_iff] at hy'
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e₀.surjective g
      have := hy' g'
      change e₀ g' * e₀ y = e₀ y * e₀ g'
      rw [← map_mul, ← map_mul, this]
    · intro hx
      refine ⟨e₀.symm x, ?_, by simp⟩
      have hx' := Subgroup.mem_center_iff.1 hx
      show e₀.symm x ∈ Subgroup.center ↥(⊤ : Subgroup L)
      rw [Subgroup.mem_center_iff]
      intro g
      apply e₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx' (e₀ g)
  let ι : ↥(⊤ : Subgroup L) ⧸ Subgroup.center ↥(⊤ : Subgroup L) ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.congr _ _ e₀ hmap
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup L)) = Nat.card (Subgroup.center L) :=
    Nat.card_congr (Subgroup.centerCongr e₀).toEquiv
  have h' : IsRestTwoOrG2 (↥(⊤ : Subgroup L) ⧸ Subgroup.center ↥(⊤ : Subgroup L)) :=
    isRestTwoOrG2_of_mulEquiv ι.symm h
  rw [← hcard] at hodd ⊢
  exact not_dvd_card_center_rest hZ (heis_isComponentOf_top hq) hodd h' hp hp5

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
