module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex

public section

namespace CFSG.SectionRank

open CFSG.Open

theorem pRank_top_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (H : Subgroup G) (hH : ¬ p ∣ H.index) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ CFSG.Open.pRank p H := by
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp.one_lt (⊤ : Subgroup G)
  have hP : IsPGroup p E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨g, hg⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      hp H hH E hP
  let E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom
  have hE'H : E' ≤ H := by
    rintro _ ⟨e, he, rfl⟩
    exact hg e he
  have hE'el : IsElemAbelian p E' := isElemAbelian_map hE _
  have hcard' : Nat.card E' = p ^ CFSG.Open.pRank p (⊤ : Subgroup G) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  exact le_pRank hp.one_lt hE'H hE'el hcard'

theorem pRank_top_le_of_mulEquiv_subgroup {G : Type*} [Group G] [Finite G]
    {G' : Type*} [Group G'] [Finite G'] {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (e : G' ≃* H) (hH : ¬ p ∣ H.index) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ CFSG.Open.pRank p (⊤ : Subgroup G') := by
  calc CFSG.Open.pRank p (⊤ : Subgroup G) ≤ CFSG.Open.pRank p H :=
        pRank_top_le_of_not_dvd_index hp H hH
    _ = CFSG.Open.pRank p (⊤ : Subgroup H) := pRank_eq_pRank_top_subgroup H
    _ = CFSG.Open.pRank p (⊤ : Subgroup G') :=
        (pRank_top_eq_of_mulEquiv hp.one_lt e).symm

end CFSG.SectionRank
