module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsOrthInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsOrthOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open

theorem compNormal_of_statedOmega {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ2 : ℓ ≠ 2) (hpℓ : p ≠ ℓ)
    (hD4 : t = .POmegaPlus → n = 4 → p = 3 → ∀ β : MulAut G, β ^ p = 1 →
      (∀ a : G, MulAut.conj a ≠ β) → CompNormal β)
    (β : MulAut G) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : CompNormal β := by
  by_cases hin : ∃ a : G, MulAut.conj a = β
  · obtain ⟨a, rfl⟩ := hin
    exact compNormal_conj_omega hp hp2 ht hG hℓ2 hpℓ a hβ fun h => hβ1 (by rw [h, map_one])
  · have hout : ∀ a : G, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    by_cases hd : t = .POmegaPlus ∧ n = 4 ∧ p = 3
    · exact hD4 hd.1 hd.2.1 hd.2.2 β hβ hout
    · exact compNormal_omega_outer hp hp2 ht hG (fun h1 h2 h3 => hd ⟨h1, h2, h3⟩) β hβ hout

theorem genNormalAllOn_orth (hD4 : D4OuterCompNormal) : GenNormalAllOn S267OrthIdx := by
  intro p T _ _ d hd hQ x hx hx1
  obtain ⟨e⟩ := hd.iso
  obtain ⟨d1, hv⟩ := d
  have hchar : d1.characteristic ≠ 2 := hd.charOdd
  have hpq : p ≠ d1.characteristic := hd.ne
  cases d1 with
  | B r q =>
    exact compNormal_of_statedOmega hd.prime hd.odd (Or.inl rfl)
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
        (by simpa using hchar) hQ e)
      (by simpa using hchar) (by simpa using hpq) (fun h => by cases h) x hx hx1
  | D r q =>
    refine compNormal_of_statedOmega hd.prime hd.odd (Or.inr (Or.inl rfl))
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
      (by simpa using hchar) (by simpa using hpq) (fun _ h4 h3 β hβ hout => ?_) x hx hx1
    subst h4 h3
    exact hD4 T ⟨_, hv⟩ hd ⟨q, rfl⟩ β hβ hout
  | twistedD r q =>
    exact compNormal_of_statedOmega hd.prime hd.odd (Or.inr (Or.inr rfl))
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
      (by simpa using hchar) (by simpa using hpq) (fun h => by cases h) x hx hx1
  | _ => exact absurd hQ (by simp [S267OrthIdx])

section Plane


theorem genPlaneCompOn_orth_of_seitz (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hD4 : D4OuterCompNormal) : GenPlaneCompOn S267OrthIdx :=
  genPlaneCompOn_of_normalAll hS (genNormalAllOn_orth hD4)

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
