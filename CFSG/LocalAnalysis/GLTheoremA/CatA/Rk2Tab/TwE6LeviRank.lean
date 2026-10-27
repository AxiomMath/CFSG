module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwoLocalLeviTwisted
public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def twE6MaxA5 : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a.val ≠ 3}

@[expose] def twE6MaxA2A1 : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a.val ≠ 2}

@[expose] def twE6MaxA1A2 : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a.val ≠ 1}

@[expose] def twE6MaxD4 : Set (Fin TwistTag.E6.foldedTag.rank) := {a | a.val ≠ 0}

theorem subset_maximalSet_of_ne_univ {J : Set (Fin TwistTag.E6.foldedTag.rank)}
    (hJ : J ≠ Set.univ) :
    J ⊆ twE6MaxA5 ∨ J ⊆ twE6MaxA2A1 ∨ J ⊆ twE6MaxA1A2 ∨ J ⊆ twE6MaxD4 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.E6.foldedTag.rank, a ∉ J := by
    by_contra h
    exact hJ (Set.eq_univ_of_forall fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  have hcases : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 := by
    have hlt : a.val < 4 := a.isLt
    omega
  rcases hcases with h | h | h | h
  · right; right; right
    intro x hx hx0
    exact ha (Fin.ext (hx0.trans h.symm) ▸ hx)
  · right; right; left
    intro x hx hx1
    exact ha (Fin.ext (hx1.trans h.symm) ▸ hx)
  · right; left
    intro x hx hx2
    exact ha (Fin.ext (hx2.trans h.symm) ▸ hx)
  · left
    intro x hx hx3
    exact ha (Fin.ext (hx3.trans h.symm) ▸ hx)

theorem orbitUnion_mono {t : TwistTag} {J J' : Set (Fin t.foldedTag.rank)} (h : J ⊆ J') :
    t.orbitUnion J ⊆ t.orbitUnion J' := by
  intro i hi
  obtain ⟨a, ha, hia⟩ := (TwistTag.mem_orbitUnion (t := t)).1 hi
  exact (TwistTag.mem_orbitUnion (t := t)).2 ⟨a, h ha, hia⟩

theorem graphFixedParabolicLevi_mono
    {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    {J J' : Set (Fin t.foldedTag.rank)} (h : J ⊆ J') :
    graphFixedParabolicLevi t K σ J ≤ graphFixedParabolicLevi t K σ J' :=
  inf_le_inf_right _ (CFSG.RankThree.PartTwo.Census.Carrier.D4Even.parabolicLevi_mono
    (τ := t.tag) (K := K) (orbitUnion_mono h))

@[expose] def Rk2TwE6LeviRankInputMaximal :
    Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = (2 ^ n) ^ 2 →
    ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ (2 ^ n)) →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
        (∀ E : Subgroup (ModGL TwistTag.E6.tag F),
          E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 →
            IsElemAbelian p E → Nat.card E ≤ p ^ 5) ∧
        (∀ E : Subgroup (ModGL TwistTag.E6.tag F),
          E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 →
            IsElemAbelian p E → Nat.card E ≤ p ^ 5) ∧
        (∀ E : Subgroup (ModGL TwistTag.E6.tag F),
          E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 →
            IsElemAbelian p E → Nat.card E ≤ p ^ 5) ∧
        (∀ E : Subgroup (ModGL TwistTag.E6.tag F),
          E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 →
            IsElemAbelian p E → Nat.card E ≤ p ^ 5)

theorem rk2TwE6LeviRankInput_of_maximal
    (hM : Rk2TwE6LeviRankInputMaximal) :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ (2 ^ n)) →
        ∀ (p : ℕ), p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
          ∀ (J : Set (Fin TwistTag.E6.foldedTag.rank)), J ≠ Set.univ →
            ∀ E : Subgroup (ModGL TwistTag.E6.tag F),
              E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J →
                IsElemAbelian p E → Nat.card E ≤ p ^ 5 := by
  intro F _ _ n hF σ hσ p hp hp2 hq J hJ E hE hEel
  obtain ⟨h5, h2a, h1a, hd⟩ := hM F n hF σ hσ p hp hp2 hq
  rcases subset_maximalSet_of_ne_univ hJ with h | h | h | h
  · exact h5 E (hE.trans (graphFixedParabolicLevi_mono h)) hEel
  · exact h2a E (hE.trans (graphFixedParabolicLevi_mono h)) hEel
  · exact h1a E (hE.trans (graphFixedParabolicLevi_mono h)) hEel
  · exact hd E (hE.trans (graphFixedParabolicLevi_mono h)) hEel

end CFSG.LocalAnalysis.GLTheoremA
