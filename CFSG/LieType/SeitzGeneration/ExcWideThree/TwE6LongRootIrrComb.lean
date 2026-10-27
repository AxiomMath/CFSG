module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootOps

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace CoreIrr

abbrev Wt : Type := Fin TwistTag.E6.tag.rank → ℤ

@[expose] def ht (γ : Dr) : ℤ := ∑ i, γ.1 i

@[expose] def topV : Wt := ![1, 1, 2, 3, 2, 1]

theorem topV_mem : topV ∈ degOneRoots := by decide +kernel

@[expose] def topD : Dr := ⟨topV, topV_mem⟩

theorem ht_facts : ∀ γ : Dr, 0 < ht γ ∧ ht γ ≤ 10 ∧ (γ ≠ topD → ht γ < 10) := by decide +kernel

theorem ht_pos (γ : Dr) : 0 < ht γ := (ht_facts γ).1

theorem ht_le (γ : Dr) : ht γ ≤ 10 := (ht_facts γ).2.1

theorem ht_lt {γ : Dr} (h : γ ≠ topD) : ht γ < 10 := (ht_facts γ).2.2 h

theorem ht_top : ht topD = 10 := by decide +kernel

theorem exists_up : ∀ γ : Dr, γ ≠ topD →
    γ.1 + (Pi.single 0 1 : Wt) ∈ degOneRoots ∨ γ.1 + (Pi.single 2 1 : Wt) ∈ degOneRoots ∨
    γ.1 + (Pi.single 3 1 : Wt) ∈ degOneRoots ∨ γ.1 + (Pi.single 4 1 : Wt) ∈ degOneRoots ∨
    γ.1 + (Pi.single 5 1 : Wt) ∈ degOneRoots := by decide +kernel

theorem rho_top : rhoD topD = topD := by decide +kernel

theorem rho_rho : ∀ γ : Dr, rhoD (rhoD γ) = γ := by decide +kernel

theorem refl_facts : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ γ : Dr,
    reflD a (reflD a γ) = γ ∧ rhoD (reflD a γ) = reflD a (rhoD γ) := by decide +kernel

theorem refl_invol (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ 3) (γ : Dr) :
    reflD a (reflD a γ) = γ := (refl_facts a ha γ).1

theorem refl_rho (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ 3) (γ : Dr) :
    rhoD (reflD a γ) = reflD a (rhoD γ) := (refl_facts a ha γ).2

@[expose] def applyWord : List (Fin TwistTag.E6.foldedTag.rank) → Dr → Dr
  | [], x => x
  | a :: w, x => applyWord w (reflD a x)

@[expose] def fixedWords : List (List (Fin TwistTag.E6.foldedTag.rank)) :=
  [[], [2], [2, 1], [2, 1, 0], [2, 1, 2], [2, 1, 0, 2], [2, 1, 0, 2, 1], [2, 1, 0, 2, 1, 2]]

theorem fixedWords_ne : ∀ w ∈ fixedWords, ∀ a ∈ w, a ≠ 3 := by decide +kernel

theorem fixed_reach : ∀ γ : Dr, rhoD γ = γ → ∃ w ∈ fixedWords, applyWord w topD = γ := by
  decide +kernel

@[expose] def pairData : List (Fin TwistTag.E6.foldedTag.rank × Fin TwistTag.E6.tag.rank ×
    Fin TwistTag.E6.tag.rank) := [(0, 0, 5), (1, 2, 4)]

@[expose] def seeds : Finset Dr := Finset.univ.filter fun δ =>
  ∃ γ : Dr, rhoD γ = γ ∧ ∃ p ∈ pairData,
    δ.1 + (Pi.single p.2.1 1 : Wt) = γ.1 ∧ (rhoD δ).1 + (Pi.single p.2.2 1 : Wt) = γ.1 ∧
      rhoD δ ≠ δ ∧ ∃ γ'' : Dr, rhoD γ'' = γ'' ∧
        γ''.1 + (Pi.single p.2.1 1 : Wt) = (rhoD δ).1

theorem seeds_spec {δ : Dr} (h : δ ∈ seeds) :
    ∃ γ : Dr, rhoD γ = γ ∧ ∃ p ∈ pairData,
      δ.1 + (Pi.single p.2.1 1 : Wt) = γ.1 ∧ (rhoD δ).1 + (Pi.single p.2.2 1 : Wt) = γ.1 ∧
        rhoD δ ≠ δ ∧ ∃ γ'' : Dr, rhoD γ'' = γ'' ∧
          γ''.1 + (Pi.single p.2.1 1 : Wt) = (rhoD δ).1 :=
  (Finset.mem_filter.1 h).2

@[expose] def fixedSet : Finset Dr := Finset.univ.filter fun γ => rhoD γ = γ

@[expose] def covered : Finset Dr := fixedSet ∪ seeds ∪ seeds.image rhoD

theorem all_reach : ∀ γ : Dr, γ ∈ covered ∨ reflD 0 γ ∈ covered ∨ reflD 1 γ ∈ covered ∨
    reflD 2 γ ∈ covered := by decide +kernel

end CoreIrr

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
