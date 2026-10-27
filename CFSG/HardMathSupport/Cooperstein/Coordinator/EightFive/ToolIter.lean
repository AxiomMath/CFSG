module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm

theorem natShape_of_stab_iter {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) : ∀ (k n : ℕ), m + 1 + k = n → ∀ (ι : Fin m ↪ Fin n)
      (ρ : alternatingGroup (Fin n) →* MulAut V),
      NatShape (ρ.comp (altLift ι)) (alternatingGroup (Fin m)).subtype →
      NatShape ρ (alternatingGroup (Fin n)).subtype := by
  intro k
  induction k with
  | zero =>
    intro n hn ι ρ h
    exact natShape_of_stab hV (by omega) ι (by omega) ρ h
  | succ k ih =>
    intro n hn ι ρ h
    obtain rfl : n = m + 1 + k + 1 := by omega
    obtain ⟨ω, hω⟩ := exists_notMem_of_card_lt (Finset.univ.map ι) (by simp; omega)
    let ι₂ : Fin (m + 1 + k) ↪ Fin (m + 1 + k + 1) := Fin.succAboveEmb ω
    obtain ⟨ι₁, hι₁⟩ := exists_embedding_factor ι ι₂ fun i => by
      change ι i ∈ Set.range ω.succAbove
      rw [Fin.range_succAbove]
      intro h
      exact hω ((Set.mem_singleton_iff.1 h) ▸ Finset.mem_map_of_mem ι (Finset.mem_univ i))
    refine natShape_of_stab hV (by omega) ι₂ rfl ρ (ih _ rfl ι₁ (ρ.comp (altLift ι₂)) ?_)
    rw [MonoidHom.comp_assoc, ← altLift_trans, hι₁]
    exact h

theorem natShape_of_stab_lt {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) {m n : ℕ}
    (hm : 7 ≤ m) (hmn : m < n) (ι : Fin m ↪ Fin n) (ρ : alternatingGroup (Fin n) →* MulAut V)
    (h : NatShape (ρ.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) :
    NatShape ρ (alternatingGroup (Fin n)).subtype :=
  natShape_of_stab_iter hV hm (n - m - 1) n (by omega) ι ρ h

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
