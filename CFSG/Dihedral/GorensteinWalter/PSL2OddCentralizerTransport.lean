module

public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer

public noncomputable section

namespace CFSG.GorensteinWalter

theorem odd_centralizer_normalizer_of_psl2_equiv
    {G : Type} [Group G] [Finite G]
    (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    {t : G} (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set G)) :
    Subgroup.normalizer (X : Set G) = Subgroup.centralizer ({t} : Set G) := by
  have hte : BenderSuzuki.PFAppendixIII.IsInvolution (e t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact ht.1 (e.injective (by simpa using h))
    · simpa using congrArg e ht.2
  let Y := X.map e.toMonoidHom
  have hYne : Y ≠ ⊥ := by
    intro h
    apply hXne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using h
  have hYodd : ∀ y : PSL2 K, y ∈ Y → Odd (orderOf y) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    change Odd (orderOf (e x))
    rw [e.orderOf_eq]
    exact hXodd.of_dvd_nat (X.orderOf_dvd_natCard hx)
  have hYcent : Y ≤ Subgroup.centralizer ({e t} : Set (PSL2 K)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp (hXcent hx))
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_equiv_normalizer_eq, CFSG.centralizer_singleton_map]
  exact psl2_odd_centralizer_normalizer hK hte Y hYne hYodd hYcent

end CFSG.GorensteinWalter
