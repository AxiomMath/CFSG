module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem

section Roots

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem rootGroup_le_sup_rankOne_of_orth
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i j : Fin D.rank} (hcij : D.cartan i j = 0) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hpos : 0 < ht γ) (hsupp : ∀ k, k ≠ i → k ≠ j → γ k = 0) :
    D.rootGroup γ ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible with hΦ
  have hij : i ≠ j := fun h => by
    rw [h, D.isFiniteType.apply_self] at hcij
    omega
  have hγΦ : γ ∈ Φ.roots := hγ
  have hnn : ∀ k, 0 ≤ γ k := by
    rcases Φ.sign γ hγΦ with h | h
    · exact h
    · exfalso
      have : ht γ ≤ 0 := Finset.sum_nonpos fun k _ => h k
      omega
  have hri : Φ.refl i γ ∈ Φ.roots := Φ.refl_mem i γ hγΦ
  have hreflj : Φ.refl i γ j = γ j := Φ.refl_apply_of_ne i γ j (Ne.symm hij)
  have hrefli : Φ.refl i γ i = -γ i := by
    rw [RootSystem.ofCartan_refl_apply, reflection_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    have hsum : ∑ k, D.cartan i k * γ k = 2 * γ i + D.cartan i j * γ j := by
      rw [Finset.sum_eq_add i j hij]
      · rw [D.isFiniteType.apply_self]
      · intro k _ ⟨h1, h2⟩
        rw [hsupp k h1 h2, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum, hcij]
    ring
  have hzero : γ i = 0 ∨ γ j = 0 := by
    rcases Φ.sign _ hri with h | h
    · left
      have := h i
      rw [hrefli] at this
      have := hnn i
      omega
    · right
      have := h j
      rw [hreflj] at this
      have := hnn j
      omega
  rcases hzero with h | h
  · refine (hct.le_rankOne j γ hγ fun k hk => ?_).trans le_sup_right
    by_cases hki : k = i
    · rw [hki]; exact h
    · exact hsupp k hki hk
  · refine (hct.le_rankOne i γ hγ fun k hk => ?_).trans le_sup_left
    by_cases hkj : k = j
    · rw [hkj]; exact h
    · exact hsupp k hk hkj

end Roots

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
