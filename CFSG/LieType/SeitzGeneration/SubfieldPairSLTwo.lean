module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLCore
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem subfieldPairSL_two {K : Type} [Field K] [Finite K]
    [CharP K 2] (k : Subfield K) {p : ℕ} (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p)
    {n : ℕ} (hn3 : 3 ≤ n) (hnp : n < p) (A : GL (Fin n) K)
    (hne : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k) :
    Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
      ((slSub n k).map (slConjugation n K A).toMonoidHom :
        Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  set G₀ := slSub n k with hG₀
  set G₁ := G₀.map (slConjugation n K A).toMonoidHom with hG₁
  set H := Subgroup.closure ((G₀ : Set (SpecialLinearGroup (Fin n) K)) ∪
    (G₁ : Set (SpecialLinearGroup (Fin n) K))) with hH
  have hk : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hk1 : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  by_contra hHtop
  have NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij a ∉ H :=
    fun a ha i j hij hmem => hHtop (eq_top_of_root_not_mem hk hn3 hp hK ha hij hmem)
  have hd2 : p ≠ 2 := by omega
  have hall : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), tv v φ h ∈ H → v ≠ 0 → tv v φ h ∈ G₀ := by
    intro v φ h hmem hv0
    by_cases hφ0 : φ = 0
    · subst hφ0
      have h1 : tv v 0 h = 1 := Subtype.ext (by simp [tv_coe])
      rw [h1]
      exact G₀.one_mem
    · rcases tv_mem_slSub_or_generic hk hn3 NIR h hmem hv0 with hrat | hgen
      · exact hrat
      · obtain ⟨a, ha, i, j, hij, hmem'⟩ :=
          exists_root_of_generic hp hd2 hnp hn3 hK hk h hmem hφ0 hgen
        exact absurd hmem' (NIR a ha i j hij)
  have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k →
      slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ G₀ := by
    intro i j hij c hc
    have h1 : slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ H :=
      hk1 (Subgroup.mem_map_of_mem _ (transvection_mem_slSub hij hc))
    have hne0 : (A : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) ≠ 0 := by
      intro h0
      have h2 := congrArg (fun w => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) h0
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      simpa using congrFun h2 i
    rw [transvection_eq_tv hij c, slConjugation_tv] at h1 ⊢
    exact hall _ _ _ h1 hne0
  exact hne (map_conj_slSub_eq A hroot)

end CFSG.LieType.SeitzGeneration
