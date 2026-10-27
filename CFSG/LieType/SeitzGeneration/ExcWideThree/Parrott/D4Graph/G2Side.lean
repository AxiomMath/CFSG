module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.RankThree.Chevalley


variable {K : Type} [Field K]

theorem g2_exists_conj_of_mem_rootQ {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β)
    {y : adjointGroup Tag.G2 K}
    (hy : (y : ModGL Tag.G2 K) ∈ rootSubgroup Tag.G2 K β ⊔ rootSubgroup Tag.G2 K (-β)) :
    ∃ (g : adjointGroup Tag.G2 K) (j : Fin Tag.G2.rank) (A : SL2 K),
      ((g * y * g⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
        simpleRootSL2 Tag.G2 K j A := by
  rw [← range_rootSL2_of_isRoot hβ] at hy
  obtain ⟨A, hA⟩ := hy
  rw [rootSL2_apply] at hA
  set W : adjointGroup Tag.G2 K := ⟨pinnedWeyl Tag.G2 K β, pinnedWeyl_mem_adjointGroup β⟩
  refine ⟨W⁻¹, (pinnedData Tag.G2 β).1, A, ?_⟩
  show (pinnedWeyl Tag.G2 K β)⁻¹ * (y : ModGL Tag.G2 K) * (pinnedWeyl Tag.G2 K β)⁻¹⁻¹ = _
  rw [← hA]
  group

theorem g2_exists_conj_simpleRootSL2 [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup Tag.G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (g : adjointGroup Tag.G2 K) (j : Fin Tag.G2.rank) (A : SL2 K),
      ((g * z * g⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
        simpleRootSL2 Tag.G2 K j A := by
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 z
    hz3 hz1
  rcases hg with hS | hL
  · obtain ⟨g', j, A, h⟩ := g2_exists_conj_of_mem_rootQ (y := g * z * g⁻¹) isRoot_g2δ
      (Subgroup.mem_comap.1 hS)
    refine ⟨g' * g, j, A, ?_⟩
    have e : g' * g * z * (g' * g)⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹ := by group
    rw [e]
    exact h
  · obtain ⟨g', j, A, h⟩ := g2_exists_conj_of_mem_rootQ (y := g * z * g⁻¹)
      (isRoot_single Tag.G2 g2l) (Subgroup.mem_comap.1 hL)
    refine ⟨g' * g, j, A, ?_⟩
    have e : g' * g * z * (g' * g)⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹ := by group
    rw [e]
    exact h

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
