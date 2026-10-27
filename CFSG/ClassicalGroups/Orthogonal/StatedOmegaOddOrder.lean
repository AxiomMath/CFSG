module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.LieType.Universal.Spin

private theorem toLinEquiv_mem_orthogonalGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    {g : GL ι K} (hg : ∀ v, Q₀ (Matrix.mulVec (g : Matrix ι ι K) v) = Q₀ v) :
    toLinEquiv ι K g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [toLinEquiv_apply, hQ]
  exact hg v

private theorem mem_statedOmega_of_toLinEquiv_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    {g : GL ι K} (hg : toLinEquiv ι K g ∈ CFSG.RankThree.Classical2.orthDerived Q) :
    g ∈ StatedOmega Q₀ := by
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
  exact hg

theorem sq_mem_statedOmega_quadOdd {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (g : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K)
    (hg : ∀ v, StatedQuadOdd 3 K (Matrix.mulVec (g : Matrix _ _ K) v) = StatedQuadOdd 3 K v) :
    g ^ 2 ∈ StatedOmega (StatedQuadOdd 3 K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hQnd, hT⟩ := regular_quadOdd (K := K) (n := 3) h2 (by norm_num)
  obtain ⟨-, -, -, -, -, hsq, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  refine mem_statedOmega_of_toLinEquiv_mem (coe_quadOdd 3 K) ?_
  rw [map_pow]
  exact hsq (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) K g)
    (toLinEquiv_mem_orthogonalGroup (coe_quadOdd 3 K) hg)

theorem mem_statedOmega_quadOdd_of_odd {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (g : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K)
    (hg : ∀ v, StatedQuadOdd 3 K (Matrix.mulVec (g : Matrix _ _ K) v) = StatedQuadOdd 3 K v)
    (hodd : Odd (orderOf g)) : g ∈ StatedOmega (StatedQuadOdd 3 K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hQnd, hT⟩ := regular_quadOdd (K := K) (n := 3) h2 (by norm_num)
  obtain ⟨-, -, -, -, -, -, hoddmem, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  refine mem_statedOmega_of_toLinEquiv_mem (coe_quadOdd 3 K) ?_
  refine hoddmem (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) K g)
    (toLinEquiv_mem_orthogonalGroup (coe_quadOdd 3 K) hg) ?_
  have horder : orderOf ((toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) K) g) = orderOf g :=
    orderOf_injective (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) K).toMonoidHom
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) K).injective g
  rw [horder]
  exact hodd

theorem sq_mem_statedOmega_quadMinus {K : Type} [Field K] [Finite K] (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K)
    (hg : ∀ v, StatedQuadMinus 4 K b c (Matrix.mulVec (g : Matrix _ _ K) v) =
      StatedQuadMinus 4 K b c v) :
    g ^ 2 ∈ StatedOmega (StatedQuadMinus 4 K b c) := by
  obtain ⟨hQnd, hT⟩ := regular_quadMinus (K := K) (n := 4) (b := b) (c := c) (by norm_num) hbc
  obtain ⟨-, -, -, -, -, hsq, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  refine mem_statedOmega_of_toLinEquiv_mem (coe_quadMinus 4 K b c) ?_
  rw [map_pow]
  exact hsq (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K g)
    (toLinEquiv_mem_orthogonalGroup (coe_quadMinus 4 K b c) hg)

theorem mem_statedOmega_quadMinus_of_odd {K : Type} [Field K] [Finite K] (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K)
    (hg : ∀ v, StatedQuadMinus 4 K b c (Matrix.mulVec (g : Matrix _ _ K) v) =
      StatedQuadMinus 4 K b c v)
    (hodd : Odd (orderOf g)) : g ∈ StatedOmega (StatedQuadMinus 4 K b c) := by
  obtain ⟨hQnd, hT⟩ := regular_quadMinus (K := K) (n := 4) (b := b) (c := c) (by norm_num) hbc
  obtain ⟨-, -, -, -, -, -, hoddmem, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  refine mem_statedOmega_of_toLinEquiv_mem (coe_quadMinus 4 K b c) ?_
  refine hoddmem (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K g)
    (toLinEquiv_mem_orthogonalGroup (coe_quadMinus 4 K b c) hg) ?_
  have horder : orderOf ((toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) g) = orderOf g :=
    orderOf_injective (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).toMonoidHom
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).injective g
  rw [horder]
  exact hodd

end CFSG.ClassicalGroups.Orthogonal
