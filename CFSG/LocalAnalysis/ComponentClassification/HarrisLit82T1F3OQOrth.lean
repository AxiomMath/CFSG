module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outNoA4_of_orthogonalGates {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hg : OrthogonalGates Q f) (htop : matrixProjectiveImage Q = ⊤) (hf3 : ¬ 3 ∣ f) :
    OutNoA4 (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, k, hk⟩, -⟩ := hg
  have hcard : Nat.card (K ≃+* K) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  refine outNoA4_of_three (D := (linearConjugationHom Q).range) (fun x => ⟨f, hf3, ?_⟩)
    fun y hy => ⟨k, ?_⟩
  · have hx : x ∈ matrixProjectiveImage Q := htop ▸ Subgroup.mem_top x
    have h1 : ψ ⟨x, hx⟩ ^ f = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have h2 : (⟨x, hx⟩ : matrixProjectiveImage Q) ^ f ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, h1]
    rw [hψker, mem_subgroupOf] at h2
    simpa using h2
  · have hc : Nat.card ((linearConjugationHom Q).range ⧸
        (inner (matrixProjectiveDerived Q)).subgroupOf (linearConjugationHom Q).range) = 2 ^ k :=
      hk
    have h1 : (QuotientGroup.mk ⟨y, hy⟩ : (linearConjugationHom Q).range ⧸
        (inner (matrixProjectiveDerived Q)).subgroupOf (linearConjugationHom Q).range) ^ 2 ^ k =
          1 := by
      rw [← hc]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1

theorem outNoA4_of_statedClassicalModel_orth {S : Type} [Group S] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hp2 : p ≠ 2)
    (hn : ¬(t = .POmegaPlus ∧ n = 4)) (hf3 : ¬ 3 ∣ f) (h : StatedClassicalModel S t n p f) :
    OutNoA4 S := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S t ht n p f h
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hp, hf, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn3
      hchar
    exact OutNoA4.of_mulEquiv (coordinateOddWitnessEquiv K e).symm
      (outNoA4_of_orthogonalGates hp hK (hg K hK e) htop hf3)
  · obtain ⟨⟨hp, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have hn5 : 5 ≤ n := by
      by_contra hlt
      exact hn ⟨rfl, by omega⟩
    have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5
    exact OutNoA4.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
      (outNoA4_of_orthogonalGates hp hK (hg K hK e) htop hf3)
  · obtain ⟨⟨hp, -, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    have hn1 : 1 ≤ n := by omega
    have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n
      hn4 b c hirr
    exact OutNoA4.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
      (outNoA4_of_orthogonalGates hp hK (hg hn1 K hK b c hirr e) htop hf3)

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
