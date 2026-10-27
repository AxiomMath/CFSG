module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8SpDesc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

theorem sp_rank_bound {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (A : Subgroup (MulAut (StatedProj (StatedSp n K)))) (hA : IsElemAbelian 3 A)
    (h4 : CFSG.Open.pRank 3 A ≤ 4)
    (hout : ∀ a ∈ A, a ∉ (MulAut.conj : StatedProj (StatedSp n K) →*
        MulAut (StatedProj (StatedSp n K))).range →
      ∀ E : Subgroup (StatedProj (StatedSp n K)), E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A)
    (hnot : ¬ A ≤ innAutDerived (StatedProj (StatedSp n K))) : n ≤ 3 := by
  classical
  haveI hchar : CharP K 2 := charP_two_of_card_eight hK
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨ι, hιinj, hιfix, -⟩ := exists_descent_sp hn hK b (hA.2 b hbA)
    (fun h => hbout (inner_le_innAutDerived _ h))
  obtain ⟨stdIso⟩ := exists_stdIso n
  obtain ⟨E0S, -, hE0S, hE0Scard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    (H := (⊤ : Subgroup (StatedSp n (ZMod 2)))) (k := n) Nat.prime_three
    (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp (K := ZMod 2) (n := n)
      (r := 3) Nat.prime_three (by rw [Nat.card_zmod]; norm_num))
  let E0 : Subgroup ↥(TauCeti.BilinForm.isometryGroup (stdForm n)) := E0S.map stdIso.toMonoidHom
  have hE0ab : IsElemAbelian 3 (E0.map ι) :=
    isElemAbelian_map_gen ι (isElemAbelian_map_gen _ hE0S)
  have hc : Nat.card (E0.map ι) = 3 ^ n := by
    rw [Subgroup.card_map_of_injective hιinj, Subgroup.card_map_of_injective stdIso.injective,
      hE0Scard]
  have hbnotinn : b ∉ (MulAut.conj : StatedProj (StatedSp n K) →*
      MulAut (StatedProj (StatedSp n K))).range := fun h => hbout (inner_le_innAutDerived _ h)
  have h1 := hout b hbA hbnotinn (E0.map ι) (by
    rintro _ ⟨v, -, rfl⟩
    exact mem_fixSubgroup.2 (hιfix v)) hE0ab
  rw [pRank_eq_of_card' Nat.prime_three hE0ab hc] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

end
