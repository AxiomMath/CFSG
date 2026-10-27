module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoPairsDerived
import CFSG.LocalAnalysis.StandardType.SpSixOvergroupInput
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem threeFourTwoAt_spSixTwo {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}
    (hq2 : q.p = 2) (hq1 : q.exponent = 1) (hd : d.1 = .B 3 q) :
    ThreeFourTwoAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  classical
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B 3 q := hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2 le_rfl
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group)
  have hs : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 3 q.p q.exponent hm
  haveI := hs
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := by
    rw [hq2, hq1] at hF
    haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
    exact Finite.of_equiv _ eF.symm.toEquiv
  have h9 : 3 ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := by
    rw [CFSG.AGLEmbedding.card_catGroup_B_even le_rfl hq2 rfl, hq1]
    decide
  have hO := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd (r := 3)
    (K := F) q.prime_p q.exponent_pos hF (by norm_num)).2 le_rfl
  rw [hq2, hq1] at hO
  have h1 : Nat.card (Outer (StatedProj (StatedSp 3 F))) = 1 := Nat.dvd_one.1 (by simpa using hO)
  haveI : Subsingleton (Outer (StatedProj (StatedSp 3 F))) := (Nat.card_eq_one_iff_unique.1 h1).1
  refine threeFourTwoAt_of_forall hs
    (CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_three h9)
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eF.symm) ?_
  intro Y _ _ K Y₀ E R hp _ hK ⟨e⟩ _ _ _ _ _ _ _ hRY hKY J hJ hJ1 hJp hJs _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hK
  have hX : Y₀.subgroupOf K ≠ ⊤ := fun h => hKY (Subgroup.subgroupOf_eq_top.1 h)
  have h3 := threeFourTwo_not_dvd_index (K := K) R hRY
  rcases CFSG.StandardType.ggSeitzExcSpSixOvergroupInput_holds K ⟨.B 3 q, hv⟩ q hq2 hq1 rfl ⟨e⟩
      (Y₀.subgroupOf K) hX h3 with hsol | ⟨hsimp, hlie⟩
  · exact (threeFourTwo_false_of_solvable hsol hJ hJp hJ1).elim
  · obtain ⟨eJ⟩ := threeFourTwo_equiv_commutator hsimp hJ hJs hJp hJ1
    have hlie' : CFSG.Blueprint.LieModel (commutator (Y₀.subgroupOf K)) .PSU 4 q.p q.exponent := by
      rw [hq2, hq1]
      exact hlie
    obtain ⟨i, hi, ⟨eU⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.H81Orth.catalogIs_twistedA3_of_lieModel q hlie'
    rcases i with ⟨_, _⟩ | ⟨_, _⟩ | dJ | _
    · exact hi.elim
    · exact hi.elim
    · refine ⟨.lie ⟨.B 3 q, hv⟩, .lie dJ, ?_, ⟨e⟩, (eJ.trans eU).toMonoidHom,
        (eJ.trans eU).surjective⟩
      exact Or.inl ⟨rfl, q, hq2, hq1, ⟨.B 3 q, hv⟩, dJ, rfl, hi, rfl, rfl⟩
    · exact hi.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

end
