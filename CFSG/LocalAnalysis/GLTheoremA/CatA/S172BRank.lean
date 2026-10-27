module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankTorus
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC (rot rot_apply_of_perp PairPerp map_add_polar)

theorem liftableRank_orthDerived {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hn : 3 ≤ n) (hodd : Odd n) :
    CFSG.LocalAnalysis.GLTheoremA.S172X.LiftableRank 3 ↥(CFSG.RankThree.Classical2.orthDerived Q)
      (n - 1) := by
  unfold CFSG.LocalAnalysis.GLTheoremA.S172X.LiftableRank
  have h5 : 5 ≤ finrank (ZMod 2) V := by omega
  refine ⟨fun E hE => card_le_three_pow_pred_orthDerived hQ hdim hplus hodd E hE, ?_⟩
  obtain ⟨a, b, e, f, hpair, hperp, he, hf, hef, horth⟩ :=
    exists_minusPairFamily hQ hdim hplus hodd
  have hc : Q (e + f) = 1 := by
    rw [map_add_polar, he, hf, hef]
    decide
  have hca : ∀ i, polar Q (a i) (e + f) = 0 := fun i => by
    rw [polar_add_right, polar_comm Q (a i) e, polar_comm Q (a i) f, (horth i).1, (horth i).2.2.1,
      add_zero]
  have hcb : ∀ i, polar Q (b i) (e + f) = 0 := fun i => by
    rw [polar_add_right, polar_comm Q (b i) e, polar_comm Q (b i) f, (horth i).2.1, (horth i).2.2.2,
      add_zero]
  have hca' : ∀ i, polar Q (e + f) (a i) = 0 := fun i => by rw [polar_comm]; exact hca i
  have hcb' : ∀ i, polar Q (e + f) (b i) = 0 := fun i => by rw [polar_comm]; exact hcb i
  have hn1 : 0 < n - 1 := by omega
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_card_closure_rotOrthDerived hpair hperp
  refine ⟨fun i => rotOrthDerived Q (hpair i),
    fun i => ⟨reflect Q (a i) * reflect Q (e + f),
      CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator hQ h5 (hpair i).qa hc⟩,
    (rootGroup Q e).subgroupOf (orthDerived Q), hEel, hEcard, fun i => ⟨?_, ?_⟩, ?_,
    isPGroup_two_subgroupOf_rootGroup e, ?_, ?_⟩
  · apply Subtype.ext
    exact sq_reflect_mul_reflect (hca i)
  · apply Subtype.ext
    exact reflect_mul_reflect_conj_rot (hca i) (hcb i)
  · intro i j hij
    apply Subtype.ext
    obtain ⟨h1, h2, -, -⟩ := hperp i j hij
    exact (commute_reflect_mul_reflect_rot h1 h2 (hca' j) (hcb' j)).eq
  · exact subgroupOf_rootGroup_ne_bot hQ h5 he (hpair ⟨0, hn1⟩).qa (horth ⟨0, hn1⟩).1
      (by rw [polar_comm]; exact hef) (horth ⟨0, hn1⟩).2.2.1
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact mem_normalizer_subgroupOf_rootGroup (rot_apply_of_perp (hpair i) (horth i).1 (horth i).2.1)

end CFSG.LocalAnalysis.GLTheoremA.S172B

end
