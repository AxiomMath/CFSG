module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLiftY

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.GLTheoremA.S267.Gen
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


namespace CFSG.LocalAnalysis.GLTheoremA.F151

theorem compNormal_reeF4_of_three_lt
    {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    CompNormal (MulAut.conj x) := by
  obtain ⟨N, -, -, hall, -⟩ :=
    CFSG.RankThree.PartOne.TCF.largeRee_component_data ha hK hp hp3 x hx
  have hC := CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj x
  have toR : ∀ D : Subgroup (ReeTag.F4.reeGamma K a),
      CFSG.Open.IsComponentOf D (fixSubgroup (MulAut.conj x)) → D = N := by
    intro D hD
    rw [hC] at hD
    exact hall D ⟨hD.1, CFSG.HardMathSupport.Solomon.Coordinator.i183v_isQuasisimple hD.2.2,
      (CFSG.Open.IsSubnormal.iff_subgroupOf hD.1).1 hD.2.1⟩
  intro J hJ g hg
  have hJN := toR J hJ
  have hJg : CFSG.Open.IsComponentOf (J.map (MulAut.conj g).toMonoidHom)
      (fixSubgroup (MulAut.conj x)) := by
    have h := CFSG.StandardType.ggIsComponentOf_conj
      ((CFSG.Assembly.isComponentOf_iff_open).2 hJ) hg
    exact (CFSG.Assembly.isComponentOf_iff_open).1 h
  have hgN := toR _ hJg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hgN.trans hJN.symm

theorem compNormal_reeF4_three {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = 3) : CompNormal (MulAut.conj x) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    a K hK x hx
  have hK' : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hK' (by omega)).1
  have hC := CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj x
  have hqC : CFSG.Open.IsQuasisimple ↥(fixSubgroup (MulAut.conj x)) := by
    rw [hC]
    exact CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq)
  intro J hJ g hg
  have hsub := CFSG.StandardType.ggRCS_isComponentOf_subgroupOf hJ hJ.1 le_rfl
  have htop :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313.eq_top_of_isComponentOf_quasisimple
      hqC hsub
  have hJC : J = fixSubgroup (MulAut.conj x) :=
    le_antisymm hJ.1 (Subgroup.subgroupOf_eq_top.1 htop)
  rw [hJC]
  exact Subgroup.le_normalizer hg

end CFSG.LocalAnalysis.GLTheoremA.F151

end
