module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeLayers
public import CFSG.HardMathSupport.Lang.Triality.TraceKernel
public import CFSG.HardMathSupport.Lang.Triality.Char3Sylow
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.RootConj
public import CFSG.LieType.Chevalley.GraphFixedBruhatDecomposition
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Steinberg.BruhatTwist
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.D4Comm
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private abbrev n0 : Fin TwistTag.D4.tag.rank := ⟨0, by decide⟩
private abbrev n1 : Fin TwistTag.D4.tag.rank := ⟨1, by decide⟩
private abbrev n2 : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩
private abbrev n3 : Fin TwistTag.D4.tag.rank := ⟨3, by decide⟩

private theorem commute_simple_of_cartan_zero {i j : Fin TwistTag.D4.tag.rank}
    (h : TwistTag.D4.tag.cartan i j = 0) :
    simple TwistTag.D4.tag i * simple TwistTag.D4.tag j =
      simple TwistTag.D4.tag j * simple TwistTag.D4.tag i :=
  CFSG.LieType.Steinberg.simple_mul_simple_comm (isFiniteType_cartan TwistTag.D4.tag) h

private abbrev wB : WeylGroup TwistTag.D4.tag :=
  simple TwistTag.D4.tag n2 * simple TwistTag.D4.tag n0 *
    simple TwistTag.D4.tag n1 * simple TwistTag.D4.tag n3

private theorem isRoot_B : IsRoot TwistTag.D4.tag rootB := by
  have e : rootB = Pi.single n2 (1 : ℤ) := by decide
  rw [e]
  exact IsRoot.basis _

private theorem isRoot_C : IsRoot TwistTag.D4.tag rootC := by
  have e : (simple TwistTag.D4.tag n0 * simple TwistTag.D4.tag n1 *
      simple TwistTag.D4.tag n3) • rootB = rootC := by
    simp only [mul_smul, simple_smul]
    decide
  rw [← e]
  exact IsRoot.smul isRoot_B _

private theorem smul_B_eq_D : wB • rootB = rootD := by
  simp only [wB, mul_smul, simple_smul]
  decide

private theorem smul_C_eq_D : simple TwistTag.D4.tag n2 • rootC = rootD := by
  simp only [simple_smul]
  decide

private theorem weylTwist_wB : weylTwist TwistTag.D4 wB = wB := by
  have p2 : TwistTag.D4.perm n2 = n2 := by decide
  have p0 : TwistTag.D4.perm n0 = n1 := by decide
  have p1 : TwistTag.D4.perm n1 = n3 := by decide
  have p3 : TwistTag.D4.perm n3 = n0 := by decide
  have c01 := commute_simple_of_cartan_zero (i := n0) (j := n1) (by decide)
  have c03 := commute_simple_of_cartan_zero (i := n0) (j := n3) (by decide)
  have key : simple TwistTag.D4.tag n1 * (simple TwistTag.D4.tag n3 *
      simple TwistTag.D4.tag n0) =
      simple TwistTag.D4.tag n0 * (simple TwistTag.D4.tag n1 *
        simple TwistTag.D4.tag n3) := by
    rw [← c03, ← mul_assoc, ← c01, mul_assoc]
  simp only [wB, map_mul, weylTwist_simple, p2, p0, p1, p3, mul_assoc]
  rw [key]

private theorem weylTwist_s2 :
    weylTwist TwistTag.D4 (simple TwistTag.D4.tag n2) = simple TwistTag.D4.tag n2 := by
  have p2 : TwistTag.D4.perm n2 = n2 := by decide
  simp only [weylTwist_simple, p2]

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem exists_graphFixed_canonicalRep {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTwist TwistTag.D4 w = w) :
    ∃ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (n : ModGL TwistTag.D4.tag K) = canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∧
        fieldActor (t := TwistTag.D4) σ σ n = n := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hpar : ringChar K = 2 ∨ ∃ m, Odd m ∧ ∀ c, σ c = c ^ m :=
    Or.inr ⟨3 ^ f, Odd.pow (by decide), hσ⟩
  have hmem : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    canonicalRep_mem_twistedFixedGroup TwistTag.D4 K σ.toRingHom hw
  rw [twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 hpar] at hmem
  refine ⟨⟨_, hmem⟩, rfl, Subtype.ext ?_⟩
  rw [coe_fieldActor]
  exact entrywise_canonicalRep σ w

theorem exists_weyl_rootB_to_rootD : ∃ (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (ε : K),
    fieldActor (t := TwistTag.D4) σ σ n = n ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ s : K, (n : ModGL TwistTag.D4.tag K) * pinnedX TwistTag.D4.tag K rootB s *
        (n : ModGL TwistTag.D4.tag K)⁻¹ = pinnedX TwistTag.D4.tag K rootD (ε * s) := by
  obtain ⟨n, hn, hfix⟩ := exists_graphFixed_canonicalRep hf hK σ hσ weylTwist_wB
  obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K wB isRoot_B
  refine ⟨n, ε, hfix, mul_self_eq_one_iff.mp hε, fun s => ?_⟩
  rw [hn]
  have h := hconj s
  rw [smul_B_eq_D] at h
  exact h

theorem exists_weyl_rootC_to_rootD : ∃ (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (ε : K),
    fieldActor (t := TwistTag.D4) σ σ n = n ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ r : K, (n : ModGL TwistTag.D4.tag K) * pinnedX TwistTag.D4.tag K rootC r *
        (n : ModGL TwistTag.D4.tag K)⁻¹ = pinnedX TwistTag.D4.tag K rootD (ε * r) := by
  obtain ⟨n, hn, hfix⟩ := exists_graphFixed_canonicalRep hf hK σ hσ weylTwist_s2
  obtain ⟨ε, hε, hconj⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv K (simple TwistTag.D4.tag n2) isRoot_C
  refine ⟨n, ε, hfix, mul_self_eq_one_iff.mp hε, fun r => ?_⟩
  rw [hn]
  have h := hconj r
  rw [smul_C_eq_D] at h
  exact h

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
