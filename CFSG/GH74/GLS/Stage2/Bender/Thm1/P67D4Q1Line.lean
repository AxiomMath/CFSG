module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KGD.D4Frame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Base

theorem triEmb_mem_monomial {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L]
    [Algebra K L] {n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L n ∈ monomialSubgroup TwistTag.D4.tag L := by
  rw [triEmb_apply]
  exact baseChangeGL_mem_monomialSubgroup (algebraMap K L) (Subgroup.mem_inf.1 hn).1

theorem triEmb_rootDiagUnit {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L]
    [Algebra K L] {v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    {a : Fin TwistTag.D4.tag.rank → Kˣ} (hv : (v : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag a) :
    triEmb K σ L v = rootDiagUnit TwistTag.D4.tag
      (fun i => Units.map (algebraMap K L).toMonoidHom (a i)) := by
  rw [triEmb_apply, hv, baseChangeGL_rootDiagUnit]

end Base

section Main

theorem fieldActor_self_eq_of_cube {p f : ℕ} (hq : (p ^ f) % 3 = 1) (K : Type) [Field K]
    [Finite K] (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv3 : v ^ 3 = 1) : fieldActor (t := TwistTag.D4) σ σ v = v := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hv).1
  have hcube : ∀ i, a i ^ 3 = 1 := by
    intro i
    have h := congrArg Subtype.val hv3
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha, rootDiagUnit_pow,
      ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  have hσfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (a i) = a i := by
    intro i
    refine Units.ext ?_
    have hq' : p ^ f = 3 * ((p ^ f) / 3) + 1 := by omega
    have h1 : (a i : K) ^ 3 = 1 := by
      have := congrArg Units.val (hcube i)
      simpa using this
    change σ (a i : K) = (a i : K)
    rw [hσ, hq', pow_succ, pow_mul, h1, one_pow, one_mul]
  refine Subtype.ext ?_
  rw [coe_fieldActor, ha, units_map_entrywiseHom_rootDiagUnit]
  exact congrArg _ (funext hσfix)

theorem q1_line_data {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hn3 : n ^ 3 = 1) (hnv : n * v = v * n)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ ω : Kˣ, Units.map σ.toRingHom.toMonoidHom ω = ω ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (v : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] := by
  have hn3' : (n : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hn3]
    rfl
  have hW3 : (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩ :
        graphFixedRootMonomial TwistTag.D4 K σ.toRingHom) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hn3')
    rw [this, map_one]
  have hfa := fieldActor_self_eq_of_cube hq K σ hσ v hv hv3
  refine d4_fixed_line hp hp2 hf hq K hK σ hσ v n σ hv hv1 hv3 hnmono hnT hW3 (Or.inl rfl) ?_
  rw [MulAut.mul_apply, hfa, MulAut.conj_apply, hnv]
  group

theorem triEmb_not_mem_torus {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L]
    [Algebra K L] {n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L n ∉ torusGroup TwistTag.D4.tag L := by
  intro h
  apply hnT
  have hadj : (n : ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ n.2)).1
  exact Subgroup.mem_inf.2 ⟨CFSG.RankThree.Classical2.mem_torusGroup_of_baseChangeGL_mem
    (algebraMap K L) hadj h, graphFixedRootGroup_le _ _ _ n.2⟩

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
