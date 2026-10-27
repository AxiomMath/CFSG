module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4InNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Line
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Twist
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Lang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Class
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Pair
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame2
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial CFSG
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem q1_toral_data {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgen : ∀ S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), v ∈ S → n ∈ S →
      E ≤ S)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hn3 : n ^ 3 = 1) (hnv : n * v = v * n)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ (y z : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      y ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      ∃ hz : z ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K),
        twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) y =
          z * y ∧
        (∀ e ∈ E, y * triEmb K σ (AlgebraicClosure K) e * y⁻¹ ∈
          torusGroup TwistTag.D4.tag (AlgebraicClosure K)) ∧
        (z ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) ∨
          ∃ u : WeylGroup TwistTag.D4.tag, ∀ x,
            (u * weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨z⁻¹, inv_mem hz⟩ *
              (weylTwist TwistTag.D4 u)⁻¹) • x =
            d4T36M 1 *ᵥ permLattice TwistTag.D4.perm.symm x) := by
  classical
  have hp : p.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨ω, -, hω3, hω1, hvω⟩ := q1_line_data hp hp2 hf hq K hK σ hσ v n hv hv1 hv3 hn3 hnv
    hnmono hnT
  set A : Lˣ := Units.map (algebraMap K L).toMonoidHom ω with hAdef
  have hA3 : A ^ 3 = 1 := by rw [hAdef, ← map_pow, hω3, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    apply hω1
    apply Units.map_injective (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective
    rw [map_one]
    exact h
  set d : ModGL TwistTag.D4.tag L :=
    rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) with hd
  have hιv : triEmb K σ L v = d := by
    rw [triEmb_rootDiagUnit hvω, hd]
    congr 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact map_one _
    · rfl
  have hνM := triEmb_mem_monomial (L := L) hnmono
  have hνC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L) n
  have hν3 : (triEmb K σ L n) ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
  have hνT := triEmb_not_mem_torus (L := L) hnT
  have hcommν : triEmb K σ L n * d = d * triEmb K σ L n := by
    rw [← hιv, ← map_mul, ← map_mul, hnv]
  obtain ⟨Y, hY, a, hYa, hreg⟩ := d4_toral_conj_A2 hA3 hA1 hνM hνC hν3 hνT hcommν
  set y : ModGL TwistTag.D4.tag L := Y⁻¹ with hydef
  have hy : y ∈ rootSpan TwistTag.D4.tag L d4LongA2 := inv_mem hY
  have hya : y * triEmb K σ L n * y⁻¹ = rootDiagUnit TwistTag.D4.tag a := by
    rw [hydef, inv_inv]
    exact hYa
  have hFν : twistHom TwistTag.D4 L Fr (triEmb K σ L n) = triEmb K σ L n :=
    triEmb_fixed Fr hcomm n
  obtain ⟨b, hzmem, hzb, hsame⟩ := q1_F_data hq hy hya (fun α hα => (hreg α hα).2) hFν
  obtain ⟨hzM, hcls, hztor⟩ := d4_A2_conj_monomial _ hzmem a b hreg hsame hzb
  have hyG : y ∈ adjointGroup TwistTag.D4.tag L := rootSpan_le_adjointGroup L d4LongA2 hy
  have hcent : y * d = d * y := by
    have h := rootSpan_le_centralizer (τ := TwistTag.D4.tag) (K := L)
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) (S := d4LongA2)
      (fun α hα => (d4Minus_rootCharKernel hA3 hA1 α).2 hα) hy
    exact Subgroup.mem_centralizer_singleton_iff.1 h
  have hconjd : y * d * y⁻¹ = d := by
    rw [hcent]
    group
  set S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (torusGroup TwistTag.D4.tag L).comap ((MulAut.conj y).toMonoidHom.comp (triEmb K σ L))
    with hS
  have hvS : v ∈ S := by
    change y * triEmb K σ L v * y⁻¹ ∈ torusGroup TwistTag.D4.tag L
    rw [hιv, hconjd]
    exact rootDiagUnit_mem_torusGroup _
  have hnS : n ∈ S := by
    change y * triEmb K σ L n * y⁻¹ ∈ torusGroup TwistTag.D4.tag L
    rw [hya]
    exact rootDiagUnit_mem_torusGroup _
  have hyE : ∀ e ∈ E, y * triEmb K σ L e * y⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    fun e he => hgen S hvS hnS he
  refine ⟨y, twistHom TwistTag.D4 L Fr y * y⁻¹, hyG, hzM, (inv_mul_cancel_right _ _).symm, hyE, ?_⟩
  have hinv : weylQuotientHom TwistTag.D4.tag L
      ⟨(twistHom TwistTag.D4 L Fr y * y⁻¹)⁻¹, inv_mem hzM⟩ =
      (weylQuotientHom TwistTag.D4.tag L ⟨twistHom TwistTag.D4 L Fr y * y⁻¹, hzM⟩)⁻¹ :=
    map_inv (weylQuotientHom TwistTag.D4.tag L) ⟨twistHom TwistTag.D4 L Fr y * y⁻¹, hzM⟩
  rcases hcls with h1 | hA | hB
  · exact Or.inl (hztor.2 h1)
  · obtain ⟨u, hu⟩ := q1_class_witness (Or.inl hA)
    exact Or.inr ⟨u, fun x => by rw [hinv]; exact hu x⟩
  · obtain ⟨u, hu⟩ := q1_class_witness (Or.inr hB)
    exact Or.inr ⟨u, fun x => by rw [hinv]; exact hu x⟩

theorem d4_toral_q1 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (K : Type) [Field K] [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hanis : ∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R →
      R ≠ ⊥ → ¬ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∃ F : D4PhiFrame K σ (p ^ f) 1, F.Contains (E.map (β⁻¹).toMonoidHom)) ∧
      ∃ F : D4SteinbergFrame K σ (p ^ f) 1, F.Contains (E.map (β⁻¹).toMonoidHom) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β, v, hv, n, hn, hv1, hvT, hnM, hnT⟩ :=
    d4_aniso_plane_q1 hp hp2 hf K hK σ hσ hq E hEcard hanis
  refine ⟨β, ?_⟩
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'ea : IsElementaryAbelian 3 E' := IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hE'3 : ∀ e ∈ E', e ^ 3 = 1 := fun e he => elemPow_eq_one_of_isElementaryAbelian e he
  have hnv : n * v = v * n :=
    congrArg Subtype.val ((inferInstance : IsMulCommutative E').is_comm.comm ⟨n, hn⟩ ⟨v, hv⟩)
  have hnz : n ∉ Subgroup.zpowers v := by
    intro h
    apply hnT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [Subgroup.coe_zpow]
    exact zpow_mem hvT k
  have hgen := plane_le_of_pair E' hcard' hE'3 hv hn hv1 hnz
  obtain ⟨y, z, hy, hz, hFy, hyE, hcase⟩ := q1_toral_data hp2 hf hq K hK σ hσ E' v n hgen hvT hv1
    (hE'3 v hv) (hE'3 n hn) hnv hnM hnT
  rcases hcase with hzT | ⟨u, hu⟩
  · exfalso
    obtain ⟨R, hRp, hR1, hER⟩ := d4_toral_split_normalizes hf K hK σ hσ E' hy hzT hFy hyE
    obtain ⟨R', hR'p, hR'1, hER'⟩ := normalizes_of_map (β⁻¹) E R hRp hR1 hER
    exact hanis R' hR'p hR'1 hER'
  · exact ⟨d4PhiFrame_of_toral hf K hK σ hσ E' hy hz hFy hyE u hu,
      d4SteinbergFrame_of_toral K σ hσ (Or.inl rfl) E' hE'3 hy hz hFy hyE u hu⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
