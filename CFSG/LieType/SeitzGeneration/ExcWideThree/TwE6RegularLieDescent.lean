module

public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

section Descent


theorem twE6_descent_of_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hx : x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hxF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x) (hxp : ∃ n : ℕ, x ^ (p ^ n) = 1) :
    ∃ u ∈ twistedE6RootGroup K σ, baseChangeGL (algebraMap K (AlgebraicClosure K)) u = x := by
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := ℓ) (f := f) hℓ hf K
      hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  have hNR : ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr) =
      ⁅(⊤ : Subgroup (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)), ⊤⁆ := by
    have h1 : ⁅twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
        Subgroup.map (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr).subtype
          ⁅(⊤ : Subgroup (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hder, h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  haveI hnorm : (((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).Normal := by
    rw [hNR]
    infer_instance
  have hxR : x ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2 ⟨hx, hxF⟩
  have hPR : Subgroup.zpowers x ≤ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    Subgroup.zpowers_le.2 hxR
  obtain ⟨n, hn⟩ := hxp
  have hPp : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hn, one_zpow]
  haveI : Finite (Subgroup.zpowers x) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ n, pow_pos hp.pos n, hn⟩).finite_zpowers
  have hle := le_of_isPGroup_of_index_eq_pow hPR hp Nat.prime_three hp3 hk hPp
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 (hle (Subgroup.mem_zpowers x))
  exact ⟨u, hu, hux⟩

end Descent

end CFSG.LieType.SeitzGeneration.ExcWideThree
