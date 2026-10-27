module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (fieldActor fixSubfield ringEquiv_cube_apply_eq)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3 (fixSubgroupFieldActorEquiv)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (trialityFieldImageEquivG2)


theorem K148G2SimpleFact_holds : K148G2SimpleFact := by
  intro K _ _ σ f hf hK hσ
  have hf1 : 1 ≤ f := by omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ3' : σ ^ 3 = 1 := td4g2_sigma_cube hK hσ
  have hσ1 : σ ≠ 1 := td4g2_frob_ne_one Nat.prime_two hf1 hK hσ
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3' hσ1
  have hF : Nat.card (fixSubfield σ) = 2 ^ f := by
    obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK' σ
    rw [hord, Nat.mul_div_cancel_left f (by norm_num : 0 < 3)] at hc
    exact hc
  have h4 : 4 ≤ 2 ^ f := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hF]
    omega
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast h3
  have hS := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3
  have hfix : CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) :=
    Subgroup.ext fun _ => Iff.rfl
  let e := (MulEquiv.subgroupCongr hfix).trans
    ((fixSubgroupFieldActorEquiv K σ hσ3).trans (trialityFieldImageEquivG2 σ hk3))
  haveI := hS
  exact e.isSimpleGroup

end CFSG.LocalAnalysis.GLTheoremA

end
