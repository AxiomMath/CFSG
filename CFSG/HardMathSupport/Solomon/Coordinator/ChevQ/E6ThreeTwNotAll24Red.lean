module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree

namespace KSNotAll24

theorem ker_inv_sub_one {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (t : LinearMap.GeneralLinearGroup F V) :
    LinearMap.ker (((t⁻¹ : LinearMap.GeneralLinearGroup F V) : Module.End F V) - 1) =
      LinearMap.ker ((t : Module.End F V) - 1) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have h1 : ∀ w, (t : Module.End F V) (((t⁻¹ : LinearMap.GeneralLinearGroup F V) :
      Module.End F V) w) = w := fun w => by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h2 : ∀ w, ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : Module.End F V)
      ((t : Module.End F V) w) = w := fun w => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  constructor
  · intro h
    calc (t : Module.End F V) v = (t : Module.End F V) (((t⁻¹ :
        LinearMap.GeneralLinearGroup F V) : Module.End F V) v) := by rw [h]
      _ = v := h1 v
  · intro h
    calc ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : Module.End F V) v =
        ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : Module.End F V) ((t : Module.End F V) v) := by
          rw [h]
      _ = v := h2 v

theorem eq_or_eq_inv_of_mem_zpowers {G : Type*} [Group G] {c f : G} (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hf : f ∈ Subgroup.zpowers c) (hf1 : f ≠ 1) : f = c ∨ f = c⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
  have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hk : c ^ k = c ^ (k % 3) := by
    have := zpow_mod_orderOf c k
    rw [ho] at this
    exact this.symm
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exact absurd (by rw [hk, h, zpow_zero]) hf1
  · left
    rw [hk, h, zpow_one]
  · right
    have h2 : c ^ (2 : ℤ) = c ^ 2 := by norm_cast
    rw [hk, h, h2]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc3)

end KSNotAll24

section Structure

set_option linter.unusedSectionVars false

theorem KSNotAll24.twE6FixDim_inv (K : Type) [Field K] (σ : K ≃+* K)
    (s : twistedE6RootGroup K σ) : twE6FixDim K σ s⁻¹ = twE6FixDim K σ s := by
  unfold twE6FixDim
  rw [Subgroup.coe_inv, KSNotAll24.ker_inv_sub_one]

end Structure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
