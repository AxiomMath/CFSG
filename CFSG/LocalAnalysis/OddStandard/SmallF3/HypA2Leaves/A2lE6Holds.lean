module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTwE6Three
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Transport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Component
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Cube
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Levi

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Open (StatedSU)


theorem a2lTwistedE6ThreeSU6_holds : a2lTwistedE6ThreeSU6 := by
  intro X _ _ hX
  have hc := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨K, hF, hfin, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card
    TwistTag.E6 (p := 3) (f := 1) Nat.prime_three le_rfl hc.2
  have hK : Nat.card K = 9 := by rw [hcard]; decide
  have hK3 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  have hσ3 : ∀ c, σ c = c ^ 3 := fun c => by simpa using hσ c
  haveI : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three (by norm_num) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  obtain ⟨ζ, hζ, hσζ⟩ := exists_trace_zero σ (q := 3) (by norm_num) hK3 hσ3
  obtain ⟨e₀, he₀⟩ := a2lE6_exists_equiv_statedSU σ hK hσ3 hζ hσζ
  let x₀ : SU σ 6 :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ), a2lE6_scalar_neg_one_mem_SU σ⟩
  have hx₀ : (x₀ : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ) := rfl
  have hda := a2lE6_leviHomA_neg_one σ hζ x₀ hx₀
  have hdT : rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) ∈ twE6LeviSA K σ := by
    rw [← range_fixAToMod σ]
    exact ⟨leviHom σ hζ hσζ x₀, hda⟩
  have hdC := a2lE6_twE6LeviSA_le σ hK hσ3 hdT
  have hCA : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ adjointGroup .E6 K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left
  have hHC : subsystemGroup .E6 K e6LeviA5 ⊓ graphFixedRootGroup TwistTag.E6 K σ.toRingHom =
      twE6LeviSA K σ := by
    rw [a2lE6_subsystemGroup_eq]
    exact a2lE6_groupA_inf σ hK hσ3
  obtain ⟨T, φ, hcomp, hz, hφ⟩ := a2lE6_component_transport
    (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) e hdC a2l_rootDiagUnit_e6BitsA5_mem hCA
    (a2lE6_component_toral hK) hHC (a2lE6_twE6LeviSA_quasisimple σ hK hσ3)
  have hd2 : orderOf (rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact a2l_rootDiagUnit_e6BitsA5_mul_self)
      (a2l_rootDiagUnit_e6BitsA5_ne_one hK2)
  let φ' : ↥T ≃* ↥(twE6LeviSA K σ) := φ
  let e₁ : ↥T ≃* StatedSU 6 3 K := φ'.trans e₀
  refine ⟨T, e.symm ⟨_, hdC⟩, K, hF, hK, ?_, hcomp, hz, e₁, ?_⟩
  · calc orderOf (e.symm ⟨_, hdC⟩) = orderOf (⟨_, hdC⟩ : ↥(graphFixedRootGroup TwistTag.E6 K
          σ.toRingHom)) := MulEquiv.orderOf_eq _ _
      _ = orderOf (rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5)) := Subgroup.orderOf_mk _ _
      _ = 2 := hd2
  · exact he₀ x₀ hx₀ (φ ⟨_, hz⟩) (hφ.trans hda.symm)

end CFSG.OddStandard.SmallF3.HypA2Leaves
