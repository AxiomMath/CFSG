module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem map_fixedPointSubgroup_conj_eq {Ψ : Set (Fin τ.rank → ℤ)}
    {F F' : ModGL τ L →* ModGL τ L} {z : ModGL τ L}
    (hconj : ∀ g, F' (z⁻¹ * g * z) = z⁻¹ * F g * z)
    (hzN : z ∈ Subgroup.normalizer (rootSpan τ L Ψ))
    (hzC : z ∈ adjointGroup τ L) :
    (fixedPointSubgroup F (rootSpan τ L Ψ)).map (MulAut.conj z⁻¹).toMonoidHom =
      rootSpan τ L Ψ ⊓ (adjointGroup τ L ⊓ F'.eqLocus (MonoidHom.id _)) := by
  have hzinv : z⁻¹ ∈ Subgroup.normalizer (rootSpan τ L Ψ) := inv_mem hzN
  have hzCinv : z⁻¹ ∈ adjointGroup τ L := inv_mem hzC
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨hxS, hxF⟩, rfl⟩
    have hφx : (MulAut.conj z⁻¹).toMonoidHom x = z⁻¹ * x * z := by simp
    rw [hφx]
    have hxA : x ∈ adjointGroup τ L := rootSpan_le_adjointGroup L Ψ hxS
    refine ⟨(Subgroup.mem_normalizer_iff.mp hzinv x).1 hxS, mul_mem (mul_mem hzCinv hxA) hzC, ?_⟩
    show F' (z⁻¹ * x * z) = z⁻¹ * x * z
    rw [hconj, hxF]
  · rintro x ⟨hxS, hxC, hxF'⟩
    have hxS' : z * x * z⁻¹ ∈ rootSpan τ L Ψ :=
      (Subgroup.mem_normalizer_iff.mp hzN x).1 hxS
    have hxC' : z * x * z⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hzC hxC) hzCinv
    have harg : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    have hfix : F (z * x * z⁻¹) = z * x * z⁻¹ := by
      have h1 := hconj (z * x * z⁻¹)
      rw [harg, hxF', MonoidHom.id_apply] at h1
      calc F (z * x * z⁻¹) = z * (z⁻¹ * F (z * x * z⁻¹) * z) * z⁻¹ := by group
        _ = z * x * z⁻¹ := by rw [← h1]
    refine Subgroup.mem_map.2 ⟨z * x * z⁻¹, ⟨hxS', hfix⟩, ?_⟩
    have hφ : (MulAut.conj z⁻¹).toMonoidHom (z * x * z⁻¹) = z⁻¹ * (z * x * z⁻¹) * z := by simp
    rw [hφ]
    group

theorem map_fixedPointSubgroup_conj_eq_of_pin {Ψ : Set (Fin τ.rank → ℤ)}
    {F F' : ModGL τ L →* ModGL τ L} {y z : ModGL τ L}
    (hF' : ∀ g, F' g = y * F g * y⁻¹) (hz : F z = z * y)
    (hzN : z ∈ Subgroup.normalizer (rootSpan τ L Ψ))
    (hzC : z ∈ adjointGroup τ L) :
    (fixedPointSubgroup F (rootSpan τ L Ψ)).map (MulAut.conj z⁻¹).toMonoidHom =
      rootSpan τ L Ψ ⊓ (adjointGroup τ L ⊓ F'.eqLocus (MonoidHom.id _)) := by
  refine map_fixedPointSubgroup_conj_eq ?_ hzN hzC
  intro g
  rw [hF', map_mul, map_mul, map_inv, hz]
  group

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
