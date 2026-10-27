module

public import CFSG.ClassicalInvolution.RouteD.PatternBasic
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.RouteD.Leaf
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Generic (conjSub)

@[expose] def charOf {r : ℕ} (v : Fin r → ZMod 2) (γ : Fin r → ℤ) : ZMod 2 :=
  ∑ i, (γ i : ZMod 2) * v i

section Char

variable {r : ℕ} (v : Fin r → ZMod 2)

theorem charOf_sub (γ δ : Fin r → ℤ) : charOf v (γ - δ) = charOf v γ - charOf v δ := by
  simp only [charOf, Pi.sub_apply, Int.cast_sub, sub_mul]
  exact Finset.sum_sub_distrib _ _

theorem charOf_smul (c : ℤ) (γ : Fin r → ℤ) : charOf v (c • γ) = (c : ZMod 2) * charOf v γ := by
  simp only [charOf, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum, mul_assoc]

theorem charOf_single (j : Fin r) : charOf v (Pi.single j 1) = v j := by
  simp [charOf, Pi.single_apply]

end Char

section Weyl

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

theorem exists_weyl_of_charReach {v w : Fin D.rank → ZMod 2} (h : CharReach D.cartan v w) :
    ∃ W₀ : (coxeterMatrix D.isFiniteType).Group, ∀ j,
      charOf v (weylAction D.isFiniteType W₀ (Pi.single j 1)) = w j := by
  induction h with
  | refl => exact ⟨1, fun j => by rw [map_one, Module.End.one_apply, charOf_single]⟩
  | @tail b c _ hs ih =>
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨W₀, hW₀⟩ := ih
    refine ⟨W₀ * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i, fun j => ?_⟩
    rw [weylAction_mul_apply, weylAction_simple, reflection_apply_coroot, coroot_single, map_sub,
      map_zsmul, charOf_sub, charOf_smul, hW₀, hW₀]
    simp only [charRefl]
    rw [sub_eq_add_neg, CharTwo.neg_eq]

variable {D}

theorem exists_actsAs_of_charReach {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {v w : Fin D.rank → ZMod 2} (h : CharReach D.cartan v w) :
    ∃ (W₀ : (coxeterMatrix D.isFiniteType).Group) (k : K), ActsAs D k W₀ ∧
      ∀ j, charOf v (weylAction D.isFiniteType W₀ (Pi.single j 1)) = w j := by
  obtain ⟨W₀, hW₀⟩ := exists_weyl_of_charReach D h
  exact ⟨W₀, nrep hct W₀, actsAs_nrep hct W₀, hW₀⟩

theorem conjSub_rankOne_of_actsAs {k : K} {W₀ : (coxeterMatrix D.isFiniteType).Group}
    (hk : ActsAs D k W₀) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hγ' : -γ ∈ D.roots) :
    conjSub k (D.rootGroup γ ⊔ D.rootGroup (-γ)) =
      D.rootGroup (weylAction D.isFiniteType W₀ γ) ⊔
        D.rootGroup (-weylAction D.isFiniteType W₀ γ) := by
  unfold conjSub
  rw [Subgroup.map_sup, hk γ hγ, hk (-γ) hγ', map_neg]

end Weyl

end CFSG.ClassicalInvolution.RouteD
