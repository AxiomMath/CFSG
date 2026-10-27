module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapCentral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

universe u v w

variable {L : Type u} {F : Type v} [Group L] [Group F]

theorem odd_kernel_injective_on_two_subgroup (f : L →* F)
    (hodd : Odd (Nat.card f.ker)) (A : Subgroup L) (hA : IsPGroup 2 A) :
    Function.Injective (f.comp A.subtype) := by
  intro x y hxy
  change f (x : L) = f (y : L) at hxy
  have hker : (x : L)⁻¹ * (y : L) ∈ f.ker := by
    change f ((x : L)⁻¹ * (y : L)) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hAxy : (x : L)⁻¹ * (y : L) ∈ A :=
    A.mul_mem (A.inv_mem x.property) y.property
  have heq : (x : L)⁻¹ * (y : L) = 1 :=
    Subgroup.disjoint_def.mp (odd_subgroup_disjoint_two_subgroup A f.ker hA hodd) hAxy hker
  exact Subtype.ext (inv_mul_eq_one.mp heq)

theorem regularOn_compHom_of_odd_kernel {Omega : Type w} [MulAction F Omega]
    (f : L →* F) (hodd : Odd (Nat.card f.ker)) (A : Subgroup L)
    (hA : IsPGroup 2 A) (X : Set Omega) (hreg : IsRegularOn (A.map f) X) :
    letI : MulAction L Omega := MulAction.compHom Omega f
    IsRegularOn A X := by
  let : MulAction L Omega := MulAction.compHom Omega f
  have hinj := odd_kernel_injective_on_two_subgroup f hodd A hA
  intro a b ha hb
  obtain ⟨r0, hr0, huniq⟩ := hreg ha hb
  obtain ⟨r, hrA, hfr⟩ := r0.property
  let rA : A := ⟨r, hrA⟩
  refine ⟨rA, ?_, ?_⟩
  · change f r • a = b
    rw [hfr]
    exact hr0
  · intro s hs
    let s0 : A.map f := ⟨f (s : L), Subgroup.mem_map_of_mem f s.property⟩
    have hs0 : (s0 : F) • a = b := hs
    have heq : s0 = r0 := huniq s0 hs0
    apply hinj
    change f (s : L) = f r
    exact (congrArg Subtype.val heq).trans hfr.symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
