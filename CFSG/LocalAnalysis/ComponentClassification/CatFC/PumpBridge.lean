module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem autCentralizer_eq_fixedSubgroup {S : Type*} [Group S] (τ : MulAut S) :
    EvenSporadicStandard.HSStd.autCentralizer τ = fixedSubgroup τ :=
  Subgroup.ext fun _ => Iff.rfl

theorem fixedComponent_of_pump {S : Type} [Group S] {τ : MulAut S} {N : Subgroup S}
    (hle : N ≤ EvenSporadicStandard.HSStd.autCentralizer τ) (hq : CFSG.IsQuasisimple ↥N)
    (hsub : (N.subgroupOf (EvenSporadicStandard.HSStd.autCentralizer τ)).IsSubnormal) :
    ∃ D : Subgroup ↥(fixedSubgroup τ), IsComponent D ∧ Nonempty (↥D ≃* ↥N) := by
  let K : Subgroup ↥(EvenSporadicStandard.HSStd.autCentralizer τ) :=
    N.subgroupOf (EvenSporadicStandard.HSStd.autCentralizer τ)
  let eK : ↥K ≃* ↥N := Subgroup.subgroupOfEquivOfLe hle
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hq
  let φ : ↥(EvenSporadicStandard.HSStd.autCentralizer τ) ≃* ↥(fixedSubgroup τ) :=
    MulEquiv.subgroupCongr (autCentralizer_eq_fixedSubgroup τ)
  refine ⟨K.map φ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv φ ⟨hKq, hsub⟩, ?_⟩
  exact ⟨((K.equivMapOfInjective φ.toMonoidHom φ.injective).symm).trans eK⟩

theorem nonabelian_of_quasisimple {S : Type*} [Group S] {N : Subgroup S}
    (hq : CFSG.IsQuasisimple ↥N) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hcomm a' b')

end CFSG.ComponentClassification.CatFC
