module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique.Setup.X35

theorem sectionProductionProp_of_irreducibleSection (hSec : X1.IrreducibleSectionProp) :
    SectionProductionProp := by
  intro V _ _ hV G L A hL hA hne
  obtain ⟨hAN, -, ⟨S⟩⟩ := hSec V hV G L A hL hA hne
  set ρ : ↥L →* MulAut S.W := S.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  refine ⟨S.W, S.commGroup, S.finite, ρ, (S.τW.comp (Subgroup.inclusion le_sup_right)).range,
    ?_, S.nontrivial, S.lbar_ne_bot, ?_, S.abar_ne_bot, S.abar_elem, ?_, S.abar_offender⟩
  · intro w
    obtain ⟨v, rfl⟩ := S.π_surjective w
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (hV v)
    rw [this, map_one]
  · intro U hU
    exact S.irreducible U fun x hx u hu =>
      hU (S.τW x) ⟨⟨x, hx⟩, congrArg S.τW (Subtype.ext rfl)⟩ u hu
  · have key : ∀ a : ↥(L ⊔ A), (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) →
        ∀ y ∈ ρ.range, S.τW a * y * (S.τW a)⁻¹ ∈ ρ.range := by
      rintro a ha _ ⟨l, rfl⟩
      have hl : (a : MulAut V) * (l : MulAut V) * (a : MulAut V)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 ha l).1 l.2
      refine ⟨⟨_, hl⟩, ?_⟩
      have h1 : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A)
          ⟨(a : MulAut V) * (l : MulAut V) * (a : MulAut V)⁻¹, hl⟩ =
          a * Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A) l * a⁻¹ := Subtype.ext rfl
      rw [hρ, MonoidHom.comp_apply, h1, map_mul, map_mul, map_inv]
      rfl
    rintro _ ⟨a, rfl⟩
    have haN : ((Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A) a : ↥(L ⊔ A)) : MulAut V) ∈
        Subgroup.normalizer (L : Set (MulAut V)) := hAN a.2
    have haN' : (((Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A) a)⁻¹ : ↥(L ⊔ A)) : MulAut V) ∈
        Subgroup.normalizer (L : Set (MulAut V)) := (Subgroup.normalizer _).inv_mem haN
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact key _ haN y hy
    · intro hy
      have := key _ haN' _ hy
      rw [map_inv] at this
      simpa [mul_assoc] using this

theorem familyTop_of_L1b
    (hspor : NoSporadicComponentProp)
    (hlin3 : PrimeLinearThreeExclusionProp) (huni3 : PrimeUnitaryThreeExclusionProp) :
    OneQuasisimpleResidualProp :=
  familyTop Layer.Actor.actorLayerProp Layer.Actor.actorComponentTransfer
    Layer.Actor.componentTransferProp Layer.Actor.irreducibleSectionProp hspor
    (sectionProductionProp_of_irreducibleSection Layer.Actor.irreducibleSectionProp) hlin3 huni3

end CFSG.QuasithinUnique.Setup.Family
