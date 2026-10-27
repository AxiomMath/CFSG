module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAssembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaNeighbourAlternative
  OmegaCatalogueClausesAt OmegaOvergroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Root


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def rootTorusG (e : L ≃* adjointGroup .E7 K) : Subgroup G :=
  (((EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map e.symm.toMonoidHom).map
    L.subtype

@[expose] noncomputable def rootLeviG (e : L ≃* adjointGroup .E7 K) : Subgroup G :=
  ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype

theorem mem_centralizer_rootTorusG (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : t ∈ centralizer (L : Set G)) : t ∈ centralizer (rootTorusG e : Set G) :=
  centralizer_le (map_subtype_le _) ht

@[expose] def HR8FieldE7 (e : L ≃* adjointGroup .E7 K) (t : G) (f : ℕ) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    ∃ Kc : Subgroup (centralizer (rootTorusG e : Set G) ⧸
        oddCore (centralizer (rootTorusG e : Set G))), IsComponent Kc ∧
      ((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc ∧
      ((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))) < Kc ∧
      QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩ ∉ Kc ∧
      ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩ ∈
          normalizer (Kc : Set (centralizer (rootTorusG e : Set G) ⧸
            oddCore (centralizer (rootTorusG e : Set G)))),
        OmegaOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 f

@[expose] def HR8SwapE7 (e : L ≃* adjointGroup .E7 K) (t : G) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    ∃ Kc : Subgroup (centralizer (rootTorusG e : Set G) ⧸
        oddCore (centralizer (rootTorusG e : Set G))), IsComponent Kc ∧
      ((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* (((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))) : Subgroup _))

end Root

section HR8


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem hr8FieldE7_or_hr8SwapE7 (hcat : OmegaCatalogueClausesAt 6) {t : G} {f : ℕ}
    (hw : E7Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 K) :
    HR8FieldE7 e t f ∨ HR8SwapE7 e t := by
  have htX := mem_centralizer_rootTorusG e hw.mem_centralizer
  obtain ⟨⟨Kc, hKc, hDK, h1 | h2⟩, -⟩ := neighbour_overgroup_E7_torus hcat hw.standard hf
    hw.card_eq e hw.orderOf_eq (hw.inf_eq e) (X := rootTorusG e) (Or.inr rfl) htX
    (D := rootLeviG e) rfl
  · obtain ⟨h1a, h1b, h1c, hsN, hov⟩ := h1
    exact .inl ⟨htX, Kc, hKc, hDK, h1a, h1b, h1c, hsN, hov⟩
  · obtain ⟨h2a, h2b, h2c, h2d⟩ := h2
    exact .inr ⟨htX, Kc, hKc, hDK, h2a, h2b, h2c, h2d⟩


theorem hr8FieldE7_or_hr8SwapE7_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    {t : G} {f : ℕ} (hw : E7Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 K) :
    HR8FieldE7 e t f ∨ HR8SwapE7 e t :=
  hr8FieldE7_or_hr8SwapE7 (OmegaPilot.omegaCatalogueClausesAt_of_inputs hGLS hXodd hSpor) hw hf e

end HR8

end CFSG.SeitzReduction.E7Pilot
