module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNComps
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

theorem not_isHNType_of_properFixedComponent_M
    {S : Type} [Group S] [Finite S] [hs : IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .M) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ IsHNType (P ⧸ Open.fusionZStar P) :=
  not_isHNType_of_comps hna
    (fun σ hσ => oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M hna e) hσ)
    (fun t ht K hK hc => by
      obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput S hs ⟨e⟩ t ht K hK
      rw [hc] at h41
      exact absurd h41 (by decide))
    (fun α _ hα => absurd (CatLeafProof.monsterInnerInput S hs ⟨e⟩ α) hα)
    h

end CFSG.ComponentClassification.EvenPump
