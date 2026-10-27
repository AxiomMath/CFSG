module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.One
public import CFSG.Milestones.ASVolI.A3Spor.Out

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem eq_top_of_J1
    {G : Type} [Group G] {S : Subgroup G} [S.Normal] (hcent : centralizer (S : Set G) = ⊥)
    (e : ↥S ≃* Carrier .J1) : S = ⊤ := by
  have hall := CFSG.ASVolI.burnsideA315s_allInner_J1 e
  rw [eq_top_iff]
  intro g _
  obtain ⟨l, hl⟩ := hall (MulAut.conjNormal (H := S) g)
  have h1 : MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) (l : G) := by
    rw [hl, MulAut.conjNormal_val]
  rw [conjNormal_injective_of_centralizer hcent h1]
  exact l.2

theorem card_centralizer_of_J1
    {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) (e : ↥S ≃* Carrier .J1) {t : G} (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set G)) = 120 := by
  have htop : S = ⊤ := eq_top_of_J1 hcent e
  have eG : G ≃* Carrier .J1 :=
    ((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e
  exact (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨eG⟩ t ht).1

theorem noZ2S5J1_holds :
    NoZ2S5J1 := by
  intro G _ _ S hSn ⟨e⟩ hcent t ht _ ⟨ζ⟩
  haveI := hSn
  have h120 := card_centralizer_of_J1 hcent e ht
  have h240 := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.card_centralizer_of_equiv ζ
  omega

theorem noTwoCfgJ1_holds :
    NoTwoCfgJ1 := by
  intro G _ _ S hSn ⟨e⟩ hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have h120 := card_centralizer_of_J1 hcent e h.ht
  have h480 := h.card_centralizer htop
  omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
