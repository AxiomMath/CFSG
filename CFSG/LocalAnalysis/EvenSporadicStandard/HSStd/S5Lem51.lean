module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Sq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

theorem hs_exists_outer_involution (M : HS100Model) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : HSLemma21Setting G L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2) :
    ∃ v ∈ centralizer ({t} : Set G), v ∉ L ⊔ zpowers t ∧ v * v = 1 := by
  obtain ⟨hStd, hL, hCL, hfus, -⟩ := hset
  have hZ : center L = ⊥ := M.center_eq_bot L hL
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2 ▸ pow_orderOf_eq_one t
  have htL : t ∉ L := by
    intro htl
    have h1 : (⟨t, htl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 ht g g.2)
    rw [hZ, mem_bot] at h1
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht2
    omega
  have hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    hStd.centralizer_le_normalizer ht ht2
  have hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    hStd.centralizer_inf_centralizer_eq_zpowers hCL ht ht2
  obtain ⟨θ⟩ := M.equiv L hL
  obtain ⟨e, he⟩ := M.aut
  obtain ⟨u, huR, hu2⟩ := M.outer
  let D : AutModelData L ↥hs100R ↥hs100P :=
    { ι := Subgroup.inclusion hs100P_le_R
      ι_injective := Subgroup.inclusion_injective _
      θ := θ
      e := e
      he := fun w x => Subtype.ext (he w x) }
  obtain ⟨S, z, hSC, hS2, hSidx, hzS, hzL, hz2, hzc, n, hn, hnt⟩ := hfus t ht ht2
  exact exists_outer_involution D ht htt htL hC hker hidx M.card ⟨u, huR, hu2⟩ S hSC hS2 hSidx
    z hzL hz2 hzc n hn hnt M.count

end CFSG.EvenSporadicStandard.HSStd
