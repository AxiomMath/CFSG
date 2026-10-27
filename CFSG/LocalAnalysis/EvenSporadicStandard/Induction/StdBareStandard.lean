module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

variable {H : Type} [Group H]

theorem normalizer_centralizer_eq_of_even {L : Subgroup H}
    (hev : Even (Nat.card (centralizer (L : Set H))))
    (htight : ∀ g : H, g ∉ normalizer (L : Set H) →
      Odd (Nat.card (↥(centralizer (L : Set H) ⊓
        (centralizer (L : Set H)).map (MulAut.conj g).toMonoidHom : Subgroup H)))) :
    normalizer ((centralizer (L : Set H) : Subgroup H) : Set H) = normalizer (L : Set H) := by
  refine le_antisymm (fun g hg => ?_)
    (GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
  by_contra hgL
  have hodd := htight g hgL
  have hmap : (centralizer (L : Set H)).map (MulAut.conj g).toMonoidHom =
      centralizer (L : Set H) :=
    (mem_normalizer_iff_map_conj_eq (H := centralizer (L : Set H)) (g := g)).1 hg
  rw [hmap, inf_idem] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) hev

theorem standardComponentIsStandard_iff_stdBare {L : Subgroup H} :
    CFSG.Open.standardComponentIsStandard L ↔
      CFSG.Open.IsQuasisimple L ∧ Even (Nat.card (centralizer (L : Set H))) ∧ StdBare L := by
  constructor
  · rintro ⟨hq, hev, htight, hNC, hcomm⟩
    refine ⟨hq, hev, hcomm, fun g hg => htight g fun hgC => hg ?_⟩
    rw [← hNC]
    exact hgC
  · rintro ⟨hq, hev, hcomm, htight⟩
    have hNC := normalizer_centralizer_eq_of_even hev htight
    refine ⟨hq, hev, fun g hg => htight g fun hgL => hg ?_, hNC, hcomm⟩
    rw [hNC]
    exact hgL

theorem standardComponentIsStandard_of_stdBare' {L : Subgroup H}
    (hq : CFSG.Open.IsQuasisimple L) (hev : Even (Nat.card (centralizer (L : Set H))))
    (h : StdBare L) : CFSG.Open.standardComponentIsStandard L :=
  standardComponentIsStandard_iff_stdBare.2 ⟨hq, hev, h⟩

theorem even_card_centralizer_of_le_centralizer {L : Subgroup H} {t : H} (ht : orderOf t = 2)
    (hle : L ≤ centralizer ({t} : Set H)) : Even (Nat.card (centralizer (L : Set H))) :=
  StandardSubgroupAPI.even_card_of_mem_of_orderOf_eq_two
    (mem_centralizer_iff.2 fun _ hx => mem_centralizer_singleton_iff.1 (hle hx)) ht

end CFSG.EvenSporadicStandard.Induction
