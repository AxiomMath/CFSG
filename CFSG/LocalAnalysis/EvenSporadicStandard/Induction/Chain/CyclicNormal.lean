module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Quasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulRank

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem conjClosure_le_of_le_normalizer {M T : Subgroup H} (hT : T ≤ normalizer (M : Set H)) :
    conjClosure M T ≤ M := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨m, hm, rfl⟩
  exact (mem_normalizer_iff.1 (hT hg) m).1 hm

theorem le_normalizer_of_cyclic_centralizer [Finite H] {R T M : Subgroup H}
    (hM : IsCompIn M (centralizer (R : Set H))) (hT : T ≤ centralizer (R : Set H))
    (hrank : ∀ y : H, 3 ≤ CFSG.pRank 2 ↥(M.map (MulAut.conj y).toMonoidHom))
    (hcyc : ∃ S : Sylow 2 (centralizer (M : Set H)), IsCyclic ↥S) :
    T ≤ normalizer (M : Set H) := by
  intro x hx
  by_contra hxn
  have hne : M.map (MulAut.conj x).toMonoidHom ≠ M := fun h =>
    hxn (Solomon78.mem_normalizer_iff_map_conj_eq.2 h)
  have hM₁ : IsCompIn (M.map (MulAut.conj x).toMonoidHom) (centralizer (R : Set H)) :=
    hM.map_conj (hT hx)
  have hc := hM₁.commute_of_ne hM hne
  have hle : M.map (MulAut.conj x).toMonoidHom ≤ centralizer (M : Set H) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun m hm => (hc y hy m hm).symm
  obtain ⟨S, hS⟩ := hcyc
  have h3 := hrank x
  have hev : Even (Nat.card (centralizer (M : Set H))) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 (even_card_of_three_le_pRank h3)).trans
      (Subgroup.card_dvd_of_le hle))
  have h1 := CFSG.OddStandard.AltStdFaithful.pRank_two_eq_one_of_isCyclic hev S hS
  have h2 : CFSG.pRank 2 ↥(M.map (MulAut.conj x).toMonoidHom) ≤
      CFSG.Open.pRank 2 (centralizer (M : Set H)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.SectionRank.pRank_mono (by norm_num) hle
  omega

end CFSG.EvenSporadicStandard.Induction
