module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27ComponentLayer
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem four_dvd_card_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.IsQuasisimple Q) : 4 ∣ Nat.card Q := by
  obtain ⟨hperf, hsimple, a, b, hab⟩ := h
  refine CFSG.GorensteinWalter.isQuasisimple_four_dvd_card
    ⟨?_, Group.isPerfect_def.1 hperf, hsimple⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  exact hab (Subsingleton.elim _ _)

variable {H : Type} [Group H]

theorem isCompIn_map_conj_eq [Finite H] {C M : Subgroup H} (hM : IsCompIn M C)
    (h4M : 4 ∣ Nat.card M) (h4 : ¬ 4 ∣ Nat.card (centralizer (M : Set H))) {c : H} (hc : c ∈ C) :
    M.map (MulAut.conj c).toMonoidHom = M := by
  by_contra hne
  have hcomm := IsCompIn.commute_of_ne (hM.map_conj hc) hM hne
  have hle : M.map (MulAut.conj c).toMonoidHom ≤ centralizer (M : Set H) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  apply h4
  refine h4M.trans ?_
  have hcard : Nat.card (M.map (MulAut.conj c).toMonoidHom) = Nat.card M :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem isCompIn_conj_mem [Finite H] {C M : Subgroup H} (hM : IsCompIn M C) (h4M : 4 ∣ Nat.card M)
    (h4 : ¬ 4 ∣ Nat.card (centralizer (M : Set H))) {c : H} (hc : c ∈ C) {m : H} (hm : m ∈ M) :
    c * m * c⁻¹ ∈ M := by
  have h : c * m * c⁻¹ ∈ M.map (MulAut.conj c).toMonoidHom := ⟨m, hm, by simp [MulAut.conj_apply]⟩
  rwa [isCompIn_map_conj_eq hM h4M h4 hc] at h

theorem centralizer_le_normalizer_of_stdBare {L : Subgroup H} (hstd : StdBare L) {t : H}
    (ht2 : orderOf t = 2) (htL : t ∈ centralizer (L : Set H)) :
    centralizer ({t} : Set H) ≤ normalizer (L : Set H) := fun _ hg =>
  CFSG.StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hstd.2 htL ht2
    (mem_centralizer_singleton_iff.1 hg)

end CFSG.EvenSporadicStandard.Induction.Balance
