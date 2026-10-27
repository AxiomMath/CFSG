module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Om6M

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_not_pocket [Finite G] (h35 : Asc82Lemma35) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {v y b : G} {V W Y : Subgroup G} (hv : orderOf v = 2)
    (hVc : IsComponentIn V (centralizer ({v} : Set G)))
    (hWc : IsComponentIn W (centralizer ({v} : Set G))) (hWF : InFStar W) (hne : W ≠ V)
    (hy : orderOf y = 2) (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InFStar Y)
    (hbV : b ∈ V) (hVY : V ≤ Y) (hpocket : IsI4PlusIn Y b) : False := by
  obtain ⟨hb2, K, hK⟩ := hpocket
  have hbY : b ∈ Y := hVY hbV
  have hKC : Sl23PocketIn (centralizer ({y} : Set G)) b K :=
    sec63_pocket_of_subnormal hK hYc.1 hYc.2.2
  have hdata : Sec3PocketData y Y b K :=
    ⟨hy, hYc, hYF, hb2, hbY, hK.2.1.trans inf_le_left, hKC⟩
  have hbv : b ∈ centralizer ({v} : Set G) := hVc.1 hbV
  have hvb : v ∈ centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hbv).symm
  have hWb : W ≤ centralizer ({b} : Set G) := by
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hVc.commute_of_ne hWc hne.symm b hbV c hc).symm)
  refine h35 G t L hS y Y b K v hdata hv hvb W ⟨?_, hWF⟩
  rw [centralizer_pair_eq_inf]
  exact hWc.mono (le_inf hWc.1 hWb) inf_le_left

end CFSG.OddStandard.SmallF3.Omega
