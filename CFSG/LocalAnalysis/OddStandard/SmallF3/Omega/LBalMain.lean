module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.LBalTransport
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219D

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.HarrisLit

variable {G : Type} [Group G]

theorem aschLBalance_of_aschA1 [Finite G] (hA1 : AschA1 G) : AschLBalance G := by
  intro u y hu hy huy J hJ
  have hle : centralizer ({u, y} : Set G) ≤ centralizer ({y} : Set G) :=
    centralizer_pair_le u y
  have huY : u ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact huy.symm
  obtain ⟨s, hsu⟩ : ∃ s : ↥(centralizer ({y} : Set G)), (s : G) = u := ⟨⟨u, huY⟩, rfl⟩
  subst hsu
  have hs : orderOf s = 2 := by rw [← Subgroup.orderOf_coe]; exact hu
  have hJ' := isTwoComponentIn_subgroupOf_of_isComponentIn y s hJ
  obtain ⟨K', hK'2, -, -, -, hlast⟩ :=
    (harris82Lemma219Input_holds (centralizer ({y} : Set G)) s hs).2 _ hJ'
  have hJ'le : J.subgroupOf (centralizer ({y} : Set G)) ≤
      K' ⊔ K'.map (MulAut.conj s).toMonoidHom := by
    rw [← hlast]
    refine le_trans ?_ (le_iSup (fun g : ↥(twoLayer (centralizer ({y} : Set G))) =>
      (J.subgroupOf (centralizer ({y} : Set G))).map
        (MulAut.conj (g : ↥(centralizer ({y} : Set G)))).toMonoidHom) 1)
    intro x hx
    exact ⟨x, hx, by simp⟩
  refine ⟨K'.map (centralizer ({y} : Set G)).subtype,
    isComponentIn_map_subtype_of_isTwoComponent hA1 hy hK'2, ?_⟩
  have hJeq : (J.subgroupOf (centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype =
      J := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (hJ.1.trans hle)
  calc J = (J.subgroupOf (centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype :=
        hJeq.symm
    _ ≤ (K' ⊔ K'.map (MulAut.conj s).toMonoidHom).map (centralizer ({y} : Set G)).subtype :=
        Subgroup.map_mono hJ'le
    _ = K'.map (centralizer ({y} : Set G)).subtype ⊔
          CFSG.conjugate (K'.map (centralizer ({y} : Set G)).subtype) (s : G) := by
        rw [Subgroup.map_sup, map_subtype_conj_eq_conjugate hu s rfl K']

theorem sec3SettingLB_of_sec3Setting [Finite G] {t : G} {L : Subgroup G}
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hn : ¬ CFSG.Blueprint.Catalog G)
    (h : Sec3Setting G t L) : Sec3SettingLB G t L :=
  { toSec3Setting := h
    lBalance := aschLBalance_of_aschA1 h.a1
    kProper := hK
    notCat := hn }

end CFSG.OddStandard.SmallF3.Omega
