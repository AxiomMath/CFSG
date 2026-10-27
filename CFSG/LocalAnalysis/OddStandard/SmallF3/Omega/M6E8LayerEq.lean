module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Prod
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Small
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem m6e8_J_component {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G}
    {r : G} (d : M6E8Datum t L y X Y T r) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({r} : Set G))) (hJI : layerCent Y r ≤ I) :
    IsComponentIn (layerCent Y r) (I ⊓ centralizer ({y} : Set G)) := by
  have hJc : layerCent Y r ≤ centralizer ({y} : Set G) := d.J_le_Y.trans d.hYc.1
  have hJH : layerCent Y r ≤ I ⊓ centralizer ({y} : Set G) := le_inf hJI hJc
  have hHle : I ⊓ centralizer ({y} : Set G) ≤ centralizer ({y, r} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    · have hzr : z = r := Set.mem_singleton_iff.mp hz
      rw [hzr]
      exact Subgroup.mem_centralizer_iff.mp (hI.1 hx.1) r (Set.mem_singleton r)
  exact d.comp.mono hJH hHle

private theorem m6e8_comp_unique {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G}
    {r : G} (d : M6E8Datum t L y X Y T r) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({r} : Set G))) (hJI : layerCent Y r ≤ I)
    (hI6 : IsOmega6Plus I)
    (hJcomp : IsComponentIn (layerCent Y r) (I ⊓ centralizer ({y} : Set G)))
    {K : Subgroup G} (hK : IsComponentIn K (I ⊓ centralizer ({y} : Set G))) :
    K = layerCent Y r := by
  by_contra hne
  have hcomm : ∀ a ∈ K, ∀ b ∈ layerCent Y r, a * b = b * a :=
    IsComponentIn.commute_of_ne hK hJcomp hne
  have hcomm' : ∀ a ∈ layerCent Y r, ∀ b ∈ K, a * b = b * a :=
    fun a ha b hb => (hcomm b hb a ha).symm
  have hKle : K ≤ I := hK.1.trans inf_le_left
  have hdvd : ctrQ (layerCent Y r) * ctrQ K ∣ ctrQ I :=
    m6e8_ctrQ_mul_dvd hJI hKle hcomm'
  have hJord : ctrQ (layerCent Y r) = 25920 := ctrQ_of_psp4 d.quasi d.omega5
  have hIord : ctrQ I = 6065280 := ctrQ_of_l43 hI.isQuasisimple hI6
  have hdvd' : ctrQ K ∣ 234 := by
    rw [hJord, hIord] at hdvd
    rw [show 6065280 = 25920 * 234 by norm_num] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hKq := hK.isQuasisimple
  exact (m6e8_not_simple_dvd_234 (Q := ↥K ⧸ Subgroup.center ↥K) hKq.2.1 hKq.2.2) hdvd'

private theorem m6e8_layerCent_of_unique {J H : Subgroup G} (hJH : IsComponentIn J H)
    (huniq : ∀ K : Subgroup G, IsComponentIn K H → K = J) :
    CFSG.inSubgroup CFSG.layer H = J := by
  have hJ' : CFSG.IsComponent (J.subgroupOf H) := hJH.2
  have hset : {K : Subgroup ↥H | CFSG.IsComponent K} = {J.subgroupOf H} := by
    ext K'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK'
      let K : Subgroup G := K'.map H.subtype
      have hKH : K ≤ H := Subgroup.map_subtype_le K'
      have hsub : K.subgroupOf H = K' :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective K'
      have hKi : IsComponentIn K H := ⟨hKH, by rw [hsub]; exact hK'⟩
      have hKJ : K = J := huniq K hKi
      rw [← hsub, hKJ]
    · rintro rfl
      exact hJ'
  unfold CFSG.inSubgroup
  rw [CFSG.layer.eq_sSup, hset, sSup_singleton]
  exact Subgroup.map_subgroupOf_eq_of_le hJH.1

theorem m6e8_layerCent_eq {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} {r : G}
    (d : M6E8Datum t L y X Y T r) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({r} : Set G))) (hJI : layerCent Y r ≤ I)
    (hI6 : IsOmega6Plus I) : layerCent I y = layerCent Y r := by
  have hJcomp : IsComponentIn (layerCent Y r) (I ⊓ centralizer ({y} : Set G)) :=
    m6e8_J_component d hI hJI
  have huniq : ∀ K : Subgroup G, IsComponentIn K (I ⊓ centralizer ({y} : Set G)) →
      K = layerCent Y r :=
    fun K hK => m6e8_comp_unique d hI hJI hI6 hJcomp hK
  show CFSG.inSubgroup CFSG.layer (I ⊓ centralizer ({y} : Set G)) = layerCent Y r
  exact m6e8_layerCent_of_unique hJcomp huniq

end CFSG.OddStandard.SmallF3.Omega
