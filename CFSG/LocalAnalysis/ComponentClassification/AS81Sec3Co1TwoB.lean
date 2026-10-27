module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3ZNotPoint
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoB
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.RankTwoExceptional CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G]

namespace Sec3

private theorem sec3B_le_rankTwoX {A A₁ : Subgroup G} (h : A₁ ≤ A) (x : G) :
    sec3B A₁ x ≤ rankTwoX A := by
  unfold sec3B
  have hle : normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
      Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) ≤
      (normalClosure (A : Set G)).subgroupOf (centralizer ({x} : Set G)) :=
    have : ((normalClosure (A : Set G)).subgroupOf (centralizer ({x} : Set G))).Normal :=
      normalClosure_normal.subgroupOf _
    normalClosure_le_normal fun c hc => subset_normalClosure (h hc)
  refine (map_mono hle).trans ?_
  rw [subgroupOf_map_subtype]
  exact inf_le_left

theorem centralizer_le_normalizer_of_standard [Finite G] {A : Subgroup G}
    (hA : Open.standardComponentIsStandard A) {r : G} (hr : r ∈ centralizer (A : Set G))
    (hr2 : orderOf r = 2) : centralizer ({r} : Set G) ≤ normalizer (A : Set G) :=
  fun _ hy => CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute hA hr hr2
    (mem_centralizer_singleton_iff.1 hy)

end Sec3


theorem Sec3Model.exists_long_of_mem {A A₁ E F : Subgroup G} {x : G} {K : Type} [Field K]
    [CharP K 2] {f : ↥(adjointGroup .G2 K) →* G} (hM : Sec3Model G A A₁ E F x K f) {z : G}
    (hz : z ∈ E ⊓ A) (hz1 : z ≠ 1) :
    ∃ g : ↥(adjointGroup .G2 K), f g = z ∧ G2Conj (g : ModGL .G2 K) (pinnedX .G2 K g2c 1) := by
  rw [← hM.E_eq] at hz
  obtain ⟨g, hg, rfl⟩ := mem_map.1 hz
  refine ⟨g, rfl, ?_⟩
  obtain ⟨y, w, hyw⟩ := mem_g2BCGroup.1 (mem_subgroupOf.1 hg)
  rw [hyw]
  refine g2Conj_bc ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨rfl, rfl⟩ := hcon
  exact hz1 (by rw [show g = 1 from Subtype.ext (hyw.trans g2N_zero), map_one])

namespace Sec3

theorem co1TwoBData_of [Finite G] {A A₁ R : Subgroup G} {g : G} {E F Zs P T Q B₀ : Subgroup G}
    {x z y : G} (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) (hz1 : z ≠ 1)
    (hzX : z ∈ rankTwoX A) : HoltFree.Co1TwoBData ↥(rankTwoX A) ⟨z, hzX⟩ := by
  have hS := hSz.setting
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hzZ : z ∈ sec2Z A₁ E F := hSz.Zs_eq ▸ hSz.z_mem
  have hzE : z ∈ E := by
    have h2 : z ∈ centerIn (E ⊔ F) := hzZ.2
    rw [← hS.frame.inf_eq_center] at h2
    exact h2.1
  obtain ⟨K, _, _, _, -, f, hM⟩ := exists_sec3Model hS
  obtain ⟨g₀, hg₀, hlong⟩ := hM.exists_long_of_mem (mem_inf.2 ⟨hzE, hS.le hzZ.1⟩) hz1
  have hfX : ∀ c, f c ∈ rankTwoX A := fun c => hAX (hM.range_eq ▸ ⟨c, rfl⟩)
  refine ⟨A.subgroupOf (rankTwoX A), ?_, ⟨K, inferInstance, inferInstance,
    f.codRestrict (rankTwoX A) hfX, ?_, g₀, Subtype.ext hg₀, hlong⟩, ?_, ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv, hS.toSec3Pre.card_A]
    norm_num
  · have hA' : ∀ w : G, w ∈ f.range ↔ w ∈ A := fun w => by rw [hM.range_eq]
    ext c
    rw [mem_subgroupOf, ← hA', MonoidHom.mem_range, MonoidHom.mem_range]
    exact ⟨fun ⟨d, hd⟩ => ⟨d, congrArg Subtype.val hd⟩, fun ⟨d, hd⟩ => ⟨d, Subtype.ext hd⟩⟩
  ·
    intro r hr hr2 w hw
    have hrA : (r : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun a ha =>
      congrArg Subtype.val (mem_centralizer_iff.1 hr ⟨a, hAX ha⟩ ha)
    have hwN := centralizer_le_normalizer_of_standard hS.base.hyp.standard hrA
      ((Subgroup.orderOf_coe r).trans hr2)
      (mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hw)))
    exact mem_normalizer_iff.2 fun c => mem_normalizer_iff.1 hwN c
  ·
    have hRX : R ≤ rankTwoX A := hSz.R_le.trans (sec3B_le_rankTwoX hS.le x)
    have hR2 : 2 ∣ Nat.card R := by
      rcases hS.sylowR.isPGroup.card_eq_or_dvd with h1 | h2
      · have := hS.four_le
        omega
      · exact h2
    have hle : R.subgroupOf (rankTwoX A) ≤ centralizer ((A.subgroupOf (rankTwoX A) :
        Subgroup ↥(rankTwoX A)) : Set ↥(rankTwoX A)) := fun ρ hρ =>
      mem_centralizer_iff.2 fun a ha => Subtype.ext
        (mem_centralizer_iff.1 (hS.sylowR.le (mem_subgroupOf.1 hρ)) a (mem_subgroupOf.1 ha))
    refine even_iff_two_dvd.2 ((hR2.trans ?_).trans (card_dvd_of_le hle))
    rw [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv]

end Sec3

end CFSG.ComponentClassification.AS81
