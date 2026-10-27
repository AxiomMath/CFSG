module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Facts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem m6e8_card_zpowers_sup {y r : G} (hy : orderOf y = 2) (hr : orderOf r = 2)
    (hcomm : y * r = r * y) (hne : r ∉ Subgroup.zpowers y) :
    Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers r) = 4 := by
  have hnorm : Subgroup.zpowers r ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers y : Set G))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm n).eq
  have hdisj : Disjoint (Subgroup.zpowers y) (Subgroup.zpowers r) := by
    rw [disjoint_iff]
    set I := Subgroup.zpowers y ⊓ Subgroup.zpowers r with hI
    have hdvd : Nat.card I ∣ 2 := by
      rw [← hr, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq I h
    · exfalso
      apply hne
      have h1 : I = Subgroup.zpowers r :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hr])
      have h2 : Subgroup.zpowers r ≤ Subgroup.zpowers y := h1 ▸ inf_le_left
      exact h2 (Subgroup.mem_zpowers r)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, hy, hr]

theorem m6e8_index (hF2 : Asc82AutCentOmega5)
    {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} {r : G}
    (d : M6E8Datum t L y X Y T r)
    (hnorm : ∀ c ∈ centralizer ({r} : Set G), c ∈ normalizer (layerCent Y r : Set G)) :
    ∃ K : Subgroup G, K ≤ T ⊓ centralizer ({r} : Set G) ∧ y ∈ K ∧ r ∈ K ∧
      K.relIndex (T ⊓ centralizer ({r} : Set G)) = 2 ∧
      Nat.card ↥(K ⊓ (T ⊓ centralizer ({y} : Set G))) = 4 := by
  classical
  have hXq : IsQuasisimple ↥X := by
    obtain ⟨x, -, hXc⟩ := d.hXC
    exact hXc.isQuasisimple
  have hyC : y ∈ T ⊓ centralizer ({r} : Set G) :=
    ⟨d.hyT, Subgroup.mem_centralizer_singleton_iff.mpr d.comm_yr⟩
  have hrC : r ∈ T ⊓ centralizer ({r} : Set G) :=
    ⟨d.mem_R.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hKRle : T ⊓ centralizer ({y} : Set G) ≤ T ⊓ centralizer ({r} : Set G) := by
    intro z hz
    exact ⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr (d.toM6E8Ctx.R_comm hz d.mem_R)⟩
  have hKR : T ⊓ centralizer ({r} : Set G) ⊓ centralizer (layerCent Y r : Set G) ⊓
      (T ⊓ centralizer ({y} : Set G)) = Subgroup.zpowers y ⊔ Subgroup.zpowers r := by
    apply le_antisymm
    · intro z hz
      exact d.cent_le ⟨hz.2, hz.1.2⟩
    · refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr ⟨⟨hyC, d.y_mem_centralizer_J⟩, d.toM6E8Ctx.y_mem_R⟩
      · exact Subgroup.zpowers_le.mpr ⟨⟨hrC, d.r_mem_centralizer_J⟩, d.mem_R⟩
  have hcard4 : Nat.card ↥(T ⊓ centralizer ({r} : Set G) ⊓ centralizer (layerCent Y r : Set G) ⊓
      (T ⊓ centralizer ({y} : Set G))) = 4 := by
    rw [hKR]
    exact m6e8_card_zpowers_sup d.hy d.orderOf_r d.comm_yr d.not_mem
  have hCp : IsPGroup 2 ↥(T ⊓ centralizer ({r} : Set G)) := d.isPGroup_T.to_le inf_le_left
  have hCle : T ⊓ centralizer ({r} : Set G) ≤
      normalizer (layerCent Y r : Set G) ⊓ centralizer (X : Set G) :=
    fun c hc => ⟨hnorm c hc.2, d.hT.1 hc.1⟩
  have hle2 := hF2 G X (layerCent Y r) (T ⊓ centralizer ({r} : Set G)) hXq d.quasi d.hX29
    d.omega5 d.xj hCp hCle
  have hne1 : (centralizer (layerCent Y r : Set G)).relIndex
      (T ⊓ centralizer ({r} : Set G)) ≠ 1 := by
    intro h1
    have hCJ : T ⊓ centralizer ({r} : Set G) ≤ centralizer (layerCent Y r : Set G) :=
      Subgroup.relIndex_eq_one.mp h1
    have hRle : T ⊓ centralizer ({y} : Set G) ≤
        T ⊓ centralizer ({r} : Set G) ⊓ centralizer (layerCent Y r : Set G) :=
      fun z hz => ⟨hKRle hz, hCJ (hKRle hz)⟩
    have h8 : Nat.card ↥(T ⊓ centralizer ({r} : Set G) ⊓ centralizer (layerCent Y r : Set G) ⊓
        (T ⊓ centralizer ({y} : Set G))) = 8 := by
      rw [inf_eq_right.mpr hRle]
      exact d.h8
    omega
  have hne0 : (centralizer (layerCent Y r : Set G)).relIndex
      (T ⊓ centralizer ({r} : Set G)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨T ⊓ centralizer ({r} : Set G) ⊓ centralizer (layerCent Y r : Set G), inf_le_left,
    ⟨hyC, d.y_mem_centralizer_J⟩, ⟨hrC, d.r_mem_centralizer_J⟩, ?_, hcard4⟩
  rw [Subgroup.inf_relIndex_left]
  omega

end CFSG.OddStandard.SmallF3.Omega
