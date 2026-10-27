module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem ds_l515b_mem_centerIn_commute {I : Subgroup G} {d : G} (hd : d ∈ centerIn I) :
    ∀ y ∈ I, d * y = y * d := by
  rw [centerIn, Subgroup.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  intro y hy
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)).symm

private theorem ds_l515b_card_twoRes_conj (I : Subgroup G) {l : G} (hl : l ∈ I) (w : G) :
    Nat.card ↥(twoRes (I ⊓ centralizer ({l * w * l⁻¹} : Set G))) =
      Nat.card ↥(twoRes (I ⊓ centralizer ({w} : Set G))) := by
  have hI : CFSG.conjugate I l⁻¹ = I :=
    (sec5b513_conjugate_eq_iff).mpr (Subgroup.le_normalizer (inv_mem hl))
  have hC : centralizer ({l * w * l⁻¹} : Set G) =
      CFSG.conjugate (centralizer ({w} : Set G)) l⁻¹ := by
    simpa using (sec5b517_centralizer_conj w l⁻¹)
  calc Nat.card ↥(twoRes (I ⊓ centralizer ({l * w * l⁻¹} : Set G)))
      = Nat.card ↥(twoRes (I ⊓ CFSG.conjugate (centralizer ({w} : Set G)) l⁻¹)) := by
        rw [hC]
    _ = Nat.card ↥(twoRes (CFSG.conjugate I l⁻¹ ⊓
          CFSG.conjugate (centralizer ({w} : Set G)) l⁻¹)) := by
        rw [hI]
    _ = Nat.card ↥(twoRes (CFSG.conjugate (I ⊓ centralizer ({w} : Set G)) l⁻¹)) := by
        rw [← sec5b517_conjugate_inf]
    _ = Nat.card ↥(CFSG.conjugate (twoRes (I ⊓ centralizer ({w} : Set G))) l⁻¹) := by
        rw [sec5b513_twoRes_conjugate]
    _ = Nat.card ↥(twoRes (I ⊓ centralizer ({w} : Set G))) := by
        rw [CFSG.conjugate]
        simp only [inv_inv]
        exact Subgroup.card_map_of_injective (MulAut.conj l).injective

private theorem ds_l515b_inf_centralizer_mul_of_mem_centerIn {I : Subgroup G} {d : G}
    (hd : d ∈ centerIn I) (w : G) :
    I ⊓ centralizer ({d * w} : Set G) = I ⊓ centralizer ({w} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxI, hx⟩
    have hdx : d * x = x * d := ds_l515b_mem_centerIn_commute hd x hxI
    refine ⟨hxI, ?_⟩
    have key : d * (x * w) = d * (w * x) := by
      calc d * (x * w) = (d * x) * w := by group
        _ = (x * d) * w := by rw [hdx]
        _ = x * (d * w) := by group
        _ = (d * w) * x := hx
        _ = d * (w * x) := by group
    exact mul_left_cancel key
  · rintro ⟨hxI, hx⟩
    have hdx : d * x = x * d := ds_l515b_mem_centerIn_commute hd x hxI
    refine ⟨hxI, ?_⟩
    calc x * (d * w) = (x * d) * w := by group
      _ = (d * x) * w := by rw [hdx]
      _ = d * (x * w) := by group
      _ = d * (w * x) := by rw [hx]
      _ = (d * w) * x := by group

theorem sec5_pair_eq_twoRes (tab : Asc82Tab5) (h512K : Asc82Lemma512K) {d : G} {I S' : Subgroup G}
    {z' r' : G} {B' A' : Subgroup G} (hs : Sec5Setting G d I) (hcent : centerIn I = zpowers d)
    (hR : Sec5RCtx G d I S' z' r' B' A') {z : G} (hz2 : orderOf z = 2) (hzd : z ≠ d)
    {K₁ K₂ : Subgroup G} (hp : Sec5Pair K₁ K₂ z) (hle : K₁ ⊔ K₂ ≤ I) :
    K₁ ⊔ K₂ = twoRes (centralizer ({z} : Set G) ⊓ I) ∧ ∃ g ∈ I, z = g⁻¹ * z' * g := by
  have hd : d ∈ centerIn I := by rw [hcent]; exact Subgroup.mem_zpowers d
  have hd2 : orderOf d = 2 := hs.involution
  have hOm : IsOm6Z2 I := ⟨hs.component.isQuasisimple, hs.twoU43⟩
  have hzI : z ∈ I := hle (Subgroup.mem_sup_left hp.z_mem₁)
  obtain ⟨K₁', K₂', hK⟩ := h512K G d I S' z' r' B' A' hR hcent
  have hcard' : Nat.card ↥(twoRes (I ⊓ centralizer ({z'} : Set G))) = 288 := by
    rw [← hK.prod]
    exact (Sec5Pair.of_kctx hK).card_sup
  have hclass := tab.inv_classes G I hOm d hd hd2 z' hR.pocket z hzI hz2 hzd
  have hcardz : Nat.card ↥(twoRes (I ⊓ centralizer ({z} : Set G))) = 288 := by
    rcases hclass with ⟨l, hl, hzl⟩ | ⟨l, hl, hzl⟩
    · rw [hzl, ds_l515b_card_twoRes_conj I hl z']
      exact hcard'
    · have hld : l * d = d * l := (ds_l515b_mem_centerIn_commute hd l hl).symm
      have hzeq : z = d * (l * z' * l⁻¹) := by
        rw [hzl]
        calc l * (d * z') * l⁻¹ = (l * d) * z' * l⁻¹ := by group
          _ = (d * l) * z' * l⁻¹ := by rw [hld]
          _ = d * (l * z' * l⁻¹) := by group
      rw [hzeq, ds_l515b_inf_centralizer_mul_of_mem_centerIn hd (l * z' * l⁻¹),
        ds_l515b_card_twoRes_conj I hl z']
      exact hcard'
  have hM : K₁ ⊔ K₂ = twoRes (centralizer ({z} : Set G) ⊓ I) := by
    refine hp.eq_twoRes (le_inf hp.le_centralizer hle) ?_
    rw [inf_comm]
    exact hcardz
  refine ⟨hM, ?_⟩
  rcases hclass with ⟨l, hl, hzl⟩ | ⟨l, hl, hzl⟩
  · exact ⟨l⁻¹, inv_mem hl, by simpa using hzl⟩
  · exfalso
    have hld : l * d = d * l := (ds_l515b_mem_centerIn_commute hd l hl).symm
    have hzeq : z = d * (l * z' * l⁻¹) := by
      rw [hzl]
      calc l * (d * z') * l⁻¹ = (l * d) * z' * l⁻¹ := by group
        _ = (d * l) * z' * l⁻¹ := by rw [hld]
        _ = d * (l * z' * l⁻¹) := by group
    have hM' : K₁ ⊔ K₂ = twoRes (I ⊓ centralizer ({z} : Set G)) :=
      hM.trans (congrArg twoRes (inf_comm _ _))
    have hzI4 : IsI4PlusIn I z := ⟨hz2, K₁, (hp.pocket (X := I) hM').1⟩
    have hz''I4 : IsI4PlusIn I (l * z' * l⁻¹) := IsI4PlusIn.conj_of_mem hR.pocket hl
    exact (tab.tz_not_pocket G I hOm d hd hd2 (l * z' * l⁻¹) hz''I4) (hzeq ▸ hzI4)

end CFSG.OddStandard.SmallF3.Omega
