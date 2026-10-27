module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private lemma orbit_card_and_subset {N T : Subgroup G} {t : G} [MulAction ↥N G]
    (hsmul : ∀ n : ↥N, n • t = (n : G) * t * (n : G)⁻¹)
    (hstab : MulAction.stabilizer ↥N t = (centralizer ({t} : Set G)).subgroupOf N)
    (hconj : ∀ n : ↥N, (n : G) * t * (n : G)⁻¹ ∈ T) (ht1 : t ≠ 1) :
    (MulAction.orbit ↥N t).ncard = ((centralizer ({t} : Set G)).subgroupOf N).index ∧
      ∀ y ∈ MulAction.orbit ↥N t, y ∈ T ∧ y ≠ 1 := by
  constructor
  · rw [← MulAction.index_stabilizer, hstab]
  · intro y hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [hsmul n]
      exact hconj n
    · intro h1
      have h1' : (n : G) * t * (n : G)⁻¹ = 1 := by rwa [hsmul n] at h1
      have h2 : (n : G) * t = (n : G) * 1 := by
        rw [← mul_inv_eq_iff_eq_mul]
        simpa using h1'
      exact ht1 (mul_left_cancel h2)

theorem relIndex_normalizer_le_card_sub_one {T : Subgroup G} {t : G} (htT : t ∈ T)
    (ht1 : t ≠ 1) (hC : centralizer ({t} : Set G) ≤ T) :
    T.relIndex (normalizer (T : Set G)) ≤ Nat.card T - 1 := by
  let N : Subgroup G := normalizer (T : Set G)
  let f : ↥N →* MulAut G := MulAut.conj.comp N.subtype
  letI : MulAction ↥N G := MulAction.compHom G f
  have hstab : MulAction.stabilizer ↥N t = (centralizer ({t} : Set G)).subgroupOf N := by
    ext n
    show (MulAut.conj (n : G)) t = t ↔ (n : G) ∈ centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  obtain ⟨horb, hsub⟩ := orbit_card_and_subset (fun n => rfl) hstab
    (fun n => (n.2 t).mp htT) ht1
  have hcard : ((T : Set G) \ {1}).ncard = Nat.card T - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    rfl
  have hle1 : ((centralizer ({t} : Set G)).subgroupOf N).index ≤ Nat.card T - 1 := by
    rw [← horb, ← hcard]
    exact Set.ncard_le_ncard hsub
  have hle2 : (T.subgroupOf N).index ≤ ((centralizer ({t} : Set G)).subgroupOf N).index := by
    have hle : (centralizer ({t} : Set G)).subgroupOf N ≤ T.subgroupOf N :=
      Subgroup.subgroupOf_mono N hC
    have hdvd : (T.subgroupOf N).index ∣ ((centralizer ({t} : Set G)).subgroupOf N).index :=
      Subgroup.index_dvd_of_le hle
    have hpos : 0 < ((centralizer ({t} : Set G)).subgroupOf N).index :=
      Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    exact Nat.le_of_dvd hpos hdvd
  calc T.relIndex N = (T.subgroupOf N).index := rfl
    _ ≤ ((centralizer ({t} : Set G)).subgroupOf N).index := hle2
    _ ≤ Nat.card T - 1 := hle1

theorem exists_conj_eq_of_relIndex_eq {T : Subgroup G} {t : G} (htT : t ∈ T)
    (ht1 : t ≠ 1) (hC : centralizer ({t} : Set G) ≤ T)
    (hrel : T.relIndex (normalizer (T : Set G)) = Nat.card T - 1) {y : G} (hyT : y ∈ T)
    (hy1 : y ≠ 1) : ∃ n ∈ normalizer (T : Set G), n * t * n⁻¹ = y := by
  let N : Subgroup G := normalizer (T : Set G)
  let f : ↥N →* MulAut G := MulAut.conj.comp N.subtype
  letI : MulAction ↥N G := MulAction.compHom G f
  have hstab : MulAction.stabilizer ↥N t = (centralizer ({t} : Set G)).subgroupOf N := by
    ext n
    show (MulAut.conj (n : G)) t = t ↔ (n : G) ∈ centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  obtain ⟨horb, hsub⟩ := orbit_card_and_subset (fun n => rfl) hstab
    (fun n => (n.2 t).mp htT) ht1
  have hcard : ((T : Set G) \ {1}).ncard = Nat.card T - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    rfl
  have hle2 : (T.subgroupOf N).index ≤ ((centralizer ({t} : Set G)).subgroupOf N).index := by
    have hle : (centralizer ({t} : Set G)).subgroupOf N ≤ T.subgroupOf N :=
      Subgroup.subgroupOf_mono N hC
    have hdvd : (T.subgroupOf N).index ∣ ((centralizer ({t} : Set G)).subgroupOf N).index :=
      Subgroup.index_dvd_of_le hle
    have hpos : 0 < ((centralizer ({t} : Set G)).subgroupOf N).index :=
      Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    exact Nat.le_of_dvd hpos hdvd
  have hrelN : (T.subgroupOf N).index = Nat.card T - 1 := by
    rw [← hrel]
    rfl
  have horb' : (MulAction.orbit ↥N t).ncard = Nat.card T - 1 := by
    apply le_antisymm
    · rw [← hcard]
      exact Set.ncard_le_ncard hsub
    · rw [horb]
      calc Nat.card T - 1 = (T.subgroupOf N).index := hrelN.symm
        _ ≤ ((centralizer ({t} : Set G)).subgroupOf N).index := hle2
  have hset : MulAction.orbit ↥N t = (T : Set G) \ {1} := by
    refine Set.eq_of_subset_of_ncard_le (s := MulAction.orbit ↥N t)
      (t := (T : Set G) \ {1}) hsub ?_
    rw [hcard, horb']
  have hy : y ∈ MulAction.orbit ↥N t := by
    rw [hset]
    exact ⟨hyT, by simpa using hy1⟩
  rw [MulAction.mem_orbit_iff] at hy
  obtain ⟨n, hn⟩ := hy
  exact ⟨(n : G), n.2, hn⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
