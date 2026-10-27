module

public import CFSG.GH74.AS16.Defs
public import CFSG.Quasithin.Background.CharTwoLocal
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CT

variable {G : Type} [Group G]

theorem normalizer_zpowers_eq_centralizer {z : G} (hz : orderOf z = 2) :
    normalizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  ext g
  constructor
  · intro h
    rw [mem_centralizer_singleton_iff]
    have h1 : g * z * g⁻¹ ∈ zpowers z := (mem_normalizer_iff.mp h z).mp (mem_zpowers z)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hk' : g * z * g⁻¹ = z := by
      rcases zpow_eq_one_or_self hz2 k with h2 | h2
      · exfalso
        rw [h2] at hk
        have h3 : g * z * g⁻¹ = 1 := hk.symm
        apply hz1
        simpa using h3
      · rw [h2] at hk
        exact hk.symm
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hk']
  · intro h
    have hg : g ∈ centralizer ((zpowers z : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      have hcomm : Commute z g := (mem_centralizer_singleton_iff.mp h).symm
      exact ((hcomm.zpow_left k).eq)
    exact (Subgroup.centralizer_le_normalizer _) hg

theorem exists_involution_mem_center [Finite G] {T Q : Subgroup G} (hT : IsPGroup 2 T)
    (hQT : Q ≤ T) (hQn : T ≤ normalizer (Q : Set G)) (hQ : Q ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ Q ∧ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnorm : (Q.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hQn
  have hne : Q.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have h1 : (⟨q, hQT hq⟩ : T) ∈ Q.subgroupOf T := hq
    rw [hbot, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  have hS := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxS⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT) x
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp only [pow_zero, orderOf_eq_one_iff] at hj
    exact hx1' hj
  have h2dvd : 2 ∣ orderOf x := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hord0 : orderOf x ≠ 0 := by
    rw [hj]
    positivity
  have hz'ord : orderOf (x ^ (orderOf x / 2)) = 2 := orderOf_pow_orderOf_div hord0 h2dvd
  have hz'S : x ^ (orderOf x / 2) ∈ Q.subgroupOf T ⊓ center T := Subgroup.pow_mem _ hxS _
  refine ⟨((x ^ (orderOf x / 2) : T) : G), ?_, hz'S.1, (x ^ (orderOf x / 2)).2, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hz'ord
  · intro t ht
    have := (Subgroup.mem_center_iff.mp hz'S.2) ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem exists_involution_not_charTwo_of_local [Finite G] (T : Sylow 2 G) {H P : Subgroup G}
    (hPne : P ≠ ⊥) (hP2 : IsPGroup 2 P) (hHP : H = normalizer (P : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hHnot : ¬ CharTwo H) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ (T : Subgroup G) ∧ (∀ t ∈ (T : Subgroup G), t * z = z * t) ∧
      ¬ CharTwo (centralizer ({z} : Set G)) := by
  have hQT : CFSG.Open.pCoreOf 2 H ≤ (T : Subgroup G) := pCoreOf_two_le_sylow H T hTH
  have hPQ : P ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_witness_le_pCoreOf P H hP2 hHP
  have hQne : CFSG.Open.pCoreOf 2 H ≠ ⊥ := fun h => hPne (le_bot_iff.mp (h ▸ hPQ))
  have hHQ : H ≤ normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hTQ : (T : Subgroup G) ≤ normalizer (CFSG.Open.pCoreOf 2 H : Set G) := hTH.trans hHQ
  obtain ⟨z, hz2, hzQ, hzT, hzc⟩ := exists_involution_mem_center T.isPGroup' hQT hTQ hQne
  refine ⟨z, hz2, hzT, hzc, ?_⟩
  intro hC
  have h1 : CharTwo (normalizer (zpowers z : Set G)) := by
    rw [normalizer_zpowers_eq_centralizer hz2]
    exact hC
  have h2 : CharTwo (normalizer (CFSG.Open.pCoreOf 2 H : Set G)) :=
    charTwo_normalizer_of_le (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
      (zpowers_le.mpr hzQ) h1
  exact hHnot (centralizer_pCoreOf_le_of_sylow (p := 2) hHQ T.isPGroup' hTH
    (not_dvd_index_subgroupOf_of_sylow T (hTH.trans hHQ)) h2)

theorem exists_involution_not_charTwo [Finite G]
    (hnot : ¬ Assembly.Quasithin.quasithinEvenCharacteristic G) :
    ∃ (T : Sylow 2 G) (z : G), orderOf z = 2 ∧ z ∈ (T : Subgroup G) ∧
      (∀ t ∈ (T : Subgroup G), t * z = z * t) ∧ ¬ CharTwo (centralizer ({z} : Set G)) := by
  have hex : ∃ H : Subgroup G, Assembly.IsTwoLocal H ∧
      (∃ S : Sylow 2 G, (S : Subgroup G) ≤ H) ∧ ¬ CharTwo H := by
    by_contra hcon
    apply hnot
    intro H hH hS
    by_contra hHn
    exact hcon ⟨H, hH, hS, hHn⟩
  obtain ⟨H, ⟨P, hPne, hP2, hHP⟩, ⟨T, hTH⟩, hHnot⟩ := hex
  obtain ⟨z, hz⟩ := exists_involution_not_charTwo_of_local T hPne hP2 hHP hTH hHnot
  exact ⟨T, z, hz⟩

theorem exists_component_of_not_charTwo [Finite G] {z : G}
    (hE1 : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥)
    (hC : ¬ CharTwo (centralizer ({z} : Set G))) :
    ∃ L : Subgroup G, GLS.IsCompIn (centralizer ({z} : Set G)) L := by
  by_contra hno
  apply hC
  have hlayer : layer ↥(centralizer ({z} : Set G)) = ⊥ := by
    simp only [CFSG.layer.eq_sSup]
    have hempty : {K : Subgroup ↥(centralizer ({z} : Set G)) | IsComponent K} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro K hK
      apply hno
      refine ⟨K.map (centralizer ({z} : Set G)).subtype, ?_, ?_⟩
      · rintro _ ⟨y, _, rfl⟩
        exact y.2
      · have e : (K.map (centralizer ({z} : Set G)).subtype).subgroupOf (centralizer ({z} : Set G))
            = K := Subgroup.comap_map_eq_self_of_injective (centralizer ({z} : Set G)).subtype_injective K
        rw [e]
        exact hK
    rw [hempty, sSup_empty]
  have hchar : IsCharacteristicP 2 ↥(centralizer ({z} : Set G)) :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2 hE1 hlayer
  rw [charTwo_iff_internal]
  have h := hchar
  unfold IsCharacteristicP at h
  assumption

theorem exists_pair [Finite G]
    (hE1 : ∀ x : G, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥)
    (hnot : ¬ Assembly.Quasithin.quasithinEvenCharacteristic G) :
    ∃ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L := by
  obtain ⟨T, z, hz2, hzT, hzc, hC⟩ := exists_involution_not_charTwo hnot
  obtain ⟨L, hL⟩ := exists_component_of_not_charTwo (hE1 z hz2) hC
  exact ⟨T, z, L, ⟨hz2, hzT, hzc, hL⟩⟩

end CFSG.GH74.AS16
