module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem leafSylow2Cent
    : LeafSylow2Cent := by
  intro G _ _ Y z hz hzY
  have NL : ∀ (R Q : Subgroup G), IsPGroup 2 R → Q ≤ R → Q ≠ R →
      ∃ n : G, n ∈ R ∧ n ∈ Subgroup.normalizer (Q : Set G) ∧ n ∉ Q := by
    intro R Q hR hQR hne
    haveI : Group.IsNilpotent R := hR.isNilpotent
    have hlt : Q.subgroupOf R < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hQR (Subgroup.subgroupOf_eq_top.mp h))
    obtain ⟨n, hnN, hnQ⟩ :=
      SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (Q.subgroupOf R) hlt)
    have hnN' : (n : G) ∈ Subgroup.normalizer (Q : Set G) := by
      have h : n ∈ (Subgroup.normalizer (Q : Set G)).subgroupOf R := by
        rw [Subgroup.subgroupOf_normalizer_eq hQR]
        exact hnN
      exact Subgroup.mem_subgroupOf.mp h
    exact ⟨(n : G), n.2, hnN', fun h => hnQ (Subgroup.mem_subgroupOf.mpr h)⟩
  have Cz : ∀ Q₀ : Subgroup G, z ∈ Q₀ →
      (∀ q ∈ Q₀, (∀ q' ∈ Q₀, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers z) →
      ∀ n ∈ Subgroup.normalizer (Q₀ : Set G), n ∈ Subgroup.centralizer {z} := by
    intro Q₀ hzQ hZ n hn
    have hzcomm : ∀ q' ∈ Q₀, z * q' = q' * z := (hZ z hzQ).mpr (Subgroup.mem_zpowers z)
    have hx : n * z * n⁻¹ ∈ Q₀ := (Subgroup.mem_normalizer_iff.mp hn z).mp hzQ
    have hninv : n⁻¹ ∈ Subgroup.normalizer (Q₀ : Set G) :=
      (Subgroup.normalizer (Q₀ : Set G)).inv_mem hn
    have hxc : ∀ q' ∈ Q₀, n * z * n⁻¹ * q' = q' * (n * z * n⁻¹) := by
      intro q' hq'
      have hq'' : n⁻¹ * q' * n ∈ Q₀ := by
        have h := (Subgroup.mem_normalizer_iff.mp hninv q').mp hq'
        rwa [inv_inv] at h
      calc n * z * n⁻¹ * q' = n * (z * (n⁻¹ * q' * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * q' * n) * z) * n⁻¹ := by rw [hzcomm _ hq'']
        _ = q' * (n * z * n⁻¹) := by group
    have hxZ : n * z * n⁻¹ ∈ Subgroup.zpowers z := (hZ _ hx).mp hxc
    have hxz : n * z * n⁻¹ = z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
      have hmod := zpow_mod_orderOf z k
      rw [hz, hk] at hmod
      push_cast at hmod
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        rw [h0, zpow_zero] at hmod
        have hz1 : z = 1 := by simpa using hmod.symm
        have h2 := hz
        rw [hz1, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      · rw [h1, zpow_one] at hmod
        exact hmod.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxz)
  have hb : ∀ Q₀ : Subgroup G, Q₀ ≤ Y → IsPGroup 2 Q₀ → z ∈ Q₀ →
      (∀ q ∈ Q₀, (∀ q' ∈ Q₀, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers z) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y ⊓ Subgroup.centralizer {z} → Q₀ ≤ R → R = Q₀) →
      ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Q₀ ≤ R → R = Q₀ := by
    intro Q₀ _ _ hzQ hZ hmax R hR hRY hQR
    by_contra hne
    obtain ⟨n, hnR, hnN, hnQ⟩ := NL R Q₀ hR hQR (Ne.symm hne)
    have hN : Subgroup.normalizer (Q₀ : Set G) ⊓ R ≤ Y ⊓ Subgroup.centralizer {z} :=
      fun g hg => ⟨hRY hg.2, Cz Q₀ hzQ hZ g hg.1⟩
    have hNeq := hmax (Subgroup.normalizer (Q₀ : Set G) ⊓ R) hR.to_inf_right hN
      (le_inf Subgroup.le_normalizer hQR)
    have hmem : n ∈ Subgroup.normalizer (Q₀ : Set G) ⊓ R := ⟨hnN, hnR⟩
    rw [hNeq] at hmem
    exact hnQ hmem
  refine ⟨fun hyp => ?_, hb⟩
  have hz0Y : Subgroup.zpowers z ≤ Y := Subgroup.zpowers_le.mpr hzY
  have hz0C : ∀ q ∈ Subgroup.zpowers z,
      (∀ q' ∈ Subgroup.zpowers z, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers z := by
    intro q hq
    refine ⟨fun _ => hq, fun _ q' hq' => ?_⟩
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq'
    exact zpow_mul_comm z a b
  have hz0max : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ Y ⊓ Subgroup.centralizer {z} →
      Subgroup.zpowers z ≤ R' → R' = Subgroup.zpowers z := by
    intro R' hR' hR'le hle
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, hz]; exact hyp R' hR' hR'le)).symm
  have hz0 := hb (Subgroup.zpowers z) hz0Y
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])) (Subgroup.mem_zpowers z)
    hz0C hz0max
  have hz' : orderOf (⟨z, hzY⟩ : Y) = 2 := (Subgroup.orderOf_mk z hzY).trans hz
  have hT : IsPGroup 2 (Subgroup.zpowers (⟨z, hzY⟩ : Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  obtain ⟨P, hTP⟩ := IsPGroup.exists_le_sylow hT
  have hzP : (⟨z, hzY⟩ : Y) ∈ (P : Subgroup Y) := hTP (Subgroup.mem_zpowers _)
  have hR₀ := hz0 ((P : Subgroup Y).map Y.subtype) (P.isPGroup'.map Y.subtype)
    (Subgroup.map_subtype_le _) (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem Y.subtype hzP))
  have hPcard : Nat.card (P : Subgroup Y) = 2 := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, hR₀, Nat.card_zpowers, hz]
  intro R hR hRY
  have hS : IsPGroup 2 (R.subgroupOf Y) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hS
  calc Nat.card R = Nat.card (R.subgroupOf Y) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv).symm
    _ ≤ Nat.card (Q : Subgroup Y) := Subgroup.card_le_of_le hQ
    _ = Nat.card (P : Subgroup Y) :=
        (Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity P).symm
    _ = 2 := hPcard

end CFSG.GH74.QTGen4.Recog.G23.P7
