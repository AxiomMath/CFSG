module

public import CFSG.LocalAnalysis.SectionRank.QTK.SectionLift
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.SectionRank.QTK

open Subgroup

theorem exists_two_subgroup_normalized {Y : Type*} [Group Y] [Finite Y]
    {R : Subgroup (Y ⧸ center Y)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ∃ R₂ : Subgroup Y, R₂ ≠ ⊥ ∧ IsPGroup 2 R₂ ∧ ∀ w : Y,
      (w : Y ⧸ center Y) ∈ normalizer (R : Set (Y ⧸ center Y)) →
        w ∈ normalizer (R₂ : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Y) with hπ
  set U := R.comap π with hU
  let f : U →* R := (π.comp U.subtype).codRestrict R fun u => u.2
  have hfs : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
    exact ⟨⟨y, hr⟩, rfl⟩
  have hker : f.ker ≤ center U := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hu' : π u = 1 := congrArg Subtype.val hu
    have huZ : (u : Y) ∈ center Y := (QuotientGroup.eq_one_iff _).mp hu'
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp huZ g)
  have : Group.IsNilpotent R := hR2.isNilpotent
  have : Group.IsNilpotent U := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨S⟩ : Nonempty (Sylow 2 U) := inferInstance
  have hSn : (S : Subgroup U).Normal := instNormalOfIsNilpotentOfFactPrime
  have : (S : Subgroup U).Characteristic := Sylow.characteristic_of_normal S hSn
  refine ⟨(S : Subgroup U).map U.subtype, ?_, S.isPGroup'.map _, fun w hw => ?_⟩
  · intro hbot
    have h2R : 2 ∣ Nat.card R := by
      rcases hR2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR
      · exact h
    have h2U : 2 ∣ Nat.card U := h2R.trans (Subgroup.card_dvd_of_surjective (f := f) hfs)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2U
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨S', hS'⟩ := hu2.exists_le_sylow
    have : Subsingleton (Sylow 2 U) := (Sylow.unique_of_normal S hSn).instSubsingleton
    have hSS : S' = S := Subsingleton.elim _ _
    have huS : u ∈ (S : Subgroup U) := hSS ▸ hS' (Subgroup.mem_zpowers u)
    have hu1 : (u : Y) ∈ (S : Subgroup U).map U.subtype := ⟨u, huS, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hu1
    have : u = 1 := Subtype.ext hu1
    rw [this, orderOf_one] at hu
    omega
  · have hwU : w ∈ normalizer (U : Set Y) := by
      rw [mem_normalizer_iff]
      intro u
      have h := (mem_normalizer_iff.mp hw) (π u)
      simp only [hU, Subgroup.mem_comap, map_mul, map_inv] at h ⊢
      exact h
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (S : Subgroup U) hwU

theorem isElemAbelian_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') {p : ℕ}
    {K : Subgroup G} (hK : CFSG.Open.IsElemAbelian p K) :
    CFSG.Open.IsElemAbelian p (K.map f) := CFSG.Open.IsElemAbelian.map hK _

variable {G : Type} [Group G] [Finite G]

theorem le_two_of_evenRank_le_two (he : CFSG.Open.evenRank G ≤ 2) {R : Subgroup G}
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hEN : E ≤ normalizer (R : Set G)) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ 2 := by
  have hk1 : k ≤ CFSG.Open.pRank p (normalizer (R : Set G)) := by
    refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨E, hEN, hE, hk⟩
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hk2 : CFSG.Open.pRank p (normalizer (R : Set G)) ≤ CFSG.Open.evenRank G := by
    refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨p, _, hp, hp2, ⟨R, hR, hR2, rfl⟩, rfl⟩
    obtain ⟨q, K, hq, -, -, rfl⟩ := hj
    refine csSup_le' fun i hi => ?_
    obtain ⟨F, -, -, hF⟩ := hi
    have h1 : i < q ^ i := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  omega

theorem pRank_normalizer_le_two_of_not_dvd (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥Y))
    {R : Subgroup (↥Y ⧸ center ↥Y)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    CFSG.Open.pRank r (normalizer (R : Set (↥Y ⧸ center ↥Y))) ≤ 2 := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEN, hEel, hEcard⟩ := hk
  obtain ⟨P, hPel, hPcard, hPmap⟩ := exists_lift hr hrZ hEel
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := exists_two_subgroup_normalized hR hR2
  have hPN : P ≤ normalizer (R₂ : Set ↥Y) := fun w hw => by
    have hwE : QuotientGroup.mk' (center ↥Y) w ∈ E := hPmap ▸ ⟨w, hw, rfl⟩
    exact hR₂N w (hEN hwE)
  have hP'N : P.map Y.subtype ≤ normalizer ((R₂.map Y.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map _)
  have hP'card : Nat.card (P.map Y.subtype) = r ^ k := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hPcard, hEcard]
  have hR₂' : R₂.map Y.subtype ≠ ⊥ := fun h =>
    hR₂ ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h)
  exact le_two_of_evenRank_le_two he hR₂' (hR₂2.map _) hr hr2 (isElemAbelian_map _ hPel) hP'N
    hP'card

end CFSG.SectionRank.QTK
