module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralPrelim

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem mem_L1_of_piY_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1 ≤ P) {p : G}
    (hp : p ∈ P) (hpX : p ∈ normalizer (L1 : Set G)) (h1 : piY L1 ⟨p, hpX⟩ = 1) : p ∈ L1 := by
  have hO : (QuotientGroup.mk ⟨p, hpX⟩ : Xbar L1) ∈ fusionOddCore (Xbar L1) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact S.mem_L1_of_odd_image hP hL1P hp hpX
    (Odd.of_dvd_nat (natCard_fusionOddCore_odd (Xbar L1)) (Subgroup.orderOf_dvd_natCard _ hO))

theorem exists_sylow_piY (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    ∃ R : Sylow 2 (Ybar L1), (∀ p : G, ∀ hp : p ∈ P, piY L1 ⟨p, hP.le hp⟩ ∈ R) ∧
      ∀ y ∈ R, ∃ q ∈ P ⊓ centralizer ({z} : Set G), ∃ hq : q ∈ normalizer (L1 : Set G),
        piY L1 ⟨q, hq⟩ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (L1 : Set G) with hX
  have hPX : P ≤ X := hP.le
  set Q := P ⊓ centralizer ({z} : Set G) with hQ
  set H := zpowers z ⊔ (normalizer (F : Set G) ⊓ L) with hH
  have hHeq : H = X ⊓ centralizer ({z} : Set G) := S.inf_centralizer_eq.symm
  have hQH : Q ≤ H := hHeq ▸ inf_le_inf_right _ hPX
  have hHC : H ≤ centralizer ({z} : Set G) := hHeq ▸ inf_le_right
  have hQsyl : IsSylowOf 2 Q H := hT.of_le hQH hHC
  have hSP : IsSylowOf 2 ((P.subgroupOf X).map (piY L1)) ⊤ := by
    obtain ⟨R, hR⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 : IsPGroup 2 (P.subgroupOf X) := hP.isPGroup.comap_subtype
    have h2 : ¬ 2 ∣ (P.subgroupOf X).index := by
      have := R.not_dvd_index
      rwa [hR] at this
    exact isSylowOf_map_top (piY L1) (piY_surjective L1) h1 h2
  let f : ↥H →* Ybar L1 := (piY L1).comp (Subgroup.inclusion S.Q_le_X)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, hc, rfl⟩ := S.exists_centralizer_piY hcen y
    exact ⟨⟨c, hHeq ▸ mem_inf.2 ⟨c.2, hc⟩⟩, rfl⟩
  have hSQ : IsSylowOf 2 ((Q.subgroupOf H).map f) ⊤ :=
    isSylowOf_map_top f hf (hQsyl.isPGroup.comap_subtype) (by
      obtain ⟨R, hR⟩ := hQsyl.exists_sylow_eq_subgroupOf
      have := R.not_dvd_index
      rwa [hR] at this)
  have hle : (Q.subgroupOf H).map f ≤ (P.subgroupOf X).map (piY L1) := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨⟨(q : G), S.Q_le_X q.2⟩,
      Subgroup.mem_subgroupOf.2 (mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1, rfl⟩
  have heq := hSQ.eq_of_le hle le_top hSP.isPGroup
  obtain ⟨hle', hp2, hidx⟩ := isSylowOf_iff.1 hSP
  rw [Subgroup.relIndex_top_right] at hidx
  refine ⟨hp2.toSylow hidx, fun p hp => ?_, fun y hy => ?_⟩
  · exact ⟨⟨p, hP.le hp⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  · have hy' : y ∈ (Q.subgroupOf H).map f := by
      rw [← heq]
      exact hy
    obtain ⟨q, hq, rfl⟩ := hy'
    exact ⟨(q : G), Subgroup.mem_subgroupOf.1 hq, S.Q_le_X q.2, rfl⟩

theorem exists_mul_of_mem_sylowX (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) {p : G}
    (hp : p ∈ P) :
    ∃ q ∈ P ⊓ centralizer ({z} : Set G), ∃ l ∈ L1, p = q * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (L1 : Set G) with hX
  have hPX : P ≤ X := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  obtain ⟨R, hRP, hRQ⟩ := S.exists_sylow_piY hcen hP hT
  have hpX : p ∈ X := hPX hp
  obtain ⟨q, hqQ, hqX, hqp⟩ := hRQ _ (hRP p hp)
  have hqP : q ∈ P := (mem_inf.1 hqQ).1
  have h1 : piY L1 ⟨q⁻¹ * p, X.mul_mem (X.inv_mem hqX) hpX⟩ = 1 := by
    have : (⟨q⁻¹ * p, X.mul_mem (X.inv_mem hqX) hpX⟩ : ↥X) = (⟨q, hqX⟩ : ↥X)⁻¹ * ⟨p, hpX⟩ := rfl
    rw [this, map_mul, map_inv, hqp]
    exact inv_mul_cancel _
  have hl := S.mem_L1_of_piY_eq_one hP.isPGroup hL1P (P.mul_mem (P.inv_mem hqP) hp)
    (X.mul_mem (X.inv_mem hqX) hpX) h1
  exact ⟨q, hqQ, q⁻¹ * p, hl, by group⟩

theorem exists_eq_mul_of_mem_sylowX (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) {p : G}
    (hp : p ∈ P) :
    ∃ d ∈ normalizer (F : Set G) ⊓ L, ∃ l ∈ L1, p = d * l ∨ p = z * d * l := by
  obtain ⟨q, hq, l, hl, rfl⟩ := S.exists_mul_of_mem_sylowX hcen hP hT hp
  have hqQ : q ∈ zpowers z ⊔ (normalizer (F : Set G) ⊓ L) :=
    S.inf_centralizer_eq ▸ mem_inf.2 ⟨hP.le (mem_inf.1 hq).1, (mem_inf.1 hq).2⟩
  rcases S.eq_or_eq_mul_of_mem_sup hqQ with ⟨d, hd, hqd⟩ | ⟨d, hd, hqd⟩
  · exact ⟨d, hd, l, hl, Or.inl (by rw [hqd])⟩
  · exact ⟨d, hd, l, hl, Or.inr (by rw [hqd])⟩

end Setup

end CFSG.EvenSporadicStandard.M23Std
