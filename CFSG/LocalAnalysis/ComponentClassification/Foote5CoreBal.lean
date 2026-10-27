module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement

theorem exists_fixed_lift_of_odd_zStar {Y : Type*} [Group Y] [Finite Y]
    (hZ : Odd (Nat.card (Open.fusionZStar Y))) {α : MulAut Y} (hα : ∀ y, α (α y) = y)
    {s : Y ⧸ Open.fusionZStar Y} (hsα : zStarAut Y α s = s) :
    ∃ c : Y, α c = c ∧ (QuotientGroup.mk c : Y ⧸ Open.fusionZStar Y) = s := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  rw [zStarAut_mk] at hsα
  have hx : y⁻¹ * α y ∈ Open.fusionZStar Y := QuotientGroup.eq.mp hsα.symm
  have hy : α y = y * (y⁻¹ * α y) := by group
  have hαx : α (y⁻¹ * α y) = (y⁻¹ * α y)⁻¹ := by
    rw [map_mul, map_inv, hα]
    group
  have hxodd : Odd (orderOf (y⁻¹ * α y)) :=
    Odd.of_dvd_nat hZ ((Open.fusionZStar Y).orderOf_dvd_natCard hx)
  set x := y⁻¹ * α y
  set k := (orderOf x + 1) / 2
  have h2k : 2 * k = orderOf x + 1 := by
    have := Nat.odd_iff.mp hxodd
    omega
  refine ⟨y * x ^ k, ?_, ?_⟩
  · rw [map_mul, map_pow, hαx, inv_pow, hy, mul_assoc]
    congr 1
    rw [mul_inv_eq_iff_eq_mul, ← pow_add, ← two_mul, h2k, pow_succ, pow_orderOf_eq_one, one_mul]
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (pow_mem hx k), mul_one]

section Image

variable {K : Type} [Group K] [Finite K]

theorem odd_card_map_oddCore {Y : Subgroup K} {a : K}
    (hWN : oddCoreOfCentralizer a ≤ normalizer (Y : Set K)) :
    Odd (Nat.card (((oddCoreOfCentralizer a).subgroupOf (normalizer (Y : Set K))).map
      Y.normalizerMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWodd : Odd (Nat.card (oddCoreOfCentralizer a)) := by
    have h : Nat.card (oddCoreOfCentralizer a) =
        Nat.card (pPrimeCore 2 ↥(centralizer ({a} : Set K))) :=
      card_map_of_injective (subtype_injective _)
    rw [h]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine Odd.of_dvd_nat ?_ (card_map_dvd _ _)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv]

omit [Finite K] in
theorem map_oddCore_commute {Y : Subgroup K} {a : K} (haN : a ∈ normalizer (Y : Set K)) :
    ∀ β ∈ ((oddCoreOfCentralizer a).subgroupOf (normalizer (Y : Set K))).map
      Y.normalizerMonoidHom,
      β * Y.normalizerMonoidHom ⟨a, haN⟩ = Y.normalizerMonoidHom ⟨a, haN⟩ * β := by
  rintro _ ⟨⟨w, hwN⟩, hw, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp
    (oddCoreOfCentralizer_le_centralizer a (mem_subgroupOf.mp hw)))

omit [Finite K] in
theorem map_oddCore_conj {Y : Subgroup K} {a : K} (haN : a ∈ normalizer (Y : Set K)) :
    ∀ c : Y, Y.normalizerMonoidHom ⟨a, haN⟩ c = c →
      ∀ β ∈ ((oddCoreOfCentralizer a).subgroupOf (normalizer (Y : Set K))).map
        Y.normalizerMonoidHom,
        MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈
          ((oddCoreOfCentralizer a).subgroupOf (normalizer (Y : Set K))).map
            Y.normalizerMonoidHom := by
  rintro c hc _ ⟨⟨w, hwN⟩, hw, rfl⟩
  have hcC : (c : K) ∈ centralizer ({a} : Set K) := by
    have h := congrArg Subtype.val hc
    rw [normalizerMonoidHom_apply_apply_coe] at h
    apply mem_centralizer_singleton_iff.mpr
    calc (c : K) * a = a * c * a⁻¹ * a := by rw [h]
      _ = a * c := by group
  have hcw : (c : K) * w * (c : K)⁻¹ ∈ oddCoreOfCentralizer a :=
    conj_mem_oddCoreOfCentralizer hcC (mem_subgroupOf.mp hw)
  refine ⟨⟨(c : K), le_normalizer c.2⟩ * ⟨w, hwN⟩ * ⟨(c : K), le_normalizer c.2⟩⁻¹,
    mem_subgroupOf.mpr hcw, ?_⟩
  rw [map_mul, map_mul, map_inv, normalizerMonoidHom_of_mem c.2]

end Image

theorem inf_inner_le_oddCore_centralizer {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup (Y ⧸ Open.fusionZStar Y)]
    (hna : ∃ a b : Y ⧸ Open.fusionZStar Y, a * b ≠ b * a) {α : MulAut Y}
    (hα : ∀ y, α (α y) = y) (A : Subgroup (MulAut Y)) (hAodd : Odd (Nat.card A))
    (h1 : ∀ β ∈ A, β * α = α * β)
    (h2 : ∀ c : Y, α c = c → ∀ β ∈ A, MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A) :
    A.map (zStarAut Y) ⊓ (MulAut.conj : (Y ⧸ Open.fusionZStar Y) →*
      MulAut (Y ⧸ Open.fusionZStar Y)).range ≤
      (pPrimeCore 2 ↥(centralizer ({zStarAut Y α} : Set
        (MulAut (Y ⧸ Open.fusionZStar Y))))).map (centralizer
        ({zStarAut Y α} : Set (MulAut (Y ⧸ Open.fusionZStar Y)))).subtype := by
  set Inn := (MulAut.conj : (Y ⧸ Open.fusionZStar Y) →* MulAut (Y ⧸ Open.fusionZStar Y)).range
  have hInn : Inn.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, mulAut_conj_map g s⟩⟩
  set A₀ := A ⊓ Inn.comap (zStarAut Y) with hA₀
  have hA₀ : A.map (zStarAut Y) ⊓ Inn ≤ A₀.map (zStarAut Y) := by
    rintro _ ⟨⟨β, hβ, rfl⟩, hβI⟩
    exact ⟨β, ⟨hβ, hβI⟩, rfl⟩
  refine hA₀.trans (map_le_oddCore_centralizer hna hα A₀ ?_ (fun β hβ => h1 β hβ.1) ?_ ?_)
  · exact Odd.of_dvd_nat hAodd (card_dvd_of_le inf_le_left)
  · intro c hc β hβ
    refine ⟨h2 c hc β hβ.1, ?_⟩
    show zStarAut Y (MulAut.conj c * β * (MulAut.conj c)⁻¹) ∈ Inn
    rw [map_mul, map_mul, map_inv, zStarAut_conj]
    exact hInn.conj_mem _ hβ.2 _
  · intro β hβ
    obtain ⟨s, hs⟩ := hβ.2
    exact ⟨s, hs.symm⟩

end CFSG.ComponentClassification.Foote5
