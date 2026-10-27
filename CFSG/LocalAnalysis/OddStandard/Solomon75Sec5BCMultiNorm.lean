module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapDiagData
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34Solv

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
open scoped commutatorElement

section Norm

variable {X : Type} [Group X] [Finite X]

private theorem bcdNorm_le_normalizer_of_solvable {W : Type} [Group W] [Finite W]
    {R K : Subgroup W} (hR : Group.IsSolvable ↥R) (hRs : R.IsSubnormal) (hK : IsComponent K) :
    R ≤ normalizer (K : Set W) := by
  have h : ⁅K, R⁆ = ⊥ := (component_solvable_centralizer hR hRs).1 K hK
  rw [Subgroup.commutator_comm] at h
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
    (Subgroup.centralizer_le_normalizer _)

private theorem bcdNorm_EPlus_le_normalizer {W : Type} [Group W] [Finite W]
    (hO : pPrimeCore 2 W = ⊥) {K : Subgroup W} (hK : IsComponent K) :
    EPlus W ≤ normalizer (K : Set W) := by
  have h3 : pCore 3 W = ⊥ := pCore_three_eq_bot hO
  have hlayer : layer W ≤ normalizer (K : Set W) := by
    refine sSup_le fun M hM => ?_
    rcases distinct_components_commute hK hM with h | h
    · subst h
      exact Subgroup.le_normalizer
    · rw [Subgroup.commutator_comm] at h
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le_normalizer _)
  have h1 := bcdNorm_le_normalizer_of_solvable (isSolvable_NOne h3)
    (NOne_normal (G := W)).isSubnormal hK
  have h2 := bcdNorm_le_normalizer_of_solvable (isSolvable_NTwo h3)
    (NTwo_normal (G := W)).isSubnormal hK
  exact sup_le (sup_le hlayer h1) h2

private theorem bcdNorm_pCore_le_normalizer {W : Type} [Group W] [Finite W] {K : Subgroup W}
    (hK : IsComponent K) : pCore 2 W ≤ normalizer (K : Set W) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(pCore 2 W) := (pCore_isPGroup (p := 2) (G := W)).isNilpotent
  exact bcdNorm_le_normalizer_of_solvable inferInstance
    (pCore_normal (p := 2) (G := W)).isSubnormal hK

theorem lplus_core_le_normalizer {H B : Subgroup X} (hB : IsPCompIn 2 H B) :
    oTwoPrimeOf (LPlusIn H) ⊔ oddTwoCoreOf H ≤ normalizer (B : Set X) := by
  obtain ⟨K, hK, -, hKeq, -⟩ := hB.2
  have hO : pPrimeCore 2 (↥H ⧸ pPrimeCore 2 ↥H) = ⊥ :=
    pPrimeCore_quotient_eq_bot (G := ↥H) Nat.prime_two
  have key : ∀ y : ↥H, QuotientGroup.mk' (pPrimeCore 2 ↥H) y ∈
      normalizer (K : Set (↥H ⧸ pPrimeCore 2 ↥H)) → (y : X) ∈ normalizer (B : Set X) := by
    intro y hy
    refine mem_normalizer_of_map_normalizes_pCompIn hB y.2 ?_
    rw [hKeq]
    exact hy
  refine sup_le ((oTwoPrimeOf_le _).trans ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact key w (bcdNorm_EPlus_le_normalizer hO hK hw)
  · rintro _ ⟨w, hw, rfl⟩
    exact key w (bcdNorm_pCore_le_normalizer hK hw)

theorem LPlusIn_le_of_isSubnormal {Y D : Subgroup X} (hYD : Y ≤ D)
    (hY : (Y.subgroupOf D).IsSubnormal) : LPlusIn Y ≤ LPlusIn D := by
  have key : ∀ U : Subgroup ↥D, U.IsSubnormal → LPlusIn (U.map D.subtype) ≤ LPlusIn D := by
    intro U hU
    induction hU with
    | top =>
      rw [Subgroup.map_top, Subgroup.range_subtype]
    | step A B hAB _ hN ih =>
      refine le_trans (LPlusIn_le_of_normal (Subgroup.map_mono hAB) ?_) ih
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAB] at hN
      exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)
  have := key _ hY
  rwa [Subgroup.map_subgroupOf_eq_of_le hYD] at this

private theorem bcdNorm_le_pCore_of_isSubnormal {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (hU : U.IsSubnormal) (hp : IsPGroup 2 ↥U) : U ≤ pCore 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = 2} hU
  rw [← pCore_eq_piCore U 2, ← pCore_eq_piCore G 2] at h
  have htop : pCore 2 ↥U = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨Subgroup.normal_top, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem le_oddTwoCoreOf_of_isSubnormal {D Y R : Subgroup X} (hYD : Y ≤ D)
    (hY : (Y.subgroupOf D).IsSubnormal) (hR2 : IsPGroup 2 ↥R) (hRY : R ≤ Y)
    (hRn : ∀ y ∈ Y, ∀ r ∈ R, ∃ r' ∈ R, ∃ o ∈ oddCoreOf Y, y * r * y⁻¹ = r' * o) :
    R ≤ oddTwoCoreOf D := by
  set π : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D)
  have hRD : R ≤ D := hRY.trans hYD
  have hR₀Y₀ : R.subgroupOf D ≤ Y.subgroupOf D := fun x hx => hRY hx
  have hoY : oddCoreOf Y ≤ oddCoreOf D := pPrimeCoreOf_le_oddCoreOf hYD hY
  have hYq : ((Y.subgroupOf D).map π).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hY
  have hRqY : (R.subgroupOf D).map π ≤ (Y.subgroupOf D).map π := Subgroup.map_mono hR₀Y₀
  have hnorm : ∀ a ∈ (Y.subgroupOf D).map π, ∀ b ∈ (R.subgroupOf D).map π,
      a * b * a⁻¹ ∈ (R.subgroupOf D).map π := by
    rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨r₀, hr₀, rfl⟩
    obtain ⟨r', hr', o, ho, hyro⟩ := hRn (y₀ : X) hy₀ (r₀ : X) hr₀
    obtain ⟨o₀, ho₀, rfl⟩ := hoY ho
    have hr'D : r' ∈ D := hRD hr'
    refine ⟨⟨r', hr'D⟩, hr', ?_⟩
    have h1 : y₀ * r₀ * y₀⁻¹ = ⟨r', hr'D⟩ * o₀ := Subtype.ext hyro
    have hπ1 : π o₀ = 1 := (QuotientGroup.eq_one_iff o₀).mpr ho₀
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul, hπ1, mul_one]
  haveI hnormal : (((R.subgroupOf D).map π).subgroupOf ((Y.subgroupOf D).map π)).Normal :=
    ⟨fun n hn g => hnorm (g : _) g.2 (n : _) hn⟩
  have hRsub : ((R.subgroupOf D).map π).IsSubnormal :=
    Subgroup.IsSubnormal.trans hRqY (Subgroup.Normal.isSubnormal hnormal) hYq
  have hR₀2 : IsPGroup 2 ↥((R.subgroupOf D).map π) := hR2.comap_subtype.map π
  have hcore := bcdNorm_le_pCore_of_isSubnormal hRsub hR₀2
  intro r hr
  have hrD : r ∈ D := hRD hr
  exact ⟨⟨r, hrD⟩,
    hcore (Subgroup.mem_map_of_mem π (show (⟨r, hrD⟩ : ↥D) ∈ R.subgroupOf D from hr)), rfl⟩

theorem le_T_of_le_lPlus_inf {u t : X} (hu2 : u * u = 1) (hut : u * t = t * u) {Q : Subgroup X}
    (hQ : Q ≤ oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X) ⊓ centralizer ({t} : Set X)))) :
    Q ≤ oTwoPrimeOf (LPlusIn (centralizer ({t} : Set X))) ⊔
      oddTwoCoreOf (centralizer ({t} : Set X)) := by
  have hord : orderOf u ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hu2)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hB : IsPGroup 2 (zpowers u) := IsPGroup.of_card ((Nat.card_zpowers u).trans hi)
  have hBC : zpowers u ≤ centralizer ({t} : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hut.symm
  have hcz : centralizer ((zpowers u : Subgroup X) : Set X) = centralizer ({u} : Set X) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact h _ (Subgroup.mem_zpowers _)
    · intro h v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hx : u * x = x * u := h u rfl
      exact (Commute.zpow_left hx k).eq
  have h2 := lPlus_balance (centralizer ({t} : Set X)) (zpowers u) hBC hB
  rw [hcz, inf_comm] at h2
  exact hQ.trans h2

theorem le_normalizer_of_le_lPlus_inf {u t : X} (hu2 : u * u = 1) (hut : u * t = t * u)
    {Q : Subgroup X}
    (hQ : Q ≤ oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X) ⊓ centralizer ({t} : Set X))))
    {B : Subgroup X} (hB : IsPCompIn 2 (centralizer ({t} : Set X)) B) :
    Q ≤ normalizer (B : Set X) :=
  (le_T_of_le_lPlus_inf hu2 hut hQ).trans (lplus_core_le_normalizer hB)

end Norm

end CFSG.OddStandard.Solomon75
