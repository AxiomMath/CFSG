module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootSections
public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderEight

open Equiv CFSG.Wreathed.WreathCentralSquare CFSG.Wreathed.SquareRootSmallCharacterRigidity
  CFSG.Wreathed.FourPointOrderFour CFSG.Wreathed.ConditionalSquareRoot

open scoped Classical Pointwise

theorem perm_four_pow_four_of_commute_involution : ∀ g h : Perm (Fin 4), h ^ 2 = 1 → h ≠ 1 →
    g * h = h * g → g ^ 4 = 1 := by
  decide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rootCentralizer_le (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.centralizer ({actualRoot S e} : Set G) ≤ involutionCentralizer n S e := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  change g ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
  rw [Subgroup.mem_centralizer_singleton_iff, ← actualRoot_pow_modulus n (by omega) S e]
  exact (Commute.pow_right (show Commute g _ from hg) _).eq

theorem odd_orderOf_of_mem_centralizerOddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {c : involutionCentralizer n S e} (hc : c ∈ centralizerOddCore n S e) : Odd (orderOf c) :=
  (CFSG.ComponentClassification.OddCore.odd_card (involutionCentralizer n S e)).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hc)

theorem mem_centralizerOddCore_of_commute_root (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    (r : involutionCentralizer n S e) (hr : Commute (r : G) (actualRoot S e))
    (hodd : Odd (orderOf r)) : r ∈ centralizerOddCore n S e := by
  set ρN : involutionCentralizer n S e := wreathModelHom (centralizerSylow n hn S e)
    (centralizerCoordinates n hn S e) (originalRoot (2 ^ n)) with hρN
  set aN : involutionCentralizer n S e := wreathModelHom (centralizerSylow n hn S e)
    (centralizerCoordinates n hn S e) (Original.a (2 ^ n)) with haN
  set π := centralizerOddCoreMap n S e with hπ
  set τ := centralizerFullQuotientMap n hn S e with hτ
  have hρG : (ρN : G) = actualRoot S e := rfl
  have hρa : ρN ^ 2 = aN := by rw [hρN, haN, ← map_pow, originalRoot_sq]
  have hρord : orderOf ρN = 2 ^ (n + 1) := by
    rw [← Subgroup.orderOf_coe, hρG, actualRoot_orderOf n hn S e, pow_succ, mul_comm]
  have haord : orderOf aN = 2 ^ n := orderOf_centralizerModelHom_a n hn S e
  have hπker : ∀ c, π c = 1 ↔ c ∈ centralizerOddCore n S e := fun c => QuotientGroup.eq_one_iff c
  have hτker : ∀ h, τ h = 1 ↔ h ∈ centralizerFullCenterImage n hn S e := fun h =>
    QuotientGroup.eq_one_iff h
  have hA : ∀ h ∈ centralizerFullCenterImage n hn S e, ∃ k : ℤ, h = π aN ^ k := by
    intro h hh
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hh
    rw [centralizerFullCenter_eq_zpowers] at hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ⟨k, map_zpow _ _ _⟩
  have hsq : τ (π ρN) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hρa, hτker]
    exact centralizerModelHom_a_mem_fullCenterImage n hn S e
  have hne : τ (π ρN) ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := hA _ ((hτker _).mp h)
    have hsplit : ρN ^ (1 - 2 * k) = ρN * (ρN ^ 2) ^ (-k) := by
      rw [← zpow_natCast ρN 2, ← zpow_mul, ← zpow_one_add]
      congr 1
      push_cast
      ring
    have hmem : ρN ^ (1 - 2 * k) ∈ centralizerOddCore n S e := by
      rw [← hπker, hsplit, hρa, map_mul, map_zpow, hk, ← zpow_add, add_neg_cancel, zpow_zero]
    have h1 := odd_orderOf_of_mem_centralizerOddCore n S e hmem
    rw [orderOf_odd_power hρord ⟨-k, by ring⟩] at h1
    exact Nat.not_even_iff_odd.mpr h1 ((Nat.even_pow' (by omega)).mpr even_two)
  have hrρ : r * ρN = ρN * r := Subtype.ext hr.eq
  have hcomm : alpha (τ (π r)) * alpha (τ (π ρN)) = alpha (τ (π ρN)) * alpha (τ (π r)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hrρ]
  have hg4 := perm_four_pow_four_of_commute_involution (alpha (τ (π r))) (alpha (τ (π ρN)))
    (by rw [← map_pow, hsq, map_one])
    (fun h => hne (alpha.injective (h.trans (map_one alpha).symm))) hcomm
  have hgodd : Odd (orderOf (alpha (τ (π r)))) := by
    rw [MulEquiv.orderOf_eq]
    exact hodd.of_dvd_nat ((orderOf_map_dvd τ _).trans (orderOf_map_dvd π r))
  have hg1 : τ (π r) = 1 := by
    have h1 : orderOf (alpha (τ (π r))) = 1 :=
      eq_one_of_odd_of_dvd_two_pow hgodd (orderOf_dvd_of_pow_eq_one hg4) 2 (by norm_num)
    rw [orderOf_eq_one_iff] at h1
    exact alpha.injective (h1.trans (map_one alpha).symm)
  obtain ⟨k, hk⟩ := hA _ ((hτker _).mp hg1)
  have hpow : π r ^ (2 ^ n) = 1 := by
    rw [hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, ← haord,
      pow_orderOf_eq_one, map_one, one_zpow]
  have h1 : orderOf (π r) = 1 :=
    eq_one_of_odd_of_dvd_two_pow (hodd.of_dvd_nat (orderOf_map_dvd π r))
      (orderOf_dvd_of_pow_eq_one hpow) n rfl
  exact (hπker r).mp (orderOf_eq_one_iff.mp h1)

theorem mem_oddCore_rootCentralizer_iff (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    (c : Subgroup.centralizer ({actualRoot S e} : Set G)) :
    c ∈ CFSG.oddCore (Subgroup.centralizer ({actualRoot S e} : Set G)) ↔
      (c : G) ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := by
  obtain ⟨-, -, -, -, hmem, -⟩ := original_root_centralizer_product n hn S e
  rw [hmem]
  constructor
  · intro hodd
    have hcN : (c : G) ∈ involutionCentralizer n S e := rootCentralizer_le n hn S e c.2
    refine ⟨⟨c, hcN⟩, mem_centralizerOddCore_of_commute_root n hn S e alpha ⟨c, hcN⟩
      (Subgroup.mem_centralizer_singleton_iff.mp c.2) ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]
  · rintro ⟨r, hr, hrc⟩
    rw [← hrc, Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_centralizerOddCore n S e hr

theorem rootCentralizer_structure (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) (y : G)
    (hy : y = actualRoot S e) :
    let D := Subgroup.centralizer ({y} : Set G)
    let Rρ : Subgroup G := (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ D
    (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = Subgroup.zpowers y) ∧
    Rρ.subgroupOf D = CFSG.oddCore D ∧ (Rρ.subgroupOf D).Normal ∧ Odd (Nat.card Rρ) ∧
    (Rρ : Set G) * (Subgroup.zpowers y : Set G) = D ∧ Rρ ⊓ Subgroup.zpowers y = ⊥ ∧
    Nat.card D = 2 * 2 ^ n * Nat.card Rρ := by
  intro D Rρ
  subst hy
  obtain ⟨-, -, hyord, hodd, -, -, E, -, hEinv⟩ := original_root_centralizer_product n hn S e
  have hiff := mem_oddCore_rootCentralizer_iff n hn S e alpha
  have hsub : Rρ.subgroupOf D = CFSG.oddCore D := by
    ext c
    rw [Subgroup.mem_subgroupOf, hiff]
    exact ⟨fun h => h.1, fun h => ⟨h, c.2⟩⟩
  have hle : Rρ ≤ D := inf_le_right
  have hcard : Nat.card Rρ = Nat.card (CFSG.oddCore D) := by
    rw [← hsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
  have hyD : Subgroup.zpowers (actualRoot S e) ≤ D :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine ⟨?_, hsub, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_cyclic_centralizer_sylow n hn S e _ hyord
    refine ⟨P, ?_⟩
    rw [hP, MonoidHom.map_zpowers]
    rfl
  · rw [hsub]
    infer_instance
  · rw [hcard]
    exact hodd
  · ext g
    constructor
    · rintro ⟨r, hr, t, ht, rfl⟩
      exact D.mul_mem (hle hr) (hyD ht)
    · intro hg
      let c : D := ⟨g, hg⟩
      exact ⟨(((E.symm c).1 : D) : G), ⟨(hiff _).mp (E.symm c).1.2, ((E.symm c).1 : D).2⟩,
        ((E.symm c).2 : G), (E.symm c).2.2, hEinv c⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨⟨r, hr, hrg⟩, -⟩, hgy⟩
    have hgodd : Odd (orderOf g) := by
      rw [← hrg, Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact odd_orderOf_of_mem_centralizerOddCore n S e hr
    have hdvd : orderOf g ∣ 2 ^ (n + 1) := by
      rw [pow_succ, mul_comm, ← hyord]
      exact orderOf_dvd_of_mem_zpowers hgy
    have h1 := eq_one_of_odd_of_dvd_two_pow hgodd hdvd (n + 1) rfl
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  · rw [(maximal_root_centralizer_index n hn S e _ hyord).2.2, hcard, mul_comm]

omit [Finite G] in
theorem root_conj_s_sq (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    wreathModelHom S e (Original.s (2 ^ 2)) ^ 2 ∈ (S : Subgroup G) ∧
      (wreathModelHom S e (Original.s (2 ^ 2)) ^ 2)⁻¹ * actualRoot S e *
        wreathModelHom S e (Original.s (2 ^ 2)) ^ 2 = actualRoot S e ^ 5 := by
  set s := wreathModelHom S e (Original.s (2 ^ 2)) with hs
  have hx2 : wreathModelHom S e (Original.x2 (2 ^ 2)) = s ^ 2 := by
    change wreathModelHom S e (Original.s (2 ^ 2) ^ (2 ^ 2 / 2)) = _
    rw [map_pow]
    rfl
  have hs4 : s ^ 4 = 1 := by
    have hord : orderOf s = 2 ^ 2 := by
      rw [hs, orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_s]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← hord, pow_orderOf_eq_one]
  have hinv : (s ^ 2)⁻¹ = s ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    exact hs4
  refine ⟨?_, ?_⟩
  · rw [hs, ← map_pow]
    exact (e.symm _).2
  · have h := actualRoot_conjugate_half 2 (by norm_num) S e
    rw [hx2, hinv] at h
    rw [hinv]
    exact h

theorem root_not_isConj_inv (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    ¬ IsConj (actualRoot S e) (actualRoot S e)⁻¹ := by
  intro h
  have h' : IsConj (actualRoot S e ^ (1 : ℤ)) (actualRoot S e ^ (-1 : ℤ)) := by
    rwa [zpow_one, zpow_neg_one]
  have hmod := (actualRoot_odd_zpow_isConj_iff 2 le_rfl S e odd_one ⟨-1, by norm_num⟩).mp h'
  rw [Int.ModEq] at hmod
  norm_num at hmod

end CFSG.Wreathed.FourPointOrderEight
