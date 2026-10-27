module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapTransfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneIndex
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
  (hle : ∀ t ∈ escapingSylowImage S z, t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) →
    t ∈ J ⊔ swapComponent J s)
include h hsS hs hle

theorem false_of_swap_le_sup :
    False := by
  have hz := h.square.central
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z)) with hN
  set T := liftToSylow hz (escapingSylowImage S z ⊓ N) with hT
  have hbarS : ∀ t : (S : Subgroup G), sylowBar hz t ∈ escapingSylowImage S z := fun t => by
    rw [← sylowBar_range hz]
    exact ⟨t, rfl⟩
  have hs2N : s * s ∈ N := by
    have := h.inv_mul_mem_normalizer_swap hs (u := s⁻¹) (v := s)
      (fun h1 => hs (by simpa using N.inv_mem h1)) hs
    rwa [inv_inv] at this
  obtain ⟨y, hyS, hyN, hy2⟩ := h.exists_sq_eq_bar_swap hsS hs
    (hle _ ((escapingSylowImage S z).mul_mem hsS hsS) hs2N)
  obtain ⟨y', rfl⟩ := exists_sylowBar_eq hz hyS
  have hy'2 : (y' : G) ^ 2 = z := by
    rw [← map_pow, sylowBar_eq_bar_iff] at hy2
    rwa [Subgroup.coe_pow] at hy2
  have hzz : z * z = 1 := by rw [← pow_two, ← hz.2.1, pow_orderOf_eq_one]
  have hy'4 : (y' : G) ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hy'2, pow_two, hzz]
  have hcoset : ∀ u ∈ escapingSylowImage S z, ∀ v ∈ escapingSylowImage S z,
      u ∉ escapingSylowImage S z ⊓ N → v ∉ escapingSylowImage S z ⊓ N →
      u⁻¹ * v ∈ escapingSylowImage S z ⊓ N := fun u hu v hv hu' hv' =>
    ⟨(escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem hu) hv,
      h.inv_mul_mem_normalizer_swap hs (fun h1 => hu' ⟨hu, h1⟩) (fun h1 => hv' ⟨hv, h1⟩)⟩
  have hmemT : ∀ t : (S : Subgroup G), (t : G) ∈ T ↔
      sylowBar hz t ∈ escapingSylowImage S z ⊓ N := fun t => mem_liftToSylow_iff hz t
  have hTS : T ≤ (S : Subgroup G) := liftToSylow_le hz _
  have hnormal : (T.subgroupOf (S : Subgroup G)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemT] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_of_inv_mul_mem inf_le_left hcoset (hbarS g) hn
  have habel : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 := commutator_mem_of_inv_mul_mem hcoset (hbarS ⟨g₁, hg₁⟩) (hbarS ⟨g₂, hg₂⟩)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
    rw [commutatorElement_def]
    exact (hmemT _).mpr h1
  have hyT : (y' : G) ∉ T := fun h1 => hyN ((hmemT y').mp h1).2
  have hcondz : ∀ a : G, a⁻¹ * z * a ∈ (S : Subgroup G) → z⁻¹ * (a⁻¹ * z * a) ∈ T := by
    intro a ha
    have hzN : escapingBar z ∈ N := by
      rw [hN, Subgroup.mem_normalizer_iff]
      intro w
      rw [show escapingBar z * w * (escapingBar z)⁻¹ = w by
        rw [← (h.quotientData.commute_bar w).eq, mul_inv_cancel_right]]
    have hzT : z ∈ T := (mem_liftToSylow hz).mpr ⟨hz.1, hbarS ⟨z, hz.1⟩, by
      rw [sylowBar_self hz]
      exact hzN⟩
    have hconjT : a⁻¹ * z * a ∈ T := by
      set x : (S : Subgroup G) := ⟨a⁻¹ * z * a, ha⟩
      have hx2 : sylowBar hz x * sylowBar hz x = 1 := by
        rw [← map_mul, ← map_one (sylowBar hz)]
        congr 1
        apply Subtype.ext
        change a⁻¹ * z * a * (a⁻¹ * z * a) = 1
        rw [show a⁻¹ * z * a * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a by group, hzz]
        group
      exact (hmemT x).mpr ⟨hbarS x, h.mem_normalizer_of_mul_self_eq_one hs (hbarS x) hx2⟩
    exact T.mul_mem (T.inv_mem hzT) hconjT
  have hcond : ∀ (m : ℤ) (a : G), a⁻¹ * (y' : G) ^ m * a ∈ (S : Subgroup G) →
      ((y' : G) ^ m)⁻¹ * (a⁻¹ * (y' : G) ^ m * a) ∈ T := by
    intro m a ha
    have h4z : (y' : G) ^ (4 : ℤ) = 1 := by
      rw [show (4 : ℤ) = ((2 ^ 2 : ℕ) : ℤ) by norm_num, zpow_natCast, hy'4]
    have hm : (y' : G) ^ m = (y' : G) ^ (m % 4) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv m 4]
      rw [zpow_add, zpow_mul, h4z, one_zpow, mul_one]
    rw [hm] at ha ⊢
    obtain ⟨r, hr⟩ : ∃ r, m % 4 = r := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg m (by norm_num)
    have hr4 : r < 4 := hr ▸ Int.emod_lt_of_pos m (by norm_num)
    rw [hr] at ha ⊢
    interval_cases r
    · simp only [zpow_zero, mul_one, inv_mul_cancel, inv_one]
      exact T.one_mem
    · simp only [zpow_one] at ha ⊢
      exact h.transfer_cond_swap hsS hs hle (u := y') hyN hy'2 ha
    · have h2 : (y' : G) ^ (2 : ℤ) = z := by rw [zpow_ofNat, hy'2]
      rw [h2] at ha ⊢
      exact hcondz a ha
    · have h3 : (y' : G) ^ (3 : ℤ) = (y' : G)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
        exact h4z
      rw [h3] at ha ⊢
      have hyinv : sylowBar hz y'⁻¹ ∉ N := fun h1 => hyN (by
        rw [map_inv] at h1
        simpa using N.inv_mem h1)
      have hyinv2 : ((y'⁻¹ : (S : Subgroup G)) : G) ^ 2 = z := by
        rw [Subgroup.coe_inv, inv_pow, hy'2, inv_eq_of_mul_eq_one_left hzz]
      exact h.transfer_cond_swap hsS hs hle (u := y'⁻¹) hyinv hyinv2 ha
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_one (p := 2) (H := (S : Subgroup G))
    (K := T) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index)
    ⟨hTS, hnormal⟩ habel y'.2 hyT ⟨2, hy'4⟩ hcond
  apply hnot
  rw [h.square.core.isPerfect.commutator_eq_top]
  exact Subgroup.mem_top _

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
