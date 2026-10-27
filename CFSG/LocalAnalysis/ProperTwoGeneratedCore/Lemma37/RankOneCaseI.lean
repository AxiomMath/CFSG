module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneTransfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneRoot
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

theorem false_of_not_sylowImage_le_sup
    (hnle : ¬ escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    False := by
  have hz := h.square.central
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JK := J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) with hJK
  set T := liftToSylow hz (escapingSylowImage S z ⊓ JK) with hT
  have hbarS : ∀ s : (S : Subgroup G), sylowBar hz s ∈ escapingSylowImage S z := fun s => by
    rw [← sylowBar_range hz]
    exact ⟨s, rfl⟩
  obtain ⟨w₀, hw₀S, hw₀⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨y, hyS, hyJK, hy2⟩ := h.exists_sq_eq_bar_not_mem hw₀S hw₀
  obtain ⟨y', rfl⟩ := exists_sylowBar_eq hz hyS
  have hy'2 : (y' : G) ^ 2 = z := by
    rw [← map_pow, sylowBar_eq_bar_iff] at hy2
    rwa [Subgroup.coe_pow] at hy2
  have hzz : z * z = 1 := by rw [← pow_two, ← hz.2.1, pow_orderOf_eq_one]
  have hy'4 : (y' : G) ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hy'2, pow_two, hzz]
  have hcoset : ∀ u ∈ escapingSylowImage S z, ∀ v ∈ escapingSylowImage S z,
      u ∉ escapingSylowImage S z ⊓ JK → v ∉ escapingSylowImage S z ⊓ JK →
      u⁻¹ * v ∈ escapingSylowImage S z ⊓ JK := fun u hu v hv hu' hv' =>
    h.inv_mul_mem_inf_sup hu hv hu' hv'
  have hmemT : ∀ s : (S : Subgroup G), (s : G) ∈ T ↔
      sylowBar hz s ∈ escapingSylowImage S z ⊓ JK := fun s => mem_liftToSylow_iff hz s
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
  have hyT : (y' : G) ∉ T := fun h1 => hyJK ((hmemT y').mp h1).2
  have hcondz : ∀ a : G, a⁻¹ * z * a ∈ (S : Subgroup G) → z⁻¹ * (a⁻¹ * z * a) ∈ T := by
    intro a ha
    have hzT : z ∈ T := (mem_liftToSylow hz).mpr ⟨hz.1, hbarS ⟨z, hz.1⟩, by
      rw [sylowBar_self hz]
      exact Subgroup.mem_sup_left (h.square.caseTwo J h.component)⟩
    have hconjT : a⁻¹ * z * a ∈ T := by
      set x : (S : Subgroup G) := ⟨a⁻¹ * z * a, ha⟩
      have hx2 : sylowBar hz x * sylowBar hz x = 1 := by
        rw [← map_mul, ← map_one (sylowBar hz)]
        congr 1
        apply Subtype.ext
        change a⁻¹ * z * a * (a⁻¹ * z * a) = 1
        rw [show a⁻¹ * z * a * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a by group, hzz]
        group
      exact (hmemT x).mpr ⟨hbarS x, (h.action_mem_inner_iff).mp
        (h.action_mem_inner_of_mul_self_eq_one (hbarS x) hx2)⟩
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
      exact h.transfer_cond_of_sq_eq (u := y') hyJK hy'2 ha
    · have h2 : (y' : G) ^ (2 : ℤ) = z := by rw [zpow_ofNat, hy'2]
      rw [h2] at ha ⊢
      exact hcondz a ha
    · have h3 : (y' : G) ^ (3 : ℤ) = (y' : G)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
        exact h4z
      rw [h3] at ha ⊢
      have hyinv : sylowBar hz y'⁻¹ ∉ JK := fun h1 => hyJK (by
        rw [map_inv] at h1
        simpa using JK.inv_mem h1)
      have hyinv2 : ((y'⁻¹ : (S : Subgroup G)) : G) ^ 2 = z := by
        rw [Subgroup.coe_inv, inv_pow, hy'2, inv_eq_of_mul_eq_one_left hzz]
      exact h.transfer_cond_of_sq_eq (u := y'⁻¹) hyinv hyinv2 ha
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_one (p := 2) (H := (S : Subgroup G))
    (K := T) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index)
    ⟨hTS, hnormal⟩ habel y'.2 hyT ⟨2, hy'4⟩ hcond
  apply hnot
  rw [h.square.core.isPerfect.commutator_eq_top]
  exact Subgroup.mem_top _

theorem false_of_normal :
    False := by
  by_cases hle : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))
  · exact h.false_of_sylowImage_le_sup hle
  · exact h.false_of_not_sylowImage_le_sup hle

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
