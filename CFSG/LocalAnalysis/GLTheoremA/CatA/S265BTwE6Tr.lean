module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.HardMathSupport.Solomon.Coordinator.B3RedAlg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

theorem ker_chevQuotHom_le_center_of_core (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) : (chevQuotHom 3 S).ker ≤ Subgroup.center ↥S := by
  refine le_center_of_normal_of_isQuasisimple hS (chevQuotHom 3 S).normal_ker fun htop => ?_
  haveI := (chev_pSimple_simple_nonabelian Nat.prime_three
    (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hS hcore)).1
  obtain ⟨y, hy⟩ := exists_ne (1 : PSimple 3 S)
  obtain ⟨s, rfl⟩ := chevQuotHom_surjective 3 S y
  exact hy (by rw [← MonoidHom.mem_ker, htop]; exact Subgroup.mem_top s)

theorem eq_one_of_mem_ker_chevQuotHom_of_mul_self (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {z : ↥S} (hz : chevQuotHom 3 S z = 1) (hz2 : z * z = 1) :
    z = 1 := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center ↥S :=
    Subgroup.zpowers_le.2 (ker_chevQuotHom_le_center_of_core hS hcore hz)
  have hN : (Subgroup.zpowers z).Normal := ⟨fun y hy g => by
    rw [Subgroup.mem_center_iff.1 (hle hy) g, mul_inv_cancel_right]
    exact hy⟩
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2))
      (by norm_num)
  have h3 : Subgroup.zpowers z ≤ GLAPPrimeCore 3 ↥S := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨hN, hcop⟩
  rw [hcore] at h3
  exact Subgroup.mem_bot.1 (h3 (Subgroup.mem_zpowers z))

theorem exists_mul_self_lift_chevQuotHom (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {v : PSimple 3 S} (hv : v * v = 1) :
    ∃ s : ↥S, chevQuotHom 3 S s = v ∧ s * s = 1 := by
  obtain ⟨s₀, rfl⟩ := chevQuotHom_surjective 3 S v
  have hz : chevQuotHom 3 S (s₀ * s₀) = 1 := by rw [map_mul]; exact hv
  have hodd : Odd (orderOf (s₀ * s₀)) := by
    rw [Nat.odd_iff]
    by_contra hne
    obtain ⟨k, hk⟩ : 2 ∣ orderOf (s₀ * s₀) := Nat.dvd_of_mod_eq_zero (by omega)
    have hk1 : (s₀ * s₀) ^ k = 1 := by
      refine eq_one_of_mem_ker_chevQuotHom_of_mul_self hS hcore (by rw [map_pow, hz, one_pow]) ?_
      rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
    have hpos : 0 < orderOf (s₀ * s₀) := orderOf_pos _
    have hle := orderOf_le_of_pow_eq_one (by omega) hk1
    omega
  obtain ⟨m, hm⟩ := hodd
  refine ⟨s₀ ^ orderOf (s₀ * s₀), ?_, ?_⟩
  · rw [map_pow, hm, pow_succ, pow_mul, sq, hv, one_pow, one_mul]
  · rw [← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]

theorem conj_eq_of_chevAut_fix_of_mul_self (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {g : X} (hg : g ∈ Subgroup.normalizer (S : Set X))
    {s : ↥S} (hs : s * s = 1)
    (hfix : chevAut 3 S ⟨g, hg⟩ (chevQuotHom 3 S s) = chevQuotHom 3 S s) :
    g * (s : X) = s * g := by
  set s' := S.normalizerMonoidHom ⟨g, hg⟩ s with hs'def
  rw [chevAut_chevQuotHom] at hfix
  have hz : chevQuotHom 3 S (s'⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, hfix, inv_mul_cancel]
  have hzc := Subgroup.mem_center_iff.1 (ker_chevQuotHom_le_center_of_core hS hcore hz)
  have hs's' : s' * s' = 1 := by rw [hs'def, ← map_mul, hs, map_one]
  have hz2 : (s'⁻¹ * s) * (s'⁻¹ * s) = 1 := by
    have e : s * s = s' * s' * ((s'⁻¹ * s) * (s'⁻¹ * s)) :=
      calc s * s = s' * ((s'⁻¹ * s) * s') * (s'⁻¹ * s) := by group
        _ = s' * (s' * (s'⁻¹ * s)) * (s'⁻¹ * s) := by rw [← hzc s']
        _ = s' * s' * ((s'⁻¹ * s) * (s'⁻¹ * s)) := by group
    rw [hs, hs's', one_mul] at e
    exact e.symm
  have hz1 := eq_one_of_mem_ker_chevQuotHom_of_mul_self hS hcore hz hz2
  have hss : s' = s := (inv_mul_eq_one.1 hz1)
  have h1 : g * (s : X) * g⁻¹ = s := by
    rw [← chev_coe_normalizerMonoidHom ⟨g, hg⟩ s, ← hs'def, hss]
  calc g * (s : X) = g * s * g⁻¹ * g := by group
    _ = s * g := by rw [h1]

theorem mem_centralizer_of_commute_chevQuotHom (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {J : Subgroup X} (hJS : J ≤ S) (hJ : ⁅J, J⁆ = J)
    {s : ↥S} (hc : ∀ j : ↥S, (j : X) ∈ J → Commute (chevQuotHom 3 S s) (chevQuotHom 3 S j)) :
    (s : X) ∈ Subgroup.centralizer (J : Set X) := by
  set Q : Subgroup X := (Subgroup.center ↥S).map S.subtype
  have hQ : ⁅J, Subgroup.zpowers (s : X)⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro j hj o ho
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ho
    have hmem : ⁅(⟨j, hJS hj⟩ : ↥S), s ^ k⁆ ∈ Subgroup.center ↥S := by
      refine ker_chevQuotHom_le_center_of_core hS hcore ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow,
        commutatorElement_eq_one_iff_mul_comm]
      exact ((hc ⟨j, hJS hj⟩ hj).symm.zpow_right k).eq
    exact ⟨_, hmem, rfl⟩
  have hcent : ∀ q ∈ Q, ∀ j ∈ J, q * j = j * q := by
    rintro _ ⟨c, hc', rfl⟩ j hj
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc' ⟨j, hJS hj⟩)).symm
  have hbot := CFSG.HardMathSupport.Solomon.Coordinator.commutator_eq_bot_of_perfect_of_le hJ hQ
    hcent
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : ⁅j, (s : X)⁆ ∈ ⁅J, Subgroup.zpowers (s : X)⁆ :=
    Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers _)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem chevQuotHom_eq_one_of_le_of_core (hS : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {K : Subgroup X} (hKS : K ≤ S) {k : X} (hk : k ∈ K)
    (h1 : chevQuotHom 3 S ⟨k, hKS hk⟩ = 1) : chevQuotHom 3 K ⟨k, hk⟩ = 1 := by
  have hc := Subgroup.mem_center_iff.1 (ker_chevQuotHom_le_center_of_core hS hcore h1)
  have hcK : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (congrArg (Subtype.val : ↥S → X) (hc ⟨y, hKS y.2⟩))
  show QuotientGroup.mk' (Subgroup.center (PQuot 3 K)) (pQuotHom 3 K ⟨k, hk⟩) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.map_center_le_center (pQuotHom_surjective 3 K) ⟨_, hcK, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
