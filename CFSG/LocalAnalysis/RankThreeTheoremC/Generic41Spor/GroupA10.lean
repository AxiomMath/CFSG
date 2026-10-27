module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Sig
import CFSG.RankThree.PartOne.KP.SporadicDefs
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

structure A10Facts : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → SylowIsPlane 5 K
  noOuter : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → NoOuterP 5 K
  noFixed : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → NormalizerNoFixed 5 K
  orbits : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10LineOrbits K
  sigTriv : SignalizerTrivialX IsA10Type 5
  lemma45 : Lemma45Facts IsA10Type 5 A10Shape

theorem a10Sylow_perm_orderOf_dvd (σ : Equiv.Perm (Fin 10)) : orderOf σ ∣ 2520 := by
  rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro b hb
  have h2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hb
  have hle : b ≤ σ.support.card := Equiv.Perm.le_card_support_of_mem_cycleType hb
  have hcard : σ.support.card ≤ 10 := by
    simpa using Finset.card_le_univ σ.support
  have hb10 : b ≤ 10 := le_trans hle hcard
  interval_cases b <;> norm_num

theorem a10Sylow_factorization_five : Nat.factorization 1814400 5 = 2 := by
  have hp : Nat.Prime 5 := Nat.prime_five
  have h2 : 5 ^ 2 ∣ 1814400 := by norm_num
  have h3 : ¬ 5 ^ 3 ∣ 1814400 := by norm_num
  have h0 : (1814400 : ℕ) ≠ 0 := by norm_num
  have hle1 : 2 ≤ Nat.factorization 1814400 5 := (hp.pow_dvd_iff_le_factorization h0).1 h2
  have hle2 : ¬ 3 ≤ Nat.factorization 1814400 5 :=
    fun h => h3 ((hp.pow_dvd_iff_le_factorization h0).2 h)
  omega

theorem a10_sylow : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → SylowIsPlane 5 K := by
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  have e' : K ≃* alternatingGroup (Fin 10) := e
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card K = 1814400 := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hdvd : ∀ x : K, orderOf x ∣ 2520 := by
    intro x
    rw [← MulEquiv.orderOf_eq e' x, ← Subgroup.orderOf_coe]
    exact a10Sylow_perm_orderOf_dvd _
  intro S
  have hS : Nat.card (S : Subgroup K) = 5 ^ 2 := by
    rw [Sylow.card_eq_multiplicity S, hcard, a10Sylow_factorization_five]
  refine ⟨?_, hS⟩
  unfold IsElemAbelian
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hS, ?_⟩
  intro x hx
  have h25 : orderOf x ∣ 5 ^ 2 := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : (S : Subgroup K))
    rw [hS, Subgroup.orderOf_mk] at h
    exact h
  have h5 : orderOf x ∣ 5 := by
    have h := Nat.dvd_gcd h25 (hdvd x)
    have hg : Nat.gcd (5 ^ 2) 2520 = 5 := by norm_num
    rw [hg] at h
    exact h
  exact orderOf_dvd_iff_pow_eq_one.mp h5

theorem a10_noOuter : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → NoOuterP 5 K := by
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  have e' : K ≃* alternatingGroup (Fin 10) := e
  unfold NoOuterP
  rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e']
  exact CFSG.RankThree.PartOne.not_dvd_outer_alternating Nat.prime_five (by norm_num)
    (by norm_num)

theorem a10Facts_holds : A10Facts :=
  ⟨a10_sylow, a10_noOuter, a10_noFixed, a10_orbits, a10_sigTriv, a10_lemma45⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
