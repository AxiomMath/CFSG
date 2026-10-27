module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup
open scoped commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

@[expose] def Sec5C6 (L K₁ K₂ : Subgroup G) : Subgroup G :=
  twoCoreIn (K₁ ⊔ K₂) ⊔ (normalizer (L : Set G) ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

private theorem s888_mul_comm_of_commutator_mem_zpowers {o q z : G} (hz2 : z * z = 1)
    (hoz : o * z = z * o) (hodd : Odd (orderOf o))
    (hc : o * q * o⁻¹ * q⁻¹ ∈ zpowers z) : q * o = o * q := by
  have hc' : ⁅o, q⁆ ∈ zpowers z := hc
  have hco : Commute o ⁅o, q⁆ := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hc'
    rw [commute_iff_eq, ← ha]
    exact (((commute_iff_eq o z).mpr hoz).zpow_right a).eq
  have hc2 : ⁅o, q⁆ * ⁅o, q⁆ = 1 := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hc'
    rw [← ha, ← zpow_add, show a + a = 2 * a by ring, zpow_mul, zpow_two, hz2, one_zpow]
  have hceq : ⁅o, q⁆ ^ orderOf o = ⁅o, q⁆ := by
    obtain ⟨s, hs⟩ := hodd
    rw [hs, pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul]
  have hpow : ⁅o, q⁆ ^ orderOf o = (1 : G) := by
    rw [hco.commutatorElement_pow_left, pow_orderOf_eq_one, commutatorElement_one_left]
  rw [hceq] at hpow
  exact (commutatorElement_eq_one_iff_mul_comm.mp hpow).symm

theorem oddCoreIn_centralizer_le (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (h52a : Asc82Lemma52a) (hF3 : Asc82FactOm6CentD) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (L : Set G) := by
  classical
  have hq := sec5b517_quad h514 c
  have hQeq : Qsub K₁ K₂ h = Sec5B517Q8 hq := by
    rw [sec5b517_Qsub_eq, hq.core_eq]
  have hO_le_C : oddCoreIn (centralizer ({t} : Set G)) ≤
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) := by
    rw [← h516a G t L S z r B A K₁ K₂ h c]
    exact le_sup_right
  have hO_cent_Q : oddCoreIn (centralizer ({t} : Set G)) ≤
      centralizer (Qsub K₁ K₂ h : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro q hqQ
    exact s888_mul_comm_of_commutator_mem_zpowers c.z_mul_self
      (Subgroup.mem_centralizer_singleton_iff.mp (hO_le_C ho).2.1)
      (odd_orderOf_of_mem_oddCoreIn ho) ((hO_le_C ho).2.2.2 q hqQ)
  have hpair : twoCoreIn (K₁ ⊔ K₂) ≤ Qsub K₁ K₂ h := by
    have hpair_eq := Sec5B517Q8.twoCoreIn_sup_eq_pair hq (i := 0) (j := 1) (by decide)
    rw [show Kfam5 K₁ K₂ h 0 = K₁ by simp [Kfam5],
      show Kfam5 K₁ K₂ h 1 = K₂ by simp [Kfam5]] at hpair_eq
    rw [hpair_eq, hQeq]
    exact inf_le_left
  have hO_le_NL : oddCoreIn (centralizer ({t} : Set G)) ≤ normalizer (L : Set G) := by
    intro o ho
    exact sec5b513_conjugate_eq_iff.mp (sec5_conj_L h52a c ((oddCoreIn_normal _).1 ho))
  have hY : oddCoreIn (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G) ⊓
        centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) :=
    le_inf hO_le_NL (le_trans hO_cent_Q (Subgroup.centralizer_le (fun _ hx => hpair hx)))
  have hdiv8 : (centralizer (L : Set G)).relIndex
      (oddCoreIn (centralizer ({t} : Set G))) ∣ 8 :=
    hF3 G L z K₁ K₂ c.toSec5Setting.isOm6Z2 (sec5b517_oddCore_bot c) c.pocket.1
      c.pocket₁ c.pocket₂ c.ne c.comm c.prod (oddCoreIn (centralizer ({t} : Set G))) hY
  have hrel_one : (centralizer (L : Set G)).relIndex
      (oddCoreIn (centralizer ({t} : Set G))) = 1 := by
    have hoddrel : Odd ((centralizer (L : Set G)).relIndex
        (oddCoreIn (centralizer ({t} : Set G)))) :=
      (odd_card_oddCoreIn (centralizer ({t} : Set G))).of_dvd_nat
        (Subgroup.relIndex_dvd_card (centralizer (L : Set G))
          (oddCoreIn (centralizer ({t} : Set G))))
    have hcop : Nat.Coprime 8 ((centralizer (L : Set G)).relIndex
        (oddCoreIn (centralizer ({t} : Set G)))) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact (hoddrel.coprime_two_left).pow_left 3
    exact Nat.eq_one_of_dvd_coprimes hcop hdiv8 dvd_rfl
  exact Subgroup.relIndex_eq_one.mp hrel_one

end CFSG.OddStandard.SmallF3.Omega
