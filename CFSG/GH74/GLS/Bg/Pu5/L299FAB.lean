module

public import CFSG.GH74.GLS.Bg.Pu5.L299Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exp_two_of_card_four {Q : Subgroup G} (hQ4 : Nat.card ↥Q = 4)
    (hnc : ¬ IsCyclic ↥Q) : ∀ q ∈ Q, q * q = 1 := by
  intro q hq
  have hdvd : orderOf (⟨q, hq⟩ : ↥Q) ∣ 2 ^ 2 := by
    have := orderOf_dvd_natCard (⟨q, hq⟩ : ↥Q)
    rw [hQ4, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
    exact this
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases j
  · have h1 : (⟨q, hq⟩ : ↥Q) = 1 := orderOf_eq_one_iff.mp (by simpa using hjo)
    have h2 : q = 1 := congrArg Subtype.val h1
    rw [h2, mul_one]
  · have h2 : (⟨q, hq⟩ : ↥Q) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (⟨q, hq⟩ : ↥Q)
      rwa [show orderOf (⟨q, hq⟩ : ↥Q) = 2 by simpa using hjo] at this
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  · exact absurd (isCyclic_of_orderOf_eq_card (⟨q, hq⟩ : ↥Q)
      (by rw [hQ4]; simpa using hjo)) hnc

omit [Finite G] in
theorem exists_ne_of_card_four {Q : Subgroup G} (hQ4 : Nat.card ↥Q = 4) {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : ∃ w ∈ Q, w ≠ 1 ∧ w ≠ z := by
  by_contra h
  push Not at h
  have hle : Q ≤ Subgroup.zpowers z := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    · rw [h w hw hw1]
      exact Subgroup.mem_zpowers z
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have := Subgroup.card_dvd_of_le hle
  rw [hQ4, Nat.card_zpowers, hz2'] at this
  omega

variable {z t : G} {S : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_pair_inf {K : Subgroup G} {g : G} (hz : g * z = z * g) (ht : g * t = t * g)
    (hg : g ∈ cSec K) : g ∈ centralizer ({z, t} : Set G) ⊓ cSec K := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨⟨hz.symm, ht.symm⟩, hg⟩

theorem t_conj_w (h44 : II4_44) (hquat : II4_4_quat) (h296 : L296) (hC : Cfg G z t S)
    (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) (hexp : ∀ q ∈ S ⊓ cSec K, q * q = 1) {w : G}
    (hwQ : w ∈ S ⊓ cSec K) (hw1 : w ≠ 1) (hwz : w ≠ z) : t * w * t⁻¹ = z * w := by
  have hz2 : z * z = 1 := hC.z_mul_self
  have ht2 : t * t = 1 := hC.t_mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzQ : z ∈ S ⊓ cSec K := hC.z_mem_Q h44 hquat hK
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.1 hC.tC).symm
  have hSC : S ≤ centralizer ({z} : Set G) := hC.sylow.le
  have hwz' : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.1 (hSC hwQ.1)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hexp w hwQ) hw1
  have hzD : z ∈ centralizer ({z, t} : Set G) ⊓ cSec K := mem_centralizer_pair_inf rfl hzt hzQ.2
  obtain ⟨u, hu⟩ : ∃ u : G, u = t * w * t⁻¹ * w⁻¹ := ⟨_, rfl⟩
  have huQ : u ∈ S ⊓ cSec K := by
    rw [hu]
    exact mul_mem (Q_conj hC hcard hK hC.tS hwQ) (inv_mem hwQ)
  have huu : u * u = 1 := hexp u huQ
  have hu1 : u ≠ 1 := by
    intro h1
    have hwt : w * t = t * w := (commutatorElement_eq_one_iff_mul_comm.1 (by rw [hu] at h1; exact h1)).symm
    have hwD : w ∈ centralizer ({z, t} : Set G) ⊓ cSec K := mem_centralizer_pair_inf hwz' hwt hwQ.2
    exact hwz (eq_of_commuting_involutions h296 hC hK hwD hzD hw2 hC.hz hwz')
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have e1 : u = t * w * t * w⁻¹ := by rw [hu, htinv]
  have e2 : u = w * t * w⁻¹ * t := by
    have h : u = u⁻¹ := (inv_eq_of_mul_eq_one_right huu).symm
    rw [h, e1]
    simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
  have hut : u * t = t * u := by
    calc u * t = (w * t * w⁻¹ * t) * t := by rw [← e2]
      _ = w * t * w⁻¹ * (t * t) := by group
      _ = w * t * w⁻¹ := by rw [ht2, mul_one]
      _ = t * (t * w * t * w⁻¹) := by
        calc w * t * w⁻¹ = (t * t) * w * t * w⁻¹ := by rw [ht2, one_mul]
          _ = t * (t * w * t * w⁻¹) := by group
      _ = t * u := by rw [← e1]
  have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.1 (hSC huQ.1)
  have huD : u ∈ centralizer ({z, t} : Set G) ⊓ cSec K := mem_centralizer_pair_inf huz hut huQ.2
  have huzeq : u = z := eq_of_commuting_involutions h296 hC hK huD hzD hu2 hC.hz huz
  rw [huzeq] at hu
  rw [← mul_inv_eq_iff_eq_mul]
  exact hu.symm

theorem exists_inverted_rigid (h44 : II4_44) (hquat : II4_4_quat) (hAut : II4_Aut) (h296 : L296)
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    ∃ v ∈ S ⊓ K, orderOf v = 4 ∧ t * v * t⁻¹ = v⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN : t ∈ normalizer (K : Set G) := mem_normalizer_of_ncard_one hcard hK hC.tC
  have hSyl : IsSylowOf 2 (S ⊓ K) K := rr_sylow hK hC.sylow
  have hS : IsSylow2In (S ⊓ K) K := isSylowOf_iff.1 hSyl
  have hSt : ∀ a ∈ S ⊓ K, t * a * t⁻¹ ∈ S ⊓ K := fun a ha =>
    ⟨S.mul_mem (S.mul_mem hC.tS ha.1) (S.inv_mem hC.tS), (mem_normalizer_iff.1 htN a).1 ha.2⟩
  have hφ1 : phi K t htN ≠ 1 := fun h =>
    hC.t_not_mem_cSec h44 hquat h296 hK ((phi_eq_one_iff K htN).1 h)
  have hφ2 := phi_mul_self K htN hC.t_mul_self
  have hQ := h44 G hC.simple z hC.hz K (rr_pcomp hK) hK.2
  obtain ⟨wb, hwbP, hwbo, hwbφ⟩ :=
    (((hAut (Hat K) hQ).2.2 (phi K t htN) hφ2).1 hφ1 (hatImg K (S ⊓ K)) (isSylow2In_hatImg hS)
      (fun p hp => phi_mem_hatImg htN hSt hp))
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.mp hwbP
  have hSL : S ⊓ K ≤ K := hS.1
  have hSp : IsPGroup 2 ↥(S ⊓ K) := hS.2.1
  have ha4 : orderOf (a : G) = 4 := by
    have := orderOf_hatMk hSL hSp haS
    rw [← this]
    exact hwbo
  refine ⟨a, haS, ha4, ?_⟩
  apply eq_of_hatMk_eq hSL hSp (hSt _ haS) (inv_mem haS)
  rw [← phi_mk K htN a, hwbφ, ← map_inv]
  rfl

theorem Cfg.z_mem_K (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) : z ∈ K := by
  have := hC.hzK
  rwa [rigidProduct_eq_of_ncard_one hcard hK] at this

theorem exists_v (h44 : II4_44) (hquat : II4_4_quat) (hAut : II4_Aut) (h296 : L296)
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    ∃ v ∈ S ⊓ K, orderOf v = 4 ∧ t * v * t⁻¹ = v⁻¹ ∧ v * v = z ∧
      ∀ q ∈ S ⊓ cSec K, v * q = q * v := by
  obtain ⟨v, hvSK, hv4, hvt⟩ := exists_inverted_rigid h44 hquat hAut h296 hC hcard hK
  have hP : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n :=
    hquat G hC.simple z hC.hz S K hC.sylow (rr_pcomp hK) hK.2
  obtain ⟨z₀, ψ, hz₀P, hz₀sq, hz₀1, hz₀c, hz₀u, -⟩ := quat_data hP
  have hzP : z ∈ S ⊓ K := ⟨hC.z_mem_S, hC.z_mem_K hcard hK⟩
  have hz1 : z ≠ 1 := by
    intro h
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  have hzz₀ : z = z₀ := (hz₀u z hzP hC.z_mul_self).resolve_left hz1
  have hv2P : v * v ∈ S ⊓ K := mul_mem hvSK hvSK
  have hv4' : (v * v) * (v * v) = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv4] at this
    have e : v ^ 4 = (v * v) * (v * v) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rwa [e] at this
  have hv21 : v * v ≠ 1 := by
    intro h
    have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hv4] at h2
    omega
  refine ⟨v, hvSK, hv4, hvt, ?_, fun q hq => ?_⟩
  · rw [hzz₀]
    exact (hz₀u _ hv2P hv4').resolve_left hv21
  · exact comm_of_mem_cSec hC.sylow.isPGroup hvSK.1 hq.1 hvSK.2 hq.2

theorem four_data (h44 : II4_44) (hquat : II4_4_quat) (hAut : II4_Aut) (h296 : L296)
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) (hQ4 : Nat.card ↥(S ⊓ cSec K) = 4)
    (hQnc : ¬ IsCyclic ↥(S ⊓ cSec K)) :
    ∃ v w : G, v ∈ S ⊓ K ∧ w ∈ S ⊓ cSec K ∧ orderOf v = 4 ∧ t * v * t⁻¹ = v⁻¹ ∧ v * v = z ∧
      w * w = 1 ∧ w ≠ 1 ∧ w ≠ z ∧ v * w = w * v ∧ t * w * t⁻¹ = z * w := by
  have hexp := exp_two_of_card_four hQ4 hQnc
  have hz1 : z ≠ 1 := by
    intro h
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  obtain ⟨w, hwQ, hw1, hwz⟩ := exists_ne_of_card_four (Q := S ⊓ cSec K) hQ4 hC.z_mul_self hz1
  obtain ⟨v, hvSK, hv4, hvt, hvv, hvc⟩ := exists_v h44 hquat hAut h296 hC hcard hK
  exact ⟨v, w, hvSK, hwQ, hv4, hvt, hvv, hexp w hwQ, hw1, hwz, hvc w hwQ,
    t_conj_w h44 hquat h296 hC hcard hK hexp hwQ hw1 hwz⟩

end CFSG.GH74.GLS.Bg.Pu5
