module

public import CFSG.GH74.GLS.Bg.Pu5.L299MAbs
public import CFSG.GH74.GLS.Bg.Pu5.L299Abs2
public import CFSG.GH74.GLS.Bg.Pu5.L299FC1
public import CFSG.GH74.GLS.Bg.Pu5.L299Swap

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G] {z t : G} {S : Subgroup G}

theorem exists_v_IIb (h44 : II4_44) (hquat : II4_4_quat) (h296 : L296) (hC : Cfg G z t S)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K)
    (hIIb : ∃ q ∈ S ⊓ cSec K, q * t = t * q ∧ q ∉ zpowers z) :
    ∃ v ∈ S ⊓ cSec K, v * t = t * v ∧ orderOf v = 4 ∧ v * v = z := by
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.1 hC.tC).symm
  have hSC : S ≤ centralizer ({z} : Set G) := hC.sylow.le
  have hQ2 : IsPGroup 2 ↥(S ⊓ cSec K) := hC.sylow.isPGroup.to_inf_left
  have hzQ : z ∈ S ⊓ cSec K := hC.z_mem_Q h44 hquat hK
  have hzD : z ∈ centralizer ({z, t} : Set G) ⊓ cSec K := mem_centralizer_pair_inf rfl hzt hzQ.2
  obtain ⟨q₀, hq₀Q, hq₀t, hq₀z⟩ := hIIb
  have hq₀zc : q₀ * z = z * q₀ := Subgroup.mem_centralizer_singleton_iff.1 (hSC hq₀Q.1)
  obtain ⟨n, hn⟩ := hQ2 ⟨q₀, hq₀Q⟩
  have hq₀pow : q₀ ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hq₀pow)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · apply hq₀z
      have h1 : q₀ = 1 := orderOf_eq_one_iff.1 (by simpa using hko)
      rw [h1]
      exact one_mem _
    · have hq₀2 : orderOf q₀ = 2 := by simpa using hko
      have hq₀D : q₀ ∈ centralizer ({z, t} : Set G) ⊓ cSec K :=
        mem_centralizer_pair_inf hq₀zc hq₀t hq₀Q.2
      have := eq_of_commuting_involutions h296 hC hK hq₀D hzD hq₀2 hC.hz hq₀zc
      apply hq₀z
      rw [this]
      exact mem_zpowers z
  set v : G := q₀ ^ (2 ^ (k - 2)) with hvdef
  have hv4 : orderOf v = 4 := by
    rw [hvdef, orderOf_pow_of_dvd (by positivity) (by rw [hko]; exact pow_dvd_pow 2 (by omega)),
      hko]
    have h4 : 2 ^ k = 2 ^ (k - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [h4]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  have hvQ : v ∈ S ⊓ cSec K := pow_mem hq₀Q _
  have hvt : v * t = t * v := (Commute.pow_left (show Commute q₀ t from hq₀t) _).eq
  have hvz : v * z = z * v := Subgroup.mem_centralizer_singleton_iff.1 (hSC hvQ.1)
  have hvv2 : orderOf (v * v) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hv4]; norm_num), hv4]
  have hvvQ : v * v ∈ S ⊓ cSec K := mul_mem hvQ hvQ
  have hvvt : v * v * t = t * (v * v) := by
    rw [mul_assoc, hvt, ← mul_assoc, hvt, mul_assoc]
  have hvvz : v * v * z = z * (v * v) := by
    rw [mul_assoc, hvz, ← mul_assoc, hvz, mul_assoc]
  have hvvD : v * v ∈ centralizer ({z, t} : Set G) ⊓ cSec K :=
    mem_centralizer_pair_inf hvvz hvvt hvvQ.2
  exact ⟨v, hvQ, hvt, hv4, eq_of_commuting_involutions h296 hC hK hvvD hzD hvv2 hC.hz hvvz⟩

theorem l299m_caseIIb (h44 : II4_44) (hquat : II4_4_quat) (h293 : L293) (h296 : L296)
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K)
    (hIIb : ∃ q ∈ S ⊓ cSec K, q * t = t * q ∧ q ∉ zpowers z)
    (hnc : ¬ IsCyclic ↥(S ⊓ cSec K))
    (hnm : ¬ IsNonabelianMaximalClassTwoGroup ↥(S ⊓ cSec K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvQ, hvt, hv4, hvvz⟩ := exists_v_IIb h44 hquat h296 hC hK hIIb
  have hv2 : ∃ k : ℕ, v ^ (2 ^ k) = 1 := ⟨2, by
    have := pow_orderOf_eq_one v
    rwa [hv4] at this⟩
  obtain ⟨S', hC', hcard', hiso⟩ := cfg_swap_data h44 hquat h293 hC hcard
  obtain ⟨K', hK'⟩ := rigid_nonempty hC'.hz hC'.hzK
  obtain ⟨e1⟩ := hiso K hK K' hK'
  have hvCt : v ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hvt
  have hvK' : v ∈ normalizer (K' : Set G) := mem_normalizer_of_ncard_one hcard' hK' hvCt
  have hvcSec : v ∈ normalizer ((cSec K' : Subgroup G) : Set G) :=
    mem_normalizer_of_forall_conj_mem fun c hc => cSec_conj K' hvK' hc
  set W : Subgroup G := cSec K' ⊓ centralizer ({t} : Set G) with hW
  have hvW : v ∈ normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hvcSec, Subgroup.le_normalizer hvCt⟩
  have hQ'W : S' ⊓ cSec K' ≤ W := fun x hx => ⟨hx.2, hC'.sylow.le hx.1⟩
  have hQ'syl : IsSylowOf 2 (S' ⊓ cSec K') W :=
    (isSylowOf_inf_cSec hC' hcard' hK').of_le hQ'W inf_le_left
  obtain ⟨T, hT, hvT⟩ := exists_isSylowOf_ge' (K := W ⊔ zpowers v) (X := zpowers v) (le_sup_right)
    (isPGroup_zpowers_of_pow_eq_one hv2)
  have hWN : W ⊔ zpowers v ≤ normalizer (W : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) (zpowers_le.2 hvW)
  have hQstar : IsSylowOf 2 (T ⊓ W) W := hT.inf_of_le_normalizer le_sup_left hWN
  have hvTmem : v ∈ T := hvT (Subgroup.mem_zpowers v)
  have hvQstar : v ∈ normalizer ((T ⊓ W : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hvTmem, hvW⟩
  obtain ⟨e2⟩ := exists_mulEquiv_of_isSylowOf_two hQstar hQ'syl
  let e : ↥(T ⊓ W) ≃* ↥(S ⊓ cSec K) := e2.trans e1.symm
  have hQnc : ¬ IsCyclic ↥(T ⊓ W) := fun h => hnc (e.isCyclic.1 h)
  have hQnm : ¬ IsNonabelianMaximalClassTwoGroup ↥(T ⊓ W) := fun h =>
    hnm (isNonabelianMaximalClassTwoGroup_of_mulEquiv e h)
  obtain ⟨U, hUQ, hU4, hUexp, hvU⟩ := exists_four_normalized hQstar.isPGroup hvQstar hv2 hQnc hQnm
  have hzU : ∀ u ∈ U, u * z = z * u := by
    intro u hu
    have := sq_centralizes_of_normalizes_four hU4 hvU hv2 u hu
    rw [hvvz] at this
    exact this.symm
  have hUW : U ≤ W := hUQ.trans inf_le_right
  have hUnt : Nontrivial ↥U := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨a', ha'⟩ := exists_ne (1 : ↥U)
  have ha1 : (a' : G) ≠ 1 := fun h => ha' (Subtype.ext h)
  obtain ⟨b, hbU, hb1, hba⟩ := exists_ne_of_card_four (Q := U) hU4 (hUexp a' a'.2) ha1
  have ha2 : orderOf (a' : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hUexp a' a'.2) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hUexp b hbU) hb1
  have hmemD : ∀ u ∈ U, u ∈ centralizer ({t, z} : Set G) ⊓ cSec K' := fun u hu =>
    mem_centralizer_pair_inf (z := t) (t := z) (Subgroup.mem_centralizer_singleton_iff.1 (hUW hu).2)
      (hzU u hu) (hUW hu).1
  have hcomm : (a' : G) * b = b * a' := comm_of_exp_two hUexp a'.2 hbU
  exact hba (eq_of_commuting_involutions h296 hC' hK' (hmemD a' a'.2) (hmemD b hbU) ha2 hb2 hcomm).symm

end CFSG.GH74.GLS.Bg.Pu5
