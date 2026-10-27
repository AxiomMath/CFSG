module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE2
public import CFSG.ClassicalInvolution.Q3.Q3T7Layer

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU.Asc77

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3NL
      CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.T8 (XMem layerRes layerSet layerJoin cenZ
  cenZ_eq_centralizer layerRes_conj layerRes_le layerJoin_le_cenZ le_layerJoin)
open scoped commutatorElement
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem xMem_of_le_centralizer (hΩ : HM MT Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K)
    {w : G} (hRw : R ≤ Subgroup.centralizer ({w} : Set G)) : XMem Ω w K := by
  have hΩg := hΩ.toGen
  have h8 : 8 ≤ Nat.card R :=
    Sec6Gen.eight_le_of_mem_RSet hΩg (mem_RSet_of_isSylow2In hK hR)
  have hRKw : R ≤ conjSub w K := by
    intro r hr
    rw [mem_conjSub_iff]
    have h1 : w * r = r * w := (Subgroup.mem_centralizer_singleton_iff.mp (hRw hr)).symm
    have : w⁻¹ * r * w = r := by rw [mul_assoc, ← h1]; group
    rw [this]
    exact hR.1 hr
  have hwK : conjSub w K = K :=
    Sec6Gen.eq_of_le_of_le hΩg (hΩg.conjInvariant w K hK) hK hR.2.1 (by omega) hRKw hR.1
  exact ⟨hK, mem_normalizer_iff_conjSub_eq.mpr hwK, R, hR,
    fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hRw hr)⟩

end Basic
section NormalTwo
variable {G : Type} [Group G] [Finite G]

theorem commutes_of_commutator_commutes {N : Subgroup G} (hN : IsPGroup 2 N) {y : G}
    (hyN : ∀ g ∈ N, y * g * y⁻¹ ∈ N) (hy : Odd (orderOf y)) {g : G} (hg : g ∈ N)
    (hd : y * (g⁻¹ * (y * g * y⁻¹)) = (g⁻¹ * (y * g * y⁻¹)) * y) : y * g = g * y := by
  have hdN : g⁻¹ * (y * g * y⁻¹) ∈ N := N.mul_mem (N.inv_mem hg) (hyN _ hg)
  obtain ⟨d, hd'⟩ : ∃ d : G, d = g⁻¹ * (y * g * y⁻¹) := ⟨_, rfl⟩
  rw [← hd'] at hdN hd
  have hgd : y * g * y⁻¹ = g * d := by rw [hd']; group
  have hyd' : y * d * y⁻¹ = d := by rw [hd]; group
  have hpow : ∀ k : ℕ, y ^ k * g * (y ^ k)⁻¹ = g * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      have e1 : y ^ (k + 1) * g * (y ^ (k + 1))⁻¹ = y * (y ^ k * g * (y ^ k)⁻¹) * y⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ihk]
      have e2 : y * (g * d ^ k) * y⁻¹ = (y * g * y⁻¹) * (y * d * y⁻¹) ^ k := by
        rw [conj_pow]; group
      rw [e2, hgd, hyd']
      group
  have hk := hpow (orderOf y)
  rw [pow_orderOf_eq_one] at hk
  have hdk : d ^ orderOf y = 1 := by
    have : g = g * d ^ orderOf y := by simpa using hk
    exact (mul_eq_left.mp this.symm)
  have hd1 : d = 1 := by
    obtain ⟨m, hm⟩ := hN.exists_orderOf_eq_pow ⟨d, hdN⟩
    have hm' : orderOf d = 2 ^ m := by rwa [Subgroup.orderOf_mk] at hm
    have hdvd : orderOf d ∣ orderOf y := orderOf_dvd_of_pow_eq_one hdk
    have hodd : Odd (orderOf d) := hy.of_dvd_nat hdvd
    rw [hm'] at hodd
    have hm0 : m = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
    rw [hm0, pow_zero] at hm'
    exact orderOf_eq_one_iff.mp hm'
  rw [hd1, mul_one] at hgd
  calc y * g = y * g * y⁻¹ * y := by group
    _ = g * y := by rw [hgd]

theorem centralizes_of_isSubnormal {Q : Subgroup G} [Q.Normal] (hQ2 : IsPGroup 2 ↥Q) {T : Set G}
    (hT : ∀ x ∈ T, Odd (orderOf x)) {M K : Subgroup G} (h : IsSubnormal M K)
    (hTM : ∀ x ∈ T, x ∈ M) (h0 : ∀ x ∈ T, ∀ q ∈ M ⊓ Q, x * q = q * x) :
    ∀ x ∈ T, ∀ q ∈ K ⊓ Q, x * q = q * x := by
  induction h with
  | refl => exact h0
  | @step H M' K' hHM hHnorm hM'K ih =>
    refine ih (fun x hx => hHM (hTM x hx)) ?_
    intro x hx q hq
    have hxH : x ∈ H := hTM x hx
    have hxM' : x ∈ M' := hHM hxH
    have hP2 : IsPGroup 2 ↥(M' ⊓ Q) := hQ2.to_inf_right
    have hnorm : ∀ g ∈ M' ⊓ Q, x * g * x⁻¹ ∈ M' ⊓ Q := fun g hg =>
      ⟨M'.mul_mem (M'.mul_mem hxM' hg.1) (M'.inv_mem hxM'), ‹Q.Normal›.conj_mem g hg.2 x⟩
    refine commutes_of_commutator_commutes hP2 hnorm (hT x hx) hq ?_
    have hdQ : q⁻¹ * (x * q * x⁻¹) ∈ Q :=
      Q.mul_mem (Q.inv_mem hq.2) (‹Q.Normal›.conj_mem q hq.2 x)
    have hdH : q⁻¹ * (x * q * x⁻¹) ∈ H := by
      have h1 : q⁻¹ * x * (q⁻¹)⁻¹ ∈ H :=
        (Subgroup.normal_subgroupOf_iff hHM).mp hHnorm x q⁻¹ hxH (M'.inv_mem hq.1)
      have e : q⁻¹ * (x * q * x⁻¹) = (q⁻¹ * x * (q⁻¹)⁻¹) * x⁻¹ := by group
      rw [e]
      exact H.mul_mem h1 (H.inv_mem hxH)
    exact h0 x hx _ ⟨hdH, hdQ⟩

end NormalTwo
section Restrict
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H Y : Subgroup G}

theorem MinCex.trans_restrict (c : MinCex MT Ω K S R W H) (hKY : K ≤ Y)
    (hall : ∀ J ∈ restrictFamily Ω Y, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = J) :
    ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ h ∈ H.subgroupOf Y, conjSub h (K.subgroupOf Y) = J := by
  intro J hJ
  have hJΛ : J ∈ restrictFamily Ω Y := by
    rcases dstarComp_subset_insert _ hJ with h | h
    · rw [h]
      exact subgroupOf_mem_restrictFamily c.stand.mem hKY
    · exact h
  obtain ⟨y, rfl⟩ := hall J hJΛ
  refine ⟨y, ?_, rfl⟩
  have h1 := dstarComp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  have h2 : (conjSub y (K.subgroupOf Y)).map Y.subtype = conjSub (y : G) K := by
    rw [conjSub_subgroupOf Y y K, Subgroup.map_subgroupOf_eq_of_le]
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  rw [h2] at h1
  exact Subgroup.mem_subgroupOf.mpr ((e18_1 G Ω K S R W H c).1 y h1)

theorem MinCex.cent_restrict (c : MinCex MT Ω K S R W H) (hKY : K ≤ Y) :
    CentralizersSylowPairs (restrictFamily Ω Y) (K.subgroupOf Y) (H.subgroupOf Y) := by
  exact E187C.cent_restrict_of c.hyp.cent hKY

@[expose] def restrictGood (Ω : Set (Subgroup G)) (Y K : Subgroup G) (L : Subgroup ↥Y) : Prop :=
  ∃ J ∈ Ω, J ≤ Y ∧ L = J.subgroupOf Y ∧ J ∈ dstarComp Ω K

theorem restrictGood_step {K : Subgroup G} {L L' : Subgroup ↥Y}
    (hL' : L' ∈ restrictFamily Ω Y) (hgood : restrictGood Ω Y K L)
    (hadj : dstarAdj (restrictFamily Ω Y) L L') : restrictGood Ω Y K L' := by
  obtain ⟨J, hJ, hJY, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', hJ'Y, rfl⟩ := hL'
  have h1 := dstarAdj_map hadj
  rw [Subgroup.map_subgroupOf_eq_of_le hJY, Subgroup.map_subgroupOf_eq_of_le hJ'Y] at h1
  exact ⟨J', hJ', hJ'Y, rfl, hJK.tail h1⟩

theorem MinCex.restrictGood_le_H (c : MinCex MT Ω K S R W H) {L : Subgroup ↥Y}
    (hgood : restrictGood Ω Y K L) : L.map Y.subtype ≤ H := by
  obtain ⟨J, hJ, hJY, rfl, hJK⟩ := hgood
  rw [Subgroup.map_subgroupOf_eq_of_le hJY]
  exact c.le_H_of_mem_dstarComp hJK

end Restrict
section ExactSection
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G} {w : G}

theorem exists_of_mem_restrict_layerSet {L : Subgroup ↥(layerJoin Ω w)}
    (hL : L ∈ restrictFamily (layerSet Ω w) (layerJoin Ω w)) :
    ∃ J, XMem Ω w J ∧ L = (layerRes w J).subgroupOf (layerJoin Ω w) := by
  obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hL
  exact ⟨J, hJ, rfl⟩

@[expose] def layerGood (Ω : Set (Subgroup G)) (w : G) (K : Subgroup G)
    (L : Subgroup ↥(layerJoin Ω w)) : Prop :=
  ∃ J, XMem Ω w J ∧ L = (layerRes w J).subgroupOf (layerJoin Ω w) ∧ J ∈ dstarComp Ω K

theorem MinCex.layerGood_le_H (c : MinCex MT Ω K S R W H) {L : Subgroup ↥(layerJoin Ω w)}
    (hgood : layerGood Ω w K L) : L.map (layerJoin Ω w).subtype ≤ H := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  rw [Subgroup.map_subgroupOf_eq_of_le (le_layerJoin ⟨J, hJ, rfl⟩)]
  exact (layerRes_le w J).trans (c.le_H_of_mem_dstarComp hJK)

end ExactSection
end CFSG.ClassicalInvolution.T7FU.Asc77
