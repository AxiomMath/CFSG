module

public import CFSG.GH74.GLS.Bg.Iii2.QuatBasic
public import CFSG.GH74.GLS.IVK.Lifted.IIAutC

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rr_pcomp {x : G} {K : Subgroup G} (h : IsRigidRankOneComp x K) :
    IsPCompIn 2 (centralizer ({x} : Set G)) K := h.1.1.2.2

omit [Finite G] in
theorem rr_ord {x : G} {K : Subgroup G} (h : IsRigidRankOneComp x K) : orderOf x = 2 := h.1.1.1

theorem isSylowTwoOf_iff' {S H : Subgroup G} :
    QuasithinUnique.IsSylowTwoOf S H ↔ IsSylowOf 2 S H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  rfl

theorem rr_sylow {x : G} {K T : Subgroup G} (hK : IsRigidRankOneComp x K)
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) : IsSylowOf 2 (T ⊓ K) K := by
  have hKC := rr_pcomp hK
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hT' : QuasithinUnique.IsSylowTwoOf T (centralizer ({x} : Set G)) := isSylowTwoOf_iff'.2 hT
  exact isSylowTwoOf_iff'.1 (QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT' hKC.1 hsub)

theorem inf_pPrimeCoreOf_eq_bot {T X : Subgroup G} (hT : IsPGroup 2 ↥T) :
    T ⊓ pPrimeCoreOf 2 X = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgT, hgX⟩
  rw [Subgroup.mem_bot]
  obtain ⟨g', hg', rfl⟩ := hgX
  obtain ⟨k, hk⟩ := hT ⟨(g' : G), hgT⟩
  have hk' : (g' : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥X)) := pPrimeCore_coprime_card
  have h1 : orderOf g' ∣ Nat.card (pPrimeCore 2 ↥X) := by
    have := orderOf_dvd_natCard (⟨g', hg'⟩ : ↥(pPrimeCore 2 ↥X))
    simpa using this
  have h2 : orderOf g' ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hk'
  have h3 : Nat.Coprime (orderOf g') 2 :=
    (Nat.Coprime.coprime_dvd_left h1 hcop.symm)
  have h4 : orderOf g' = 1 := by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h3) h2
    exact this
  have : g' = 1 := orderOf_eq_one_iff.1 h4
  simp [this]

omit [Finite G] in
theorem mem_pPrimeCoreOf_iff {K : Subgroup G} {g : G} :
    g ∈ pPrimeCoreOf 2 K ↔ ∃ h : g ∈ K, (⟨g, h⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
  unfold pPrimeCoreOf
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem rr_inv_mem_cSec (h44 : II4_44) (hG : IsKProperSimple G) {x : G} {K : Subgroup G}
    (hK : IsRigidRankOneComp x K) {z : G} (hzK : z ∈ K) (hz2 : orderOf z = 2) : z ∈ cSec K := by
  have hQ := h44 G hG x (rr_ord hK) K (rr_pcomp hK) hK.2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hzo : orderOf (π ⟨z, hzK⟩) = 2 := by
    have h1 : orderOf (π ⟨z, hzK⟩) ∣ orderOf z := by
      have := orderOf_map_dvd π (⟨z, hzK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk] at this
    rw [hz2] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exfalso
      have h2 : π ⟨z, hzK⟩ = 1 := orderOf_eq_one_iff.1 h
      have h3 : (⟨z, hzK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h2
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
      have h4 : orderOf (⟨⟨z, hzK⟩, h3⟩ : ↥(pPrimeCore 2 ↥K)) ∣ Nat.card (pPrimeCore 2 ↥K) :=
        orderOf_dvd_natCard _
      have h5 : orderOf (⟨⟨z, hzK⟩, h3⟩ : ↥(pPrimeCore 2 ↥K)) = 2 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2]
      rw [h5] at h4
      have := Nat.Coprime.eq_one_of_dvd hcop h4
      omega
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K))) 2
    (by rw [hQ.2])
  have hc2' : orderOf (c : ↥K ⧸ pPrimeCore 2 ↥K) = 2 := by rw [Subgroup.orderOf_coe]; exact hc2
  have hπz : π ⟨z, hzK⟩ = (c : ↥K ⧸ pPrimeCore 2 ↥K) := unique_involution_of_sl2or2a7 hQ hzo hc2'
  have hccent : ∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * (c : ↥K ⧸ pPrimeCore 2 ↥K) = (c : ↥K ⧸ pPrimeCore 2 ↥K) * g :=
    Subgroup.mem_center_iff.1 c.2
  show z ∈ normalizer (K : Set G) ∧ z ∈ normalizer (pPrimeCoreOf 2 K : Set G) ∧
    ∀ k ∈ K, ⁅k, z⁆ ∈ pPrimeCoreOf 2 K
  refine ⟨Subgroup.le_normalizer hzK, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hhK, hh'⟩ := mem_pPrimeCoreOf_iff.1 hh
      have hconj : (⟨z, hzK⟩ : ↥K) * ⟨h, hhK⟩ * (⟨z, hzK⟩ : ↥K)⁻¹ ∈ pPrimeCore 2 ↥K :=
        (pPrimeCore_normal (p := 2) (G := ↥K)).conj_mem _ hh' _
      exact mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (K.mul_mem hzK hhK) (K.inv_mem hzK), hconj⟩
    · intro hh
      obtain ⟨hhK, hh'⟩ := mem_pPrimeCoreOf_iff.1 hh
      have hconj : (⟨z, hzK⟩ : ↥K)⁻¹ * ⟨z * h * z⁻¹, hhK⟩ * (⟨z, hzK⟩ : ↥K)⁻¹⁻¹ ∈ pPrimeCore 2 ↥K :=
        (pPrimeCore_normal (p := 2) (G := ↥K)).conj_mem _ hh' _
      have e : z⁻¹ * (z * h * z⁻¹) * z = h := by group
      have hh2 : (h : G) ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hzK) hhK) hzK
        rwa [e] at this
      refine mem_pPrimeCoreOf_iff.2 ⟨hh2, ?_⟩
      convert hconj using 1
      apply Subtype.ext
      simp [e]
  · intro k hk
    refine mem_pPrimeCoreOf_iff.2 ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem hk hzK) (K.inv_mem hk)) (K.inv_mem hzK)
    · apply (QuotientGroup.eq_one_iff _).1
      show π ⁅(⟨k, hk⟩ : ↥K), ⟨z, hzK⟩⁆ = 1
      rw [map_commutatorElement, hπz]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hccent _)

theorem rr_sylow_comm {x : G} {K K' T : Subgroup G} (hK : IsRigidRankOneComp x K)
    (hK' : IsRigidRankOneComp x K') (hne : K ≠ K')
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) :
    ∀ p ∈ T ⊓ K, ∀ q ∈ T ⊓ K', p * q = q * p := by
  intro p hp q hq
  have h1 : K ≤ cSec K' := le_cSec_of_ne (rr_pcomp hK) (rr_pcomp hK') hne
  have h2 : p ∈ centralizerSection K' (pPrimeCoreOf 2 K') := h1 hp.2
  obtain ⟨-, -, h3⟩ := h2
  have h3' : ⁅q, p⁆ ∈ pPrimeCoreOf 2 K' := h3 q hq.2
  have h4 : ⁅q, p⁆ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hq.1 hp.1) (T.inv_mem hq.1)) (T.inv_mem hp.1)
  have h5 : ⁅q, p⁆ ∈ T ⊓ pPrimeCoreOf 2 K' := ⟨h4, h3'⟩
  rw [inf_pPrimeCoreOf_eq_bot hT.isPGroup, Subgroup.mem_bot] at h5
  exact (commutatorElement_eq_one_iff_mul_comm.1 h5).symm

omit [Finite G] in
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (quaternion_center) in
theorem q8_pair_ker {ψ₁ ψ₂ : QuaternionGroup 2 →* G} (h₁ : Function.Injective ψ₁)
    (h₂ : Function.Injective ψ₂) (hc : ∀ a b, ψ₁ a * ψ₂ b = ψ₂ b * ψ₁ a)
    (g : QuaternionGroup 2 × QuaternionGroup 2) (hg : ψ₁ g.1 * ψ₂ g.2 = 1) :
    g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  have e1 : ψ₁ g.1 = (ψ₂ g.2)⁻¹ := eq_inv_of_mul_eq_one_left hg
  have e2 : ψ₂ g.2 = (ψ₁ g.1)⁻¹ := eq_inv_of_mul_eq_one_right hg
  have hc1 : ∀ m, g.1 * m = m * g.1 := by
    intro m
    apply h₁
    rw [map_mul, map_mul, e1]
    have : ψ₁ m * ψ₂ g.2 = ψ₂ g.2 * ψ₁ m := hc m g.2
    exact ((Commute.inv_right (show Commute (ψ₁ m) (ψ₂ g.2) from this))).eq.symm
  have hc2 : ∀ m, g.2 * m = m * g.2 := by
    intro m
    apply h₂
    rw [map_mul, map_mul, e2]
    have : ψ₁ g.1 * ψ₂ m = ψ₂ m * ψ₁ g.1 := hc g.1 m
    exact ((Commute.inv_left (show Commute (ψ₁ g.1) (ψ₂ m) from this))).eq
  have hne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  rcases quaternion_center g.1 hc1 with a1 | a1
  · left
    have : ψ₂ g.2 = 1 := by rw [a1, map_one, one_mul] at hg; exact hg
    have : g.2 = 1 := h₂ (this.trans (map_one ψ₂).symm)
    exact Prod.ext a1 this
  · rcases quaternion_center g.2 hc2 with b1 | b1
    · exfalso
      rw [a1, b1, map_one, mul_one] at hg
      exact hne (h₁ (hg.trans (map_one ψ₁).symm))
    · right
      exact Prod.ext a1 b1

theorem rr_ncard_le_two (hquat : II4_4_quat) (hG : IsKProperSimple G) (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) : Set.ncard {K : Subgroup G | IsRigidRankOneComp x K} ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hfin : {K : Subgroup G | IsRigidRankOneComp x K}.Finite := Set.toFinite _
  obtain ⟨K₁, K₂, K₃, h1, h2, h3, h12, h13, h23⟩ := (Set.two_lt_ncard_iff hfin).1 hlt
  obtain ⟨T, hT⟩ := exists_isSylowOf (G := G) 2 (centralizer ({x} : Set G))
  have hq : ∀ K, IsRigidRankOneComp x K → ∃ n, IVK.IsQuaternionTwoGroup ↥(T ⊓ K) n :=
    fun K hK => hquat G hG x hx T K hT (rr_pcomp hK) hK.2
  obtain ⟨z₁, ψ₁, -, -, -, -, -, hi₁, hr₁, -, -⟩ := quat_data (hq K₁ h1)
  obtain ⟨z₂, ψ₂, -, -, -, -, -, hi₂, hr₂, -, -⟩ := quat_data (hq K₂ h2)
  obtain ⟨z₃, ψ₃, -, -, -, -, -, hi₃, hr₃, -, -⟩ := quat_data (hq K₃ h3)
  have hc12 : ∀ a b, ψ₁ a * ψ₂ b = ψ₂ b * ψ₁ a := fun a b =>
    rr_sylow_comm h1 h2 h12 hT _ (hr₁ a) _ (hr₂ b)
  have hc13 : ∀ a b, ψ₁ a * ψ₃ b = ψ₃ b * ψ₁ a := fun a b =>
    rr_sylow_comm h1 h3 h13 hT _ (hr₁ a) _ (hr₃ b)
  have hc23 : ∀ a b, ψ₂ a * ψ₃ b = ψ₃ b * ψ₂ a := fun a b =>
    rr_sylow_comm h2 h3 h23 hT _ (hr₂ a) _ (hr₃ b)
  let φ : QuaternionGroup 2 × QuaternionGroup 2 →* G :=
    ψ₁.noncommCoprod ψ₂ fun a b => hc12 a b
  have hφ : ∀ g, φ g = ψ₁ g.1 * ψ₂ g.2 := fun g => rfl
  have hker : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) :=
    fun g hg => q8_pair_ker hi₁ hi₂ hc12 g (by rw [← hφ]; exact hg)
  have hA : IsPGroup 2 ↥(T ⊓ K₃) := (hT.isPGroup).to_inf_left
  have hcomm : ∀ (a : QuaternionGroup 2 × QuaternionGroup 2) (t : G), t ∈ T ⊓ K₃ →
      φ a * t = t * φ a := by
    intro a t ht
    have c2 : ψ₂ a.2 * t = t * ψ₂ a.2 := rr_sylow_comm h2 h3 h23 hT _ (hr₂ a.2) t ht
    have c1 : ψ₁ a.1 * t = t * ψ₁ a.1 := rr_sylow_comm h1 h3 h13 hT _ (hr₁ a.1) t ht
    rw [hφ]
    calc ψ₁ a.1 * ψ₂ a.2 * t = ψ₁ a.1 * (ψ₂ a.2 * t) := mul_assoc _ _ _
      _ = ψ₁ a.1 * (t * ψ₂ a.2) := by rw [c2]
      _ = ψ₁ a.1 * t * ψ₂ a.2 := (mul_assoc _ _ _).symm
      _ = t * ψ₁ a.1 * ψ₂ a.2 := by rw [c1]
      _ = t * (ψ₁ a.1 * ψ₂ a.2) := mul_assoc _ _ _
  have := CFSG.GH74.Generic.q8q8_commuting_two_subgroup_le' hgen φ hker (T ⊓ K₃) hA hcomm
  obtain ⟨g, hg, hgc⟩ := this (ψ₃ (QuaternionGroup.a 1)) (hr₃ _)
  obtain ⟨g', hg', hgc'⟩ := this (ψ₃ (QuaternionGroup.xa 0)) (hr₃ _)
  have hcomm' : ψ₃ (QuaternionGroup.a 1) * ψ₃ (QuaternionGroup.xa 0) =
      ψ₃ (QuaternionGroup.xa 0) * ψ₃ (QuaternionGroup.a 1) := by
    rw [← hg, ← hg', ← map_mul, ← map_mul, hgc g']
  have hfin := hi₃ (show ψ₃ (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
      ψ₃ (QuaternionGroup.xa 0 * QuaternionGroup.a 1) by rw [map_mul, map_mul]; exact hcomm')
  revert hfin
  decide

end CFSG.GH74.GLS.Bg.Iii2
