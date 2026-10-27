module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617D
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem exists_mem_normalizer_of_lt {S T : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T < S) :
    ∃ a ∈ S, a ∈ normalizer (T : Set G) ∧ a ∉ T := by
  classical
  have hTle : T ≤ S := hTS.le
  let I : Subgroup ↥S := T.subgroupOf S
  have hIne : I ≠ ⊤ := by
    intro htop
    obtain ⟨s, hsS, hsT⟩ := IsConcreteLE.exists_of_lt hTS
    have : (⟨s, hsS⟩ : ↥S) ∈ I := by rw [htop]; trivial
    exact hsT (Subgroup.mem_subgroupOf.1 this)
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have hlt : I < Subgroup.normalizer (I : Set ↥S) := hnc I (lt_of_le_of_ne le_top hIne)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hxT => hxnot (Subgroup.mem_subgroupOf.2 hxT)⟩
  have hxsub : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hTle]
    exact hxN
  exact Subgroup.mem_subgroupOf.1 hxsub

theorem twoPartCard_le_top (H : Subgroup G) : twoPartCard H ≤ twoPartCard (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 H
  have h1 : Nat.card ↥Q = twoPartCard H := hQ.card_eq
  rw [← h1]
  exact Th2.L627.card_le_twoPartCard hQ.isPGroup le_top

theorem conj_x_ne_x (hs : Th2Std x y K T S) {a : G} (haS : a ∈ S) (haT : a ∉ T) :
    a * x * a⁻¹ ≠ x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hax
  have haC : a ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 (by
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hax])
  have hsup : T ⊔ zpowers a ≤ S := sup_le hs.T_le_S (zpowers_le.2 haS)
  have h2 : IsPGroup 2 ↥(T ⊔ zpowers a) := hs.sylowS.isPGroup.to_le hsup
  have hle : T ⊔ zpowers a ≤ centralizer ({x} : Set G) :=
    sup_le hs.T_le_C (zpowers_le.2 haC)
  have hcard : Nat.card ↥(T ⊔ zpowers a) ≤ twoPartCard (centralizer ({x} : Set G)) :=
    Th2.L627.card_le_twoPartCard h2 hle
  have hTcard : Nat.card ↥T = twoPartCard (centralizer ({x} : Set G)) :=
    hs.setup.sylowT.card_eq
  have hTeq : T = T ⊔ zpowers a := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  exact haT (hTeq ▸ mem_sup_right (mem_zpowers a))

omit [Finite G] in
theorem _root_.CFSG.GH74.GLS.Th2.CommDisj.unique {P Q : Subgroup G} (hcd : CommDisj P Q) {p₁ p₂ q₁ q₂ : G} (hp₁ : p₁ ∈ P)
    (hp₂ : p₂ ∈ P) (hq₁ : q₁ ∈ Q) (hq₂ : q₂ ∈ Q) (h : p₁ * q₁ = p₂ * q₂) : p₁ = p₂ ∧ q₁ = q₂ := by
  have h1 : p₂⁻¹ * p₁ = q₂ * q₁⁻¹ := by
    calc p₂⁻¹ * p₁ = p₂⁻¹ * (p₁ * q₁) * q₁⁻¹ := by group
      _ = p₂⁻¹ * (p₂ * q₂) * q₁⁻¹ := by rw [h]
      _ = q₂ * q₁⁻¹ := by group
  have hP : p₂⁻¹ * p₁ ∈ P := P.mul_mem (P.inv_mem hp₂) hp₁
  have hQ : p₂⁻¹ * p₁ ∈ Q := by rw [h1]; exact Q.mul_mem hq₂ (Q.inv_mem hq₁)
  have h2 : p₂⁻¹ * p₁ = 1 := by
    have : p₂⁻¹ * p₁ ∈ P ⊓ Q := ⟨hP, hQ⟩
    rw [hcd.inf] at this
    simpa using this
  have hp : p₁ = p₂ := by
    calc p₁ = p₂ * (p₂⁻¹ * p₁) := by group
      _ = p₂ := by rw [h2, mul_one]
  refine ⟨hp, ?_⟩
  subst hp
  exact mul_left_cancel h


theorem card_le_four_of_proper {P C : Subgroup G} (hP8 : Nat.card ↥P = 8) (hCP : C ≤ P)
    (hne : C ≠ P) : Nat.card ↥C ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥C ∣ 2 ^ 3 := by
    have h8 : (2 : ℕ) ^ 3 = Nat.card ↥P := by rw [hP8]; norm_num
    rw [h8]
    exact Subgroup.card_dvd_of_le hCP
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hcon
  push Not at hcon
  have hi3 : i = 3 := by
    by_contra hne3
    have : i ≤ 2 := by omega
    have : 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  apply hne
  refine Subgroup.eq_of_le_of_card_ge hCP ?_
  rw [hP8, hi', hi3]
  norm_num

theorem conj_ne_zx {P Q T : Subgroup G} {z x c : G} (hcd : CommDisj P Q)
    (hdec : ∀ s ∈ T, ∃ p ∈ P, ∃ q ∈ Q, s = p * q) (hPT : P ≤ T) (hQT : Q ≤ T)
    (hP8 : Nat.card ↥P = 8) (hQ8 : Nat.card ↥Q = 8)
    (hzP : z ∈ P) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzu : ∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxx : x * x = 1)
    (hxu : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = x)
    (hcQ : c ∈ Q) (hcc : c * c = x) {a : G} (ha : a ∈ normalizer (T : Set G)) :
    a * x * a⁻¹ ≠ z * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hax
  have hainv : a⁻¹ ∈ normalizer (T : Set G) := Subgroup.inv_mem _ ha
  have hconjT : ∀ g ∈ T, a * g * a⁻¹ ∈ T := fun g hg => (Subgroup.mem_normalizer_iff.1 ha g).1 hg
  have hconjT' : ∀ g ∈ T, a⁻¹ * g * a ∈ T := fun g hg => by
    have := (Subgroup.mem_normalizer_iff.1 hainv g).1 hg
    simpa using this
  set t₀ : G := a * c * a⁻¹ with ht₀
  have ht₀T : t₀ ∈ T := hconjT c (hQT hcQ)
  obtain ⟨p, hp, q, hq, hpq⟩ := hdec t₀ ht₀T
  have hsq : t₀ * t₀ = z * x := by
    rw [← hax]
    calc t₀ * t₀ = a * (c * c) * a⁻¹ := by rw [ht₀]; group
      _ = a * x * a⁻¹ := by rw [hcc]
  have hexp : (p * q) * (p * q) = p * p * (q * q) := by
    calc (p * q) * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [← hcd.comm p hp q hq]
      _ = p * p * (q * q) := by group
  have hpq2 : p * p * (q * q) = z * x := by rw [← hexp, ← hpq]; exact hsq
  obtain ⟨hpp, hqq⟩ := hcd.unique (P.mul_mem hp hp) hzP (Q.mul_mem hq hq) hxQ hpq2
  have hCp : Nat.card ↥(P ⊓ centralizer ({p} : Set G)) ≤ 4 := by
    refine card_le_four_of_proper hP8 inf_le_left ?_
    intro h
    have hcomm : ∀ p' ∈ P, p' * p = p * p' := fun p' hp' => by
      have : p' ∈ P ⊓ centralizer ({p} : Set G) := by rw [h]; exact hp'
      exact mem_centralizer_singleton_iff.1 this.2
    rcases hzu p hp hcomm with h1 | h1
    · rw [h1, one_mul] at hpp
      exact hz1 hpp.symm
    · rw [h1, hzz] at hpp
      exact hz1 hpp.symm
  have hCq : Nat.card ↥(Q ⊓ centralizer ({q} : Set G)) ≤ 4 := by
    refine card_le_four_of_proper hQ8 inf_le_left ?_
    intro h
    have hcomm : ∀ q' ∈ Q, q' * q = q * q' := fun q' hq' => by
      have : q' ∈ Q ⊓ centralizer ({q} : Set G) := by rw [h]; exact hq'
      exact mem_centralizer_singleton_iff.1 this.2
    rcases hxu q hq hcomm with h1 | h1
    · rw [h1, one_mul] at hqq
      exact hx1 hqq.symm
    · rw [h1, hxx] at hqq
      exact hx1 hqq.symm
  have hsub : T ⊓ centralizer ({t₀} : Set G) ≤
      (P ⊓ centralizer ({p} : Set G)) ⊔ (Q ⊓ centralizer ({q} : Set G)) := by
    intro s hs
    obtain ⟨p', hp', q', hq', rfl⟩ := hdec s hs.1
    have hcomm : p' * q' * t₀ = t₀ * (p' * q') := mem_centralizer_singleton_iff.1 hs.2
    rw [hpq] at hcomm
    have h1 : (p' * p) * (q' * q) = (p * p') * (q * q') := by
      calc (p' * p) * (q' * q) = p' * (p * q') * q := by group
        _ = p' * (q' * p) * q := by rw [hcd.comm p hp q' hq']
        _ = (p' * q') * (p * q) := by group
        _ = (p * q) * (p' * q') := hcomm
        _ = p * (q * p') * q' := by group
        _ = p * (p' * q) * q' := by rw [hcd.comm p' hp' q hq]
        _ = (p * p') * (q * q') := by group
    obtain ⟨hc1, hc2⟩ := hcd.unique (P.mul_mem hp' hp) (P.mul_mem hp hp') (Q.mul_mem hq' hq)
      (Q.mul_mem hq hq') h1
    have hA : p' ∈ P ⊓ centralizer ({p} : Set G) := ⟨hp', mem_centralizer_singleton_iff.2 hc1⟩
    have hB : q' ∈ Q ⊓ centralizer ({q} : Set G) := ⟨hq', mem_centralizer_singleton_iff.2 hc2⟩
    exact Subgroup.mul_mem_sup hA hB
  have hcd2 : CommDisj (P ⊓ centralizer ({p} : Set G)) (Q ⊓ centralizer ({q} : Set G)) := by
    refine ⟨fun a' ha' b' hb' => hcd.comm a' ha'.1 b' hb'.1, ?_⟩
    refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ P ⊓ Q := ⟨hw.1.1, hw.2.1⟩
    rw [hcd.inf] at this
    exact this
  have hup : Nat.card ↥(T ⊓ centralizer ({t₀} : Set G)) ≤ 16 := by
    have h1 := Subgroup.card_le_of_le hsub
    rw [hcd2.card_sup le_rfl le_rfl] at h1
    have := Nat.mul_le_mul hCp hCq
    omega
  have hcc4 : c ^ 4 = 1 := by
    calc c ^ 4 = (c * c) * (c * c) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = x * x := by rw [hcc]
      _ = 1 := hxx
  have hcc2 : ¬ c ^ 2 = 1 := by
    intro h
    apply hx1
    rw [← hcc, ← sq]
    exact h
  have hco : orderOf c = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c) (by simpa using hcc2) (by simpa using hcc4)
    simpa using this
  have hcdc : CommDisj P (zpowers c) := by
    refine ⟨fun p' hp' s hs => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute p' c from hcd.comm p' hp' c hcQ) m).eq
    · refine eq_bot_iff.2 fun w hw => ?_
      have hwQ : w ∈ Q := (zpowers_le.2 hcQ) hw.2
      have : w ∈ P ⊓ Q := ⟨hw.1, hwQ⟩
      rw [hcd.inf] at this
      exact this
  have hlow : 32 ≤ Nat.card ↥(T ⊓ centralizer ({c} : Set G)) := by
    have hle : P ⊔ zpowers c ≤ T ⊓ centralizer ({c} : Set G) := by
      refine sup_le (le_inf hPT ?_) (le_inf ?_ ?_)
      · intro p' hp'
        exact mem_centralizer_singleton_iff.2 (hcd.comm p' hp' c hcQ)
      · exact zpowers_le.2 (hQT hcQ)
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    have h1 := Subgroup.card_le_of_le hle
    rw [hcdc.card_sup le_rfl le_rfl, hP8, Nat.card_zpowers, hco] at h1
    omega
  have hmap : (T ⊓ centralizer ({c} : Set G)).map (MulAut.conj a).toMonoidHom =
      T ⊓ centralizer ({t₀} : Set G) := by
    ext g
    constructor
    · rintro ⟨h, ⟨hhT, hhc⟩, rfl⟩
      refine ⟨hconjT h hhT, mem_centralizer_singleton_iff.2 ?_⟩
      have hhc' : h * c = c * h := mem_centralizer_singleton_iff.1 hhc
      show (MulAut.conj a h) * (a * c * a⁻¹) = (a * c * a⁻¹) * (MulAut.conj a h)
      simp only [MulAut.conj_apply]
      calc a * h * a⁻¹ * (a * c * a⁻¹) = a * (h * c) * a⁻¹ := by group
        _ = a * (c * h) * a⁻¹ := by rw [hhc']
        _ = a * c * a⁻¹ * (a * h * a⁻¹) := by group
    · rintro ⟨hgT, hgc⟩
      refine ⟨a⁻¹ * g * a, ⟨hconjT' g hgT, mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
      · have hgc' : g * t₀ = t₀ * g := mem_centralizer_singleton_iff.1 hgc
        rw [ht₀] at hgc'
        calc a⁻¹ * g * a * c = a⁻¹ * (g * (a * c * a⁻¹)) * a := by group
          _ = a⁻¹ * ((a * c * a⁻¹) * g) * a := by rw [hgc']
          _ = c * (a⁻¹ * g * a) := by group
      · show a * (a⁻¹ * g * a) * a⁻¹ = g
        group
  have hcardeq : Nat.card ↥(T ⊓ centralizer ({t₀} : Set G)) =
      Nat.card ↥(T ⊓ centralizer ({c} : Set G)) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (MulAut.conj a).injective
  omega

omit [Finite G] in
theorem twoPartCard_cj (g : G) (H : Subgroup G) : twoPartCard (cj g H) = twoPartCard H := by
  unfold twoPartCard
  rw [show Nat.card ↥(cj g H) = Nat.card ↥H from
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem false_of_conj_x_eq_z (hG : C3Hyp G) (hs : Th2Std x y K T S) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) {z : G} {J : Subgroup G} (hobs : Obstr52 B z J)
    (hT64 : Nat.card ↥T = 64) (hQ8 : Nat.card ↥(T ⊓ CxK x K) = 8) (hP8 : Nat.card ↥(T ⊓ K) = 8)
    {a : G} (hxz : a * x * a⁻¹ = z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  obtain ⟨eJ⟩ := hobs.nonempty_A7_of_rank_four hG4 hBel
  have hCz : centralizer ({z} : Set G) = cj a (centralizer ({x} : Set G)) := by
    rw [cj_centralizer_singleton, hxz]
  have hCx : twoPartCard (centralizer ({x} : Set G)) = 64 := by
    have := hs.setup.sylowT.card_eq
    rw [hT64] at this
    exact this.symm
  have hCz64 : twoPartCard (centralizer ({z} : Set G)) = 64 := by
    rw [hCz, twoPartCard_cj, hCx]
  have hN4 : twoPartCard (CxK z J) = 4 := by
    have := hobs.twoPartCard_centralizer hG4 hBel eJ
    omega
  have hzx : a⁻¹ * z * a⁻¹⁻¹ = x := by rw [← hxz]; group
  have hJ' : IsPCompIn 2 (centralizer ({x} : Set G)) (cj a⁻¹ J) := by
    have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hobs.comp a⁻¹
    have h2 : cj a⁻¹ (centralizer ({z} : Set G)) = centralizer ({x} : Set G) := by
      rw [cj_centralizer_singleton, hzx]
    exact h2 ▸ h1
  have hCxJ' : CxK x (cj a⁻¹ J) = cj a⁻¹ (CxK z J) := by
    have := PumpTerm.CxK_cmap' a⁻¹ z J
    rw [hzx] at this
    exact this
  have hN4' : twoPartCard (CxK x (cj a⁻¹ J)) = 4 := by
    rw [hCxJ', twoPartCard_cj, hN4]
  by_cases hJK : cj a⁻¹ J = K
  · rw [hJK] at hN4'
    have h1 := hs.sylow_Q.card_eq
    rw [hQ8] at h1
    have h2 : twoPartCard (CxK x K) = 8 := h1.symm
    omega
  · have hKle : K ≤ centralizerSection (cj a⁻¹ J) (pPrimeCoreOf 2 (cj a⁻¹ J)) :=
      Stage1.Thm2.Recip.le_cSec_of_ne hs.comp hJ' (fun h => hJK h.symm)
    have hKC : K ≤ CxK x (cj a⁻¹ J) := le_inf hs.K_le_C hKle
    have hPle : T ⊓ K ≤ CxK x (cj a⁻¹ J) := inf_le_right.trans hKC
    have h8 := Th2.L627.card_le_twoPartCard (hs.T_pGroup.to_inf_left (K := K)) hPle
    rw [hP8, hN4'] at h8
    omega

end CFSG.GH74.GLS.Th2.Obs
