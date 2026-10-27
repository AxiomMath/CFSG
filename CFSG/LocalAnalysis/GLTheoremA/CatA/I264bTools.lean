module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

section Basic

variable {Y : Type} [Group Y] [Finite Y]

theorem glaPPrimeCoreOf_eq_bot_p {p : ℕ} {K : Subgroup Y} (hcore : GLAPPrimeCore p ↥K = ⊥) :
    GLAPPrimeCoreOf p K = ⊥ := by
  unfold GLAPPrimeCoreOf
  rw [hcore, Subgroup.map_bot]

theorem glaPComponent_self_p {p : ℕ} {K : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hcore : GLAPPrimeCore p ↥K = ⊥) : GLAPComponent p K K := by
  have eK : ↥K ⧸ GLAPPrimeCore p ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hY : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hq
  obtain ⟨hcomp, -, hbarX⟩ := glaPLayer_of_isQuasisimple hY
  have hle : GLAPLayer p K ≤ K := hcomp.1
  have h2 := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hle hbarX
  rw [glaPPrimeCoreOf_eq_bot_p hcore, sup_bot_eq] at h2
  rwa [h2] at hcomp

noncomputable def pSimpleEquiv {p : ℕ} {K : Subgroup Y} (hcore : GLAPPrimeCore p ↥K = ⊥) :
    PSimple p K ≃* ↥K ⧸ Subgroup.center ↥K :=
  let e1 : PQuot p K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  QuotientGroup.congr (Subgroup.center (PQuot p K)) (Subgroup.center ↥K) e1
    (Subgroup.map_center_eq e1)

theorem centMod_iff_centralizer {p : ℕ} {K : Subgroup Y} (hcore : GLAPPrimeCore p ↥K = ⊥) {g : Y}
    (hg : g ∈ Subgroup.normalizer (K : Set Y)) :
    CentMod p K g ↔ g ∈ Subgroup.centralizer (K : Set Y) := by
  constructor
  · intro h
    have h1 := centMod_iff.1 h
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have h2 := h1.2 l hl
    rw [glaPPrimeCoreOf_eq_bot_p hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  · exact centMod_of_mem_centralizer

end Basic

section Action

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

@[expose] noncomputable def actionHom (K B : Subgroup Y) (hBK : B ≤ Subgroup.normalizer (K : Set Y)) (p : ℕ) :
    ↥B →* MulAut (PSimple p K) :=
  (chevAut p K).comp (Subgroup.inclusion hBK)

theorem actionHom_apply (K B : Subgroup Y) (hBK : B ≤ Subgroup.normalizer (K : Set Y)) (p : ℕ)
    (b : ↥B) : actionHom K B hBK p b = chevAut p K ⟨(b : Y), hBK b.2⟩ := rfl

theorem actionHom_eq_one_iff (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (b : ↥B) :
    actionHom K B (fun g _ => (Subgroup.normalizer_eq_top_iff.2 h.normal) ▸ Subgroup.mem_top g) p b = 1 ↔
      (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
  have hcomp : GLAPComponent p K K := glaPComponent_self_p h.qs h.core
  have hbN : (b : Y) ∈ Subgroup.normalizer (K : Set Y) := Subgroup.normalizer_eq_top_iff.2 h.normal ▸ Subgroup.mem_top _
  have := chevAut_eq_one_iff hp hcomp hbN
  rw [← centMod_iff_centralizer h.core hbN]
  exact this

end Action

section Cent

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

private theorem normalizer_of_normal {K : Subgroup Y} (hK : K.Normal) {g : Y} :
    g ∈ Subgroup.normalizer (K : Set Y) :=
  Subgroup.normalizer_eq_top_iff.2 hK ▸ Subgroup.mem_top g

theorem card_actionHom (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hBK : B ≤ Subgroup.normalizer (K : Set Y)) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) * Nat.card ↥(actionHom K B hBK p).range =
      Nat.card B := by
  set ψ := actionHom K B hBK p with hψ
  have hmap : ψ.ker.map B.subtype = B ⊓ Subgroup.centralizer (K : Set Y) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (actionHom_eq_one_iff hp h x).1 hx⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (actionHom_eq_one_iff hp h ⟨g, hgB⟩).2 hgC, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective]
  rw [← hker]
  exact Subgroup.card_ker_mul_card_range ψ

theorem card_B_eq (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B) :
    ∃ ψ : ↥B →* MulAut (PSimple p K), (∀ b : ↥B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y)) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) * Nat.card ↥ψ.range = Nat.card B :=
  ⟨actionHom K B (fun g _ => normalizer_of_normal h.normal) p, actionHom_eq_one_iff hp h,
    card_actionHom hp h _⟩

theorem exists_centralizing (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) :
    ∃ b ∈ B, b ∉ Subgroup.centralizer (K : Set Y) ∧ ∃ w ∈ K, orderOf w = 2 ∧ b * w = w * b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := h.twogrp
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card T) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hpB : p ≤ Nat.card B :=
    le_trans (Nat.le_self_pow (by norm_num) p) h.card
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes hp h.elem hpB hBT hcop
  have hex : ∃ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p B,
      T ⊓ Subgroup.centralizer (H : Set Y) ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have : (⨆ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p B,
        T ⊓ Subgroup.centralizer (H : Set Y)) = ⊥ := iSup₂_eq_bot.2 hall
    rw [hgen] at this
    exact hTne this
  obtain ⟨H, ⟨hHB, hHcard⟩, hHne⟩ := hex
  have hH3 : p ^ 3 ≤ Nat.card H := by
    have : p * p ^ 3 ≤ p * Nat.card H := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ Nat.card B := h.card
        _ = p * Nat.card H := hHcard
    exact Nat.le_of_mul_le_mul_left this hp.pos
  have hHnc : ¬ H ≤ Subgroup.centralizer (K : Set Y) := by
    intro hHC
    have : Nat.card H ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) :=
      Subgroup.card_le_of_le (le_inf hHB hHC)
    omega
  obtain ⟨b, hbH, hbC⟩ := SetLike.not_le_iff_exists.1 hHnc
  set U : Subgroup Y := T ⊓ Subgroup.centralizer (H : Set Y) with hU
  have hUp : IsPGroup 2 ↥U := hT2.to_le inf_le_left
  obtain ⟨j, hj⟩ := hUp.exists_card_eq
  have hUnt : Nat.card U ≠ 1 := by
    intro h1
    apply hHne
    rw [Subgroup.eq_bot_iff_card, h1]
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hUnt (by rw [hj]; rfl)
  have h2U : 2 ∣ Nat.card U := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥U) 2 (by rwa [← Nat.card_eq_fintype_card])
  refine ⟨b, hHB hbH, hbC, (x : Y), hTK x.2.1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hx]
  · exact Subgroup.mem_centralizer_iff.1 x.2.2 b hbH

end Cent

section Vacuity

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem pSimpleEquiv_chevQuotHom {K : Subgroup Y} (hcore : GLAPPrimeCore p ↥K = ⊥) (k : ↥K) :
    pSimpleEquiv hcore (chevQuotHom p K k) = QuotientGroup.mk k := by
  simp [pSimpleEquiv, chevQuotHom, pQuotHom]
  rfl

theorem false_of_noInvCent (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hS : ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 → ∀ w : S, w ^ 2 = 1 → w ≠ 1 → α w ≠ w) : False := by
  classical
  obtain ⟨b, hbB, hbC, w, hwK, hw2, hbw⟩ := exists_centralizing hp hp2 h hc
  let eS : PSimple p K ≃* S := (pSimpleEquiv h.core).trans e
  let ψ := actionHom K B (fun g _ => normalizer_of_normal h.normal) p
  have hψ1 := actionHom_eq_one_iff hp h
  let b' : ↥B := ⟨b, hbB⟩
  let α₀ : MulAut (PSimple p K) := ψ b'
  let α : MulAut S := MulAut.congr eS α₀
  have hbp : b ^ p = 1 := h.elem.2 b hbB
  have hψpow : α₀ ^ p = 1 := by
    have : b' ^ p = 1 := Subtype.ext hbp
    show ψ b' ^ p = 1
    rw [← map_pow, this, map_one]
  have hαp : α ^ p = 1 := by
    show (MulAut.congr eS α₀) ^ p = 1
    rw [← map_pow, hψpow, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have : α₀ = 1 := by
      have := (MulAut.congr eS).injective (h1.trans (map_one (MulAut.congr eS)).symm)
      exact this
    exact hbC ((hψ1 b').1 this)
  have hbN : b ∈ Subgroup.normalizer (K : Set Y) := normalizer_of_normal h.normal
  let w' : ↥K := ⟨w, hwK⟩
  have hfix : α₀ (chevQuotHom p K w') = chevQuotHom p K w' := by
    have := chevAut_chevQuotHom p K ⟨b, hbN⟩ w'
    have hconj : (K.normalizerMonoidHom ⟨b, hbN⟩ w') = w' := by
      apply Subtype.ext
      show b * w * b⁻¹ = w
      rw [hbw]
      group
    rw [hconj] at this
    exact this
  have hw2'' : w ^ 2 = 1 := by
    rw [← hw2]
    exact pow_orderOf_eq_one w
  have hw2' : w' ^ 2 = 1 := Subtype.ext hw2''
  have hwc : w' ∉ Subgroup.center ↥K := by
    intro hz
    have hpg := KD264Z.isPGroup_center_of_pPrimeCore hp h.core
    obtain ⟨j, hj⟩ := hpg ⟨w', hz⟩
    have hord : orderOf (⟨w', hz⟩ : Subgroup.center ↥K) = 2 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (w' : ↥K) = 2
      rw [← Subgroup.orderOf_coe]
      exact hw2
    have := orderOf_dvd_of_pow_eq_one hj
    rw [hord] at this
    have hdvd : 2 ∣ p ^ j := this
    have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm
  set w₀ : S := eS (chevQuotHom p K w') with hw₀
  have hw₀2 : w₀ ^ 2 = 1 := by
    rw [hw₀, ← map_pow, ← map_pow, hw2', map_one, map_one]
  have hw₀1 : w₀ ≠ 1 := by
    intro h1
    have h2 : pSimpleEquiv h.core (chevQuotHom p K w') = 1 := by
      have := eS.injective (h1.trans (map_one eS).symm)
      rw [this, map_one]
    rw [pSimpleEquiv_chevQuotHom h.core, QuotientGroup.eq_one_iff] at h2
    exact hwc h2
  apply hS α hαp hα1 w₀ hw₀2 hw₀1
  show (MulAut.congr eS α₀) (eS (chevQuotHom p K w')) = eS (chevQuotHom p K w')
  simp [MulAut.congr_apply, hfix]

end Vacuity

end CFSG.LocalAnalysis.GLTheoremA
