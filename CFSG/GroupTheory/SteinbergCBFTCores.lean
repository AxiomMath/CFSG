module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.Walter.Transitivity.OddCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

theorem centralizer_pCore_le_pCore {Y : Type*} [Group Y] [Finite Y]
    (hY : IsPiSeparable {q : Nat.Primes | q.val = p} Y) (hcore : pPrimeCore p Y = ⊥) :
    centralizer (pCore p Y : Set Y) ≤ pCore p Y := by
  rw [pCore_eq_piCore Y p]
  refine centralizer_piCore_le_piCore hY ?_
  rw [← hcore, pPrimeCore_eq_piCore Y p]
  rfl

theorem commute_of_commutator_mem {Y : Type*} [Group Y] [Finite Y] {N H : Subgroup Y}
    {S : Set Y} (hN : IsPGroup p N) (hH : Nat.Coprime p (Nat.card H))
    (hHN : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h)
    (hHS : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ * x⁻¹ ∈ N) : ∀ h ∈ H, ∀ x ∈ S, h * x = x * h := by
  intro h hh x hx
  set z := h * x * h⁻¹ * x⁻¹ with hz
  have hzN : z ∈ N := hHS h hh x hx
  have hzc : Commute h z := hHN h hh z hzN
  have hpow : ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ = z ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzk : h * z ^ k = z ^ k * h := (hzc.pow_right k).eq
      calc h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ = h * (h ^ k * x * (h ^ k)⁻¹) * h⁻¹ := by group
        _ = h * (z ^ k * x) * h⁻¹ := by rw [ih]
        _ = z ^ k * (h * x * h⁻¹ * x⁻¹) * x := by rw [← mul_assoc h, hzk]; group
        _ = z ^ (k + 1) * x := by rw [← hz, pow_succ]
  have hz1 : z ^ orderOf h = 1 := by
    have hk := hpow (orderOf h)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    simpa using congrArg (· * x⁻¹) hk.symm
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have h1 : orderOf z ∣ p ^ n := by
    rw [← hn, ← Subgroup.orderOf_mk z hzN]
    exact orderOf_dvd_natCard _
  have h2 : orderOf z ∣ Nat.card H := by
    refine (orderOf_dvd_of_pow_eq_one hz1).trans ?_
    rw [← Subgroup.orderOf_mk h hh]
    exact orderOf_dvd_natCard _
  have hz1' : z = 1 :=
    orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hH.pow_left n) h1 h2)
  rw [hz, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz1'
  exact hz1'

theorem commutator_mem_of_le_commutator {Y : Type*} [Group Y] {N A H : Subgroup Y} {S : Set Y}
    (hNA : A ≤ normalizer (N : Set Y)) (hHN : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h)
    (hHS : ∀ h ∈ H, ∀ x ∈ S, h⁻¹ * x * h ∈ S)
    (hAS : ∀ a ∈ A, ∀ x ∈ S, a * x * a⁻¹ * x⁻¹ ∈ N) (hH : H ≤ ⁅H, A⁆) :
    ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ * x⁻¹ ∈ N := by
  let T : Subgroup Y :=
    { carrier := {g | g ∈ normalizer (N : Set Y) ∧ ∀ x ∈ S, g * x * g⁻¹ * x⁻¹ ∈ N}
      mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, fun x hx => by
        have h1 := (mem_normalizer_iff.1 hg.1 _).1 (hg'.2 x hx)
        have h2 := hg.2 x hx
        have := mul_mem h1 h2
        simpa [mul_assoc] using this⟩
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun x hx => by
        have h1 := (mem_normalizer_iff.1 (inv_mem hg.1) _).1 (hg.2 x hx)
        have := inv_mem h1
        simpa [mul_assoc] using this⟩ }
  have hAT : A ≤ T := fun a ha => ⟨hNA ha, hAS a ha⟩
  have hHnorm : ∀ h ∈ H, h ∈ normalizer (N : Set Y) := fun h hh => mem_normalizer_iff.2 fun n => by
    constructor
    · intro hn
      rw [hHN h hh n hn, mul_inv_cancel_right]
      exact hn
    · intro hn
      have hc := hHN h hh _ hn
      have h' : n = h * n * h⁻¹ := by
        calc n = h⁻¹ * ((h * n * h⁻¹) * h) := by group
          _ = h⁻¹ * (h * (h * n * h⁻¹)) := by rw [hc]
          _ = h * n * h⁻¹ := by group
      rw [h']
      exact hn
  have hconj : ∀ h ∈ H, ∀ g ∈ T, h * g * h⁻¹ ∈ T := by
    intro h hh g hg
    refine ⟨mul_mem (mul_mem (hHnorm h hh) hg.1) (inv_mem (hHnorm h hh)), fun x hx => ?_⟩
    have h1 := hg.2 _ (hHS h hh x hx)
    have h2 : h * (g * (h⁻¹ * x * h) * g⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ =
        g * (h⁻¹ * x * h) * g⁻¹ * (h⁻¹ * x * h)⁻¹ := by
      rw [hHN h hh _ h1, mul_inv_cancel_right]
    rw [← h2] at h1
    simpa [mul_assoc] using h1
  have hle : ⁅H, A⁆ ≤ T := by
    rw [commutator_le]
    intro h hh a ha
    rw [commutatorElement_def]
    exact mul_mem (hconj h hh a (hAT ha)) (inv_mem (hAT ha))
  exact fun h hh x hx => (hle (hH hh)).2 x hx

theorem eq_bot_of_normalized_by_scn {Y : Type*} [Group Y] [Finite Y] {Q P A H : Subgroup Y}
    [Q.Normal] (hQp : IsPGroup p Q) (hchar : centralizer (Q : Set Y) ≤ Q) (hQP : Q ≤ P)
    (hPp : IsPGroup p P) (hPA : P ≤ normalizer (A : Set Y))
    (hcen : P ⊓ centralizer (A : Set Y) = A) (hH : Nat.Coprime p (Nat.card H))
    (hAH : A ≤ normalizer (H : Set Y)) : H = ⊥ := by
  have hQH : Q ⊓ H = ⊥ := by
    refine disjoint_iff.1 (disjoint_of_coprime_natCard ?_)
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact hH.pow_left n
  have hAP : A ≤ P := hcen ▸ inf_le_left
  have hAp : IsPGroup p A := hPp.to_le hAP
  set N := A ⊓ Q with hNdef
  have hNp : IsPGroup p N := hQp.to_le inf_le_right
  have hHN : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h := by
    intro h hh n hn
    obtain ⟨hnA, hnQ⟩ := mem_inf.1 hn
    have hc : n * h * n⁻¹ * h⁻¹ ∈ Q ⊓ H := by
      refine mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.1 (hAH hnA) h).1 hh) (inv_mem hh)⟩
      have := mul_mem hnQ (‹Q.Normal›.conj_mem _ (inv_mem hnQ) h)
      simpa [mul_assoc] using this
    rw [hQH, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm
  have hAQ : ∀ a ∈ A, ∀ x ∈ (Q : Set Y), a * x * a⁻¹ * x⁻¹ ∈ N := by
    intro a ha x hx
    have hx' : x ∈ Q := hx
    refine mem_inf.2 ⟨?_, mul_mem (‹Q.Normal›.conj_mem x hx' a) (inv_mem hx')⟩
    have : x * a⁻¹ * x⁻¹ ∈ A := (mem_normalizer_iff.1 (hPA (hQP hx')) a⁻¹).1 (inv_mem ha)
    simpa [mul_assoc] using mul_mem ha this
  have hHQ : ∀ h ∈ H, ∀ x ∈ (Q : Set Y), h⁻¹ * x * h ∈ (Q : Set Y) := fun h _ x hx => by
    simpa using ‹Q.Normal›.conj_mem x hx h⁻¹
  set H₀ := ⁅H, A⁆ with hH₀def
  have hH₀H : H₀ ≤ H := by
    rw [commutator_le]
    intro h hh a ha
    have h1 : a * h⁻¹ * a⁻¹ ∈ H := (mem_normalizer_iff.1 (hAH ha) h⁻¹).1 (inv_mem hh)
    have := mul_mem hh h1
    simpa [commutatorElement_def, mul_assoc] using this
  have hidem : ⁅H₀, A⁆ = H₀ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp.out A H hAp hAH
      hH
  have hH₀cop : Nat.Coprime p (Nat.card H₀) :=
    hH.coprime_dvd_right (card_dvd_of_le hH₀H)
  have hH₀N : ∀ h ∈ H₀, ∀ n ∈ N, h * n = n * h := fun h hh n hn => hHN h (hH₀H hh) n hn
  have hH₀Q := commutator_mem_of_le_commutator (S := (Q : Set Y)) (H := H₀)
    (fun a ha => mem_normalizer_iff.2 fun n => by
      rw [mem_inf, mem_inf]
      constructor
      · rintro ⟨hnA, hnQ⟩
        exact ⟨mul_mem (mul_mem ha hnA) (inv_mem ha), ‹Q.Normal›.conj_mem n hnQ a⟩
      · rintro ⟨hnA, hnQ⟩
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using mul_mem (mul_mem (inv_mem ha) hnA) ha
        · simpa [mul_assoc] using ‹Q.Normal›.conj_mem _ hnQ a⁻¹)
    hH₀N (fun h hh => hHQ h (hH₀H hh)) hAQ hidem.ge
  have hH₀c := commute_of_commutator_mem hNp hH₀cop hH₀N hH₀Q
  have hH₀bot : H₀ = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    have : h ∈ Q ⊓ H := ⟨hchar (mem_centralizer_iff.2 fun x hx => (hH₀c h hh x hx).symm), hH₀H hh⟩
    rwa [hQH] at this
  have h1 : ⁅⁅Q, A⁆, H⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rw [commutator_le]
    intro x hx a ha
    have hc : ⁅x, a⁆ ∈ N := by
      have := inv_mem (hAQ a ha x hx)
      simpa [commutatorElement_def, mul_assoc] using this
    exact mem_centralizer_iff.2 fun h hh => hHN h hh _ hc
  have h2 : ⁅⁅A, H⁆, Q⁆ = ⊥ := by
    rw [commutator_comm A H, ← hH₀def, hH₀bot, commutator_bot_left]
  have h3 : ⁅⁅H, Q⁆, A⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have hHQN : ∀ h ∈ H, ∀ x ∈ (Q : Set Y), h * x * h⁻¹ * x⁻¹ ∈ N := by
    intro h hh x hx
    have hx' : x ∈ Q := hx
    have hcQ : h * x * h⁻¹ * x⁻¹ ∈ Q := mul_mem (‹Q.Normal›.conj_mem x hx' h) (inv_mem hx')
    have hcA : h * x * h⁻¹ * x⁻¹ ∈ centralizer (A : Set Y) := by
      have hc : ⁅h, x⁆ ∈ ⁅H, Q⁆ := commutator_mem_commutator hh hx'
      exact (commutator_eq_bot_iff_le_centralizer.1 h3) hc
    have : h * x * h⁻¹ * x⁻¹ ∈ P ⊓ centralizer (A : Set Y) := mem_inf.2 ⟨hQP hcQ, hcA⟩
    rw [hcen] at this
    exact mem_inf.2 ⟨this, hcQ⟩
  have hHc := commute_of_commutator_mem hNp hH hHN hHQN
  rw [eq_bot_iff]
  intro h hh
  have : h ∈ Q ⊓ H := ⟨hchar (mem_centralizer_iff.2 fun x hx => (hHc h hh x hx).symm), hh⟩
  rwa [hQH] at this

variable {X : Type*} [Group X] [Finite X]

theorem centralizer_pCore_quotient_le (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) :
    centralizer (pCore p (X ⧸ pPrimeCore p X) : Set (X ⧸ pPrimeCore p X)) ≤
      pCore p (X ⧸ pPrimeCore p X) :=
  centralizer_pCore_le_pCore (hX.quotient _) (pPrimeCore_quotient_pPrimeCore_eq_bot p)

theorem le_pPrimeCore_of_sylow_normalizes (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X)
    (P : Sylow p X) {H : Subgroup X} (hH : Nat.Coprime p (Nat.card H))
    (hPH : (P : Subgroup X) ≤ normalizer (H : Set X)) : H ≤ pPrimeCore p X := by
  let N : Subgroup X := pPrimeCore p X
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hPbar : pCore p (X ⧸ N) ≤ (Sylow.mapSurjective hsurj P : Subgroup (X ⧸ N)) :=
    (pCore_isPGroup (p := p) (G := X ⧸ N)).le_sylow_of_normal _
  have hbot : H.map (QuotientGroup.mk' N) = ⊥ := by
    refine CFSG.Walter.Transitivity.eq_bot_of_coprime_of_pCore_le_normalizer
      (centralizer_pCore_quotient_le hX)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd H _) hH) (hPbar.trans ?_)
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_mono hPH).trans (Subgroup.le_normalizer_map _)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem le_pPrimeCore_of_scn_normalizes (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X)
    (P : Sylow p X) {A : Subgroup X} (hPA : (P : Subgroup X) ≤ normalizer (A : Set X))
    (hcen : (P : Subgroup X) ⊓ centralizer (A : Set X) = A) {H : Subgroup X}
    (hH : Nat.Coprime p (Nat.card H)) (hAH : A ≤ normalizer (H : Set X)) :
    H ≤ pPrimeCore p X := by
  let K : Subgroup X := pPrimeCore p X
  let φ := QuotientGroup.mk' K
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective K
  let Pbar := Sylow.mapSurjective hsurj P
  have hPbar : (Pbar : Subgroup (X ⧸ K)) = (P : Subgroup X).map φ := Sylow.coe_mapSurjective _ _
  have hQP : pCore p (X ⧸ K) ≤ (Pbar : Subgroup (X ⧸ K)) :=
    (pCore_isPGroup (p := p) (G := X ⧸ K)).le_sylow_of_normal _
  have hAP : A ≤ P := hcen ▸ inf_le_left
  have hPK : (P : Subgroup X) ⊓ K = ⊥ := by
    refine disjoint_iff.1 (disjoint_of_coprime_natCard ?_)
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := X)).pow_left n
  have hPAbar : (Pbar : Subgroup (X ⧸ K)) ≤ normalizer (A.map φ : Set (X ⧸ K)) := by
    rw [hPbar]
    exact (map_mono hPA).trans (le_normalizer_map φ)
  have hcenbar : (Pbar : Subgroup (X ⧸ K)) ⊓ centralizer (A.map φ : Set (X ⧸ K)) = A.map φ := by
    rw [hPbar]
    apply le_antisymm
    · intro y hy
      obtain ⟨⟨x, hxP, rfl⟩, hxC⟩ := mem_inf.1 hy
      have hxP' : x ∈ (P : Subgroup X) := hxP
      have hxA : x ∈ (P : Subgroup X) ⊓ centralizer (A : Set X) := by
        refine mem_inf.2 ⟨hxP', mem_centralizer_iff.2 fun a ha => ?_⟩
        have hcomm := mem_centralizer_iff.1 hxC (φ a) ⟨a, ha, rfl⟩
        have hk : a * x * a⁻¹ * x⁻¹ ∈ (P : Subgroup X) ⊓ K := by
          refine mem_inf.2
            ⟨mul_mem (mul_mem (mul_mem (hAP ha) hxP') (inv_mem (hAP ha))) (inv_mem hxP'), ?_⟩
          rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker]
          change φ (a * x * a⁻¹ * x⁻¹) = 1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
          group
        rw [hPK, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk
        exact hk
      rw [hcen] at hxA
      exact ⟨x, hxA, rfl⟩
    · refine le_inf (map_mono hAP) ?_
      rintro _ ⟨a, ha, rfl⟩
      refine mem_centralizer_iff.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b ∈ centralizer (A : Set X) := by
        rw [← hcen] at hb
        exact hb.2
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hb' a ha]
  have hbot : H.map φ = ⊥ :=
    eq_bot_of_normalized_by_scn (pCore_isPGroup (p := p) (G := X ⧸ K))
      (centralizer_pCore_quotient_le hX) hQP Pbar.isPGroup' hPAbar hcenbar
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd H _) hH)
      ((map_mono hAH).trans (le_normalizer_map φ))
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem ft_lemma_7_3 (hX : IsPSolvable p X) (P : Sylow p X) {H : Subgroup X}
    (hH : Nat.Coprime p (Nat.card H)) (hPH : (P : Subgroup X) ≤ normalizer (H : Set X)) :
    H ≤ piCore {q : Nat.Primes | q.val ≠ p} X := by
  rw [← pPrimeCore_eq_piCore X p]
  exact le_pPrimeCore_of_sylow_normalizes (isPiSeparable_of_isPSolvable hp.out hX) P hH hPH

theorem ft_lemma_7_4_b (hX : IsPSolvable p X) (P : Sylow p X) {A : Subgroup (P : Subgroup X)}
    (hA : A ∈ SCN P) {H : Subgroup X} (hH : Nat.Coprime p (Nat.card H))
    (hAH : A.map (P : Subgroup X).subtype ≤ normalizer (H : Set X)) :
    H ≤ piCore {q : Nat.Primes | q.val ≠ p} X := by
  rw [← pPrimeCore_eq_piCore X p]
  obtain ⟨hPA, hcen⟩ := SCN.map_props hA
  exact le_pPrimeCore_of_scn_normalizes (isPiSeparable_of_isPSolvable hp.out hX) P hPA hcen hH
    hAH

end CFSG.GroupTheory.FT63ChII
