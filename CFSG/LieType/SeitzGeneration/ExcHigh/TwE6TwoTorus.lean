module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoSpine
public import CFSG.LieType.SeitzGeneration.ExcTorusTw
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

section Arith

variable {K : Type} [Field K] [Finite K]

theorem dvd_card_normOne {Q : ℕ} (hQ : 2 ≤ Q) (hK : Nat.card K = Q ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ Q) : (Q + 1) ∣ Nat.card (normOne σ) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hsq : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩
    have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
    rw [Nat.add_sub_cancel, this, Nat.add_sub_cancel]
  have hord : orderOf g = (Q - 1) * (Q + 1) := by
    rw [← hsq, ← hK, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hdvd : Q - 1 ∣ orderOf g := ⟨Q + 1, hord⟩
  set x : Kˣ := g ^ (Q - 1) with hx
  have hζ : orderOf x = Q + 1 := by
    rw [hx, orderOf_pow_of_dvd (by omega) hdvd, hord, Nat.mul_div_cancel_left _ (by omega)]
  have hmem : x ∈ normOne σ := by
    show sU σ x = x⁻¹
    refine Units.ext ?_
    have h1 : x ^ (Q + 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
    have h2 : (x : K) ^ Q * (x : K) = 1 := by
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rw [Units.val_inv_eq_inv_val]
    exact (hσ x).trans (eq_inv_of_mul_eq_one_left h2)
  have hle : Subgroup.zpowers x ≤ normOne σ := by
    rw [Subgroup.zpowers_le]
    exact hmem
  have := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hζ] at this

end Arith

section TorusOrder

variable {K : Type} [Field K] [Finite K]


variable (σ : K →+* K)

theorem not_dvd_card_ker_torusG {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    ¬ p ∣ Nat.card (torusG σ).ker := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h3' : x ^ 3 = 1 := Subtype.ext (torusG_ker_pow_three σ x.2)
  have : p ∣ 3 := hx ▸ orderOf_dvd_of_pow_eq_one h3'
  exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)

theorem two_mul_factorization_le_card_torusG {n : ℕ} (hn : n ∣ Nat.card (normOne σ)) {p : ℕ}
    (hp : p.Prime) (h3 : p ≠ 3) :
    2 * n.factorization p ≤ (Nat.card (torusG σ).range).factorization p := by
  have hker := not_dvd_card_ker_torusG σ hp h3
  have h := Subgroup.card_ker_mul_card_range (torusG σ)
  rw [Nat.card_prod] at h
  have h0 : Nat.card (torusG σ).ker ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (torusG σ).range ≠ 0 := Nat.card_pos.ne'
  have hn0 : Nat.card (normOne σ) ≠ 0 := Nat.card_pos.ne'
  have hn0' : n ≠ 0 := fun h' => hn0 (by simpa [h'] using hn)
  have h2 := congrArg (fun m => m.factorization p) h
  simp only [Nat.factorization_mul h0 h1, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hker, zero_add] at h2
  rw [h2, Nat.factorization_mul hn0 hn0, Finsupp.add_apply]
  have := (Nat.factorization_le_iff_dvd hn0' hn0).2 hn p
  omega

end TorusOrder

section Order

theorem not_dvd_degreesE6 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ 2 ∧ ¬ p ∣ 5 ∧ ¬ p ∣ 6 ∧ ¬ p ∣ 8 ∧ ¬ p ∣ 9 ∧ ¬ p ∣ 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := Nat.le_of_dvd (by norm_num) h <;>
    interval_cases p <;> first | omega | (exfalso; norm_num at hp)


theorem factorization_card_twistedE6_of_seven_le_of_dvd_add_one {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    (Nat.card (twistedE6RootGroup K σ)).factorization p = 6 * (ℓ ^ f + 1).factorization p := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpq' : ¬ p ∣ ℓ ^ f := by
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - ℓ ^ f := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - ℓ ^ f = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have h := ordProj_card_twistedE6 hℓ hf K hK σ hσ hp (by omega) hpq'
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h => hpq' (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have heQ : orderOf (Q : ZMod p) = 1 := by
    rw [orderOf_eq_one_iff]
    have h1 : ((ℓ ^ f + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast [hQdef] at h1 ⊢
    linear_combination -h1
  have hlte : ∀ d : ℕ, d ≠ 0 → p ^ ((Q ^ d - 1).natAbs).factorization p =
      p ^ ((Q - 1).natAbs).factorization p * p ^ d.factorization p := fun d hd => by
    have h1 := ordProj_int_pow_sub_one_of_dvd hp (by omega) hQ2 hpQ heQ one_ne_zero hd
    rwa [one_mul, pow_one] at h1
  have hQ1 : (Q - 1).natAbs = ℓ ^ f + 1 := by
    rw [hQdef, show -((ℓ ^ f : ℕ) : ℤ) - 1 = -((ℓ ^ f + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
  obtain ⟨n2, n5, n6, n8, n9, n12⟩ := not_dvd_degreesE6 hp hp7
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 2 (by norm_num), hlte 5 (by norm_num), hlte 6 (by norm_num), hlte 8 (by norm_num),
    hlte 9 (by norm_num), hlte 12 (by norm_num), ordProj_eq_one_of_not_dvd' n2,
    ordProj_eq_one_of_not_dvd' n5, ordProj_eq_one_of_not_dvd' n6, ordProj_eq_one_of_not_dvd' n8,
    ordProj_eq_one_of_not_dvd' n9, ordProj_eq_one_of_not_dvd' n12, hQ1] at h
  refine Nat.pow_right_injective hp.two_le ?_
  change p ^ _ = p ^ _
  rw [h]
  ring

end Order

section Sylow


theorem factorization_card_le_frame_torusG {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    (Nat.card ↥(twistedE6RootGroup K σ)).factorization p ≤
      4 * (Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) + 1).factorization p +
        (Nat.card (torusG σ.toRingHom).range).factorization p := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hdvd : (ℓ ^ f + 1) ∣ Nat.card (normOne σ.toRingHom) := dvd_card_normOne hq2 hK hσ'
  have hA := two_mul_factorization_le_card_torusG σ.toRingHom hdvd hp (by omega)
  have hG := factorization_card_twistedE6_of_seven_le_of_dvd_add_one hℓ hf K hK σ hσ hp hp7 hpq
  rw [hkcard]
  omega

theorem exists_conj_le_frame_torusG {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} [hpF : Fact p.Prime] (hp7 : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1)
    (E : Subgroup (twistedE6RootGroup K σ)) (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ g : twistedE6RootGroup K σ, E.map (MulAut.conj g).toMonoidHom ≤
      (⨆ i, (frameHom σ.toRingHom i).range) ⊔ (torusG σ.toRingHom).range := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  have hcomm : ∀ (i : Fin 4) (A : SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)))
      (t : ↥(normOne σ.toRingHom) × ↥(normOne σ.toRingHom)),
      Commute (torusG σ.toRingHom t) (frameHom σ.toRingHom i A) := fun i A t =>
    torusG_commute_frame _ (frameHom_mem_rootPair σ.toRingHom) t i A
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hpq' : p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) + 1 := by
    rw [hkcard]; exact hpq
  refine exists_conj_le_frame_torus (frameHom σ.toRingHom) (frameHom_injective σ.toRingHom)
    (fun i j hij A B => frameHom_commute σ.toRingHom hij A B) (torusG σ.toRingHom).range
    (fun a ha i y => ?_) (by omega) hpq'
    (factorization_card_le_frame_torusG hℓ hf K hK σ hσ hpF.out hp7 hpq) E hE
  obtain ⟨t, rfl⟩ := ha
  exact hcomm i y t

end Sylow

end CFSG.LieType.SeitzGeneration.ExcHigh
