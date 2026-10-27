module

public import CFSG.FeitThompson.Foundations.PGroupNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

variable {R : Type*} [Group R] {p i : ℕ} {H S : Subgroup R}

def commutatorChain (H : Subgroup R) : ℕ → Subgroup R
  | 0 => H
  | i + 1 => ⁅(⊤ : Subgroup R), commutatorChain H i⁆

@[simp] theorem commutatorChain_zero (H : Subgroup R) : commutatorChain H 0 = H := (rfl)

@[simp] theorem commutatorChain_succ (H : Subgroup R) (i : ℕ) :
    commutatorChain H (i + 1) = ⁅(⊤ : Subgroup R), commutatorChain H i⁆ := (rfl)

instance commutatorChain_characteristic (H : Subgroup R) [H.Characteristic] (i : ℕ) :
    (commutatorChain H i).Characteristic := by
  induction i with
  | zero => rw [commutatorChain_zero]; infer_instance
  | succ i _ => rw [commutatorChain_succ]; exact Subgroup.commutator_characteristic _ _

instance commutatorChain_normal (H : Subgroup R) [H.Normal] (i : ℕ) :
    (commutatorChain H i).Normal := by
  induction i with
  | zero => rw [commutatorChain_zero]; infer_instance
  | succ i _ => rw [commutatorChain_succ]; exact Subgroup.commutator_normal _ _

theorem commutatorElement_mem_commutatorChain_succ (H : Subgroup R) (i : ℕ) {x : R}
    (hx : x ∈ commutatorChain H i) (s : R) : ⁅x, s⁆ ∈ commutatorChain H (i + 1) := by
  rw [commutatorChain_succ, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hx (mem_top s)

theorem commutatorChain_succ_le (H : Subgroup R) [H.Normal] (i : ℕ) :
    commutatorChain H (i + 1) ≤ commutatorChain H i := by
  rw [commutatorChain_succ]; exact Subgroup.commutator_le_right _ _

theorem commutatorChain_antitone (H : Subgroup R) [H.Normal] : Antitone (commutatorChain H) :=
  antitone_nat_of_succ_le (commutatorChain_succ_le H)

theorem commutatorChain_le (H : Subgroup R) [H.Normal] (i : ℕ) : commutatorChain H i ≤ H :=
  commutatorChain_antitone H (Nat.zero_le i)

theorem commutatorChain_le_lowerCentralSeries (H : Subgroup R) (i : ℕ) :
    commutatorChain H i ≤ (⊤ : Subgroup R).lowerCentralSeries i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [commutatorChain_succ, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono ih le_rfl

theorem commutatorChain_add_of_succ_eq (H : Subgroup R)
    (h : commutatorChain H (i + 1) = commutatorChain H i) (k : ℕ) :
    commutatorChain H (i + k) = commutatorChain H i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, commutatorChain_succ, ih, ← commutatorChain_succ, h]

theorem exists_commutatorChain_eq_bot_of_isNilpotent [Group.IsNilpotent R] (H : Subgroup R) :
    ∃ n, commutatorChain H n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent R›
  exact ⟨n, le_bot_iff.mp (hn ▸ commutatorChain_le_lowerCentralSeries H n)⟩

theorem commutatorChain_succ_lt (H : Subgroup R) [H.Normal] {n : ℕ}
    (hn : commutatorChain H n = ⊥) (hi : commutatorChain H i ≠ ⊥) :
    commutatorChain H (i + 1) < commutatorChain H i := by
  refine lt_of_le_of_ne (commutatorChain_succ_le H i) fun h => hi ?_
  have h1 : commutatorChain H (i + n) = commutatorChain H i := commutatorChain_add_of_succ_eq H h n
  have h2 : commutatorChain H (i + n) ≤ commutatorChain H n :=
    commutatorChain_antitone H (Nat.le_add_left n i)
  rw [hn, le_bot_iff] at h2
  rw [← h1, h2]

theorem commutatorElement_left_eq_iff (s x y : R) :
    ⁅x, s⁆ = ⁅y, s⁆ ↔ x⁻¹ * y ∈ centralizer ({s} : Set R) := by
  rw [mem_centralizer_singleton_iff, commutatorElement_def, commutatorElement_def]
  constructor
  · intro h
    have h1 : x * s * x⁻¹ = y * s * y⁻¹ := by
      have h2 := congrArg (· * s) h
      simpa [mul_assoc] using h2
    calc x⁻¹ * y * s = x⁻¹ * (y * s * y⁻¹) * y := by group
      _ = x⁻¹ * (x * s * x⁻¹) * y := by rw [h1]
      _ = s * (x⁻¹ * y) := by group
  · intro h
    have h2 : x⁻¹ * y * s * (x⁻¹ * y)⁻¹ = s := by rw [h]; group
    calc x * s * x⁻¹ * s⁻¹ = x * (x⁻¹ * y * s * (x⁻¹ * y)⁻¹) * x⁻¹ * s⁻¹ := by rw [h2]
      _ = y * s * y⁻¹ * s⁻¹ := by group

theorem relIndex_mul_natCard {A B : Subgroup R} (h : B ≤ A) :
    B.relIndex A * Nat.card B = Nat.card A := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.index_mul_card _

theorem relIndex_inf_centralizer_le_natCard [Finite R] (s : R) {A B : Subgroup R}
    (hAB : ∀ x ∈ A, ⁅x, s⁆ ∈ B) :
    (A ⊓ centralizer ({s} : Set R)).relIndex A ≤ Nat.card B := by
  have hwd : ∀ x y : ↥A, QuotientGroup.leftRel ((centralizer ({s} : Set R)).subgroupOf A) x y →
      (⟨⁅(x : R), s⁆, hAB x x.2⟩ : ↥B) = ⟨⁅(y : R), s⁆, hAB y y.2⟩ := by
    intro x y hxy
    have hmem : ((x : R))⁻¹ * (y : R) ∈ centralizer ({s} : Set R) := by
      have := QuotientGroup.leftRel_apply.mp hxy
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subtype.ext ((commutatorElement_left_eq_iff s x y).mpr hmem)
  set F : ↥A ⧸ ((centralizer ({s} : Set R)).subgroupOf A) → ↥B :=
    fun q => Quotient.liftOn' q (fun x => (⟨⁅(x : R), s⁆, hAB x x.2⟩ : ↥B)) hwd with hF
  have hFinj : Function.Injective F := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | _ x =>
    induction q₂ using QuotientGroup.induction_on with
    | _ y =>
    refine QuotientGroup.eq.mpr ?_
    have h' : ⁅(x : R), s⁆ = ⁅(y : R), s⁆ := congrArg Subtype.val h
    have := (commutatorElement_left_eq_iff s x y).mp h'
    simpa [Subgroup.mem_subgroupOf] using this
  rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left, Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective F hFinj

theorem exists_zpowers_eq_of_natCard_eq_prime (hp : p.Prime) (hS : Nat.card S = p) :
    ∃ s ∈ S, Subgroup.zpowers s = S := by
  have hfp : Fact (Nat.card S).Prime := ⟨hS ▸ hp⟩
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; exact hp.ne_zero)
  have hnt : Nontrivial S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hS]; exact hp.one_lt
  obtain ⟨s, hs1⟩ := exists_ne (1 : S)
  refine ⟨(s : R), s.2, le_antisymm (by rw [Subgroup.zpowers_le]; exact s.2) ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ : (⟨x, hx⟩ : S) ∈ Subgroup.zpowers s := mem_zpowers_of_prime_card rfl hs1
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem relIndex_commutatorChain_succ_eq_prime [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (H S : Subgroup R) [H.Characteristic] (hS : Nat.card S = p)
    (hCH : Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p)
    (hi : commutatorChain H i ≠ ⊥) :
    (commutatorChain H (i + 1)).relIndex (commutatorChain H i) = p := by
  have hfa : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  have : Group.IsNilpotent R := isNilpotent_of_natCard_eq_prime_pow hp ha
  obtain ⟨n, hn⟩ := exists_commutatorChain_eq_bot_of_isNilpotent H
  have hlt : commutatorChain H (i + 1) < commutatorChain H i := commutatorChain_succ_lt H hn hi
  obtain ⟨s, hsS, hs⟩ := exists_zpowers_eq_of_natCard_eq_prime hp hS
  have hCs : centralizer ({s} : Set R) = centralizer (S : Set R) := by
    rw [← hs, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCle : Nat.card (commutatorChain H i ⊓ centralizer ({s} : Set R) : Subgroup R) ≤ p := by
    rw [← hCH]
    exact Subgroup.card_le_of_le (inf_le_inf (commutatorChain_le H i) hCs.le)
  have hkey : Nat.card (commutatorChain H i) ≤ p * Nat.card (commutatorChain H (i + 1)) := by
    calc Nat.card (commutatorChain H i)
        = (commutatorChain H i ⊓ centralizer ({s} : Set R)).relIndex (commutatorChain H i) *
            Nat.card (commutatorChain H i ⊓ centralizer ({s} : Set R) : Subgroup R) :=
          (relIndex_mul_natCard inf_le_left).symm
      _ ≤ Nat.card (commutatorChain H (i + 1)) * p :=
          Nat.mul_le_mul (relIndex_inf_centralizer_le_natCard s
            (fun x hx => commutatorElement_mem_commutatorChain_succ H i hx s)) hCle
      _ = p * Nat.card (commutatorChain H (i + 1)) := by ring
  obtain ⟨k, hk⟩ := (hR.to_subgroup (commutatorChain H i)).exists_card_eq
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (hk ▸ Subgroup.relIndex_dvd_card (commutatorChain H (i + 1)) (commutatorChain H i))
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hlt.not_ge hj
  have hlow : p ≤ (commutatorChain H (i + 1)).relIndex (commutatorChain H i) := by
    rw [hj]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
  have hB0 : 0 < Nat.card (commutatorChain H (i + 1)) := Nat.card_pos
  have heq := relIndex_mul_natCard hlt.le
  have hle : (commutatorChain H (i + 1)).relIndex (commutatorChain H i) ≤ p := by
    by_contra h
    have hlt' : p * Nat.card (commutatorChain H (i + 1)) <
        (commutatorChain H (i + 1)).relIndex (commutatorChain H i) *
          Nat.card (commutatorChain H (i + 1)) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hB0
    omega
  omega

theorem exists_commutatorChain_eq_bot_and_relIndex_eq_prime [Finite R] (hp : p.Prime)
    (hR : IsPGroup p R) (H S : Subgroup R) [H.Characteristic] (hH : H ≠ ⊥) (hS : Nat.card S = p)
    (hCH : Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p) :
    ∃ n, 1 ≤ n ∧ commutatorChain H n = ⊥ ∧ (∀ i, (commutatorChain H i).Characteristic) ∧
      ∀ i, commutatorChain H i ≠ ⊥ →
        (commutatorChain H (i + 1)).relIndex (commutatorChain H i) = p := by
  classical
  have hfa : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  have : Group.IsNilpotent R := isNilpotent_of_natCard_eq_prime_pow hp ha
  have hex : ∃ n, commutatorChain H n = ⊥ := exists_commutatorChain_eq_bot_of_isNilpotent H
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun i => inferInstance, fun i hi =>
    relIndex_commutatorChain_succ_eq_prime hp hR H S hS hCH hi⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h
  · exact absurd ((commutatorChain_zero H) ▸ h0 ▸ Nat.find_spec hex) hH
  · exact h

end

end CFSG.FeitThompson
