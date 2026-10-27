module

public import CFSG.LieType.Steinberg.CentralExt.SLMilnor

public section

open Matrix
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

variable {m : ℕ} {F : Type} [Field F]

theorem commutatorElement_swap {G : Type*} [Group G] {a b c : G} (hab : a * b = b * a)
    (h : ⁅a, c⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆) : ⁅a, ⁅b, c⁆⁆ = ⁅b, ⁅a, c⁆⁆ := by
  have hb : a * b * a⁻¹ = b := by rw [hab, mul_inv_cancel_right]
  have hc : a * c * a⁻¹ = ⁅a, c⁆ * c := by
    rw [commutatorElement_def]
    group
  have e : ⁅b, ⁅a, c⁆ * c⁆ = ⁅b, ⁅a, c⁆⁆ * (⁅a, c⁆ * ⁅b, c⁆ * ⁅a, c⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  calc ⁅a, ⁅b, c⁆⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅b, c⁆⁻¹ := commutatorElement_def _ _
    _ = ⁅b, ⁅a, c⁆ * c⁆ * ⁅b, c⁆⁻¹ := by rw [conjugate_commutatorElement, hb, hc]
    _ = ⁅b, ⁅a, c⁆⁆ := by rw [e, h, mul_inv_cancel_right, mul_inv_cancel_right]

theorem eq_zero_or_one_or_neg_one [Finite F] (hF : Nat.card F = 3) (x : F) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h3 : (3 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rwa [Fintype.card_eq_nat_card, hF, Nat.cast_ofNat] at this
  have h1 : (1 : F) ≠ -1 := fun e => one_ne_zero (by linear_combination (-1 : F) * e + h3)
  by_contra hx
  push Not at hx
  obtain ⟨hx0, hx1, hxn⟩ := hx
  have h01 : (0 : F) ∉ ({1, -1, x} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, fun e => one_ne_zero (neg_eq_zero.1 e.symm), Ne.symm hx0⟩
  have h11 : (1 : F) ∉ ({-1, x} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, Ne.symm hx1⟩
  have hcard : ({0, 1, -1, x} : Finset F).card = 4 := by
    rw [Finset.card_insert_of_notMem h01, Finset.card_insert_of_notMem h11,
      Finset.card_pair (Ne.symm hxn)]
  have := Finset.card_le_univ ({0, 1, -1, x} : Finset F)
  rw [hcard, Fintype.card_eq_nat_card, hF] at this
  omega

theorem eq_one_of_biadditive_three [Finite F] (hF : Nat.card F = 3) {G : Type*} [Group G]
    {H : F → F → G} (h1 : ∀ u u' v, H (u + u') v = H u v * H u' v)
    (h2 : ∀ u v v', H u (v + v') = H u v * H u v') (hsym : H (-1) 1 = H 1 1) (u v : F) :
    H u v = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h3 : (1 + 1 + 1 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rw [Fintype.card_eq_nat_card, hF, Nat.cast_ofNat] at this
    linear_combination this
  have hz1 : ∀ v, H 0 v = 1 := fun v => by
    have := h1 0 0 v
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hz2 : ∀ u, H u 0 = 1 := fun u => by
    have := h2 u 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hneg1 : ∀ v, H (-1) v * H 1 v = 1 := fun v => by
    rw [← h1, neg_add_cancel, hz1]
  have hneg2 : ∀ u, H u (-1) * H u 1 = 1 := fun u => by
    rw [← h2, neg_add_cancel, hz2]
  have hsq : H 1 1 * H 1 1 = 1 := by
    have := hneg1 1
    rwa [hsym] at this
  have hcube : H 1 1 * H 1 1 * H 1 1 = 1 := by
    rw [← h1, ← h1, h3, hz1]
  have h11 : H 1 1 = 1 := by
    rw [hsq, one_mul] at hcube
    exact hcube
  have h1v : ∀ v, H 1 v = 1 := fun v => by
    rcases eq_zero_or_one_or_neg_one hF v with rfl | rfl | rfl
    · exact hz2 1
    · exact h11
    · have := hneg2 1
      rwa [h11, mul_one] at this
  rcases eq_zero_or_one_or_neg_one hF u with rfl | rfl | rfl
  · exact hz1 v
  · exact h1v v
  · have := hneg1 v
    rwa [h1v, mul_one] at this

section Lift

variable {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π) (hm : 2 ≤ m)
  (hsep : SeparatingOverlap m F)
include hcen hπ hm hsep

theorem X_comm_mem_center {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s t : F) : ⁅X π i j s, X π k l t⁆ ∈ Subgroup.center E := by
  apply hcen
  rw [MonoidHom.mem_ker, map_commutatorElement, (X_spec hcen hπ hm hsep hij).2.1,
    (X_spec hcen hπ hm hsep hkl).2.1, commutatorElement_eq_one_iff_mul_comm]
  exact tv_commute hij hkl hjk hli s t

theorem X_comm_disjoint_A {i j k l : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hkl : k ≠ l) (s t : F) :
    ⁅X π i j s, X π k l t⁆ = ⁅X π k j (-(1 * t * s)), X π i l 1⁆ := by
  have hXkj := (X_spec hcen hπ hm hsep (Ne.symm hjk)).1
  have hbc : ⁅X π k i t, X π i l 1⁆ = X π k l t := by
    rw [X_chain hcen hπ hm hsep hik.symm hil hkl t 1, one_mul, mul_one]
  have hab : ⁅X π i j s, X π k i t⁆ = X π k j (-(1 * t * s)) := by
    rw [← commutatorElement_inv, X_chain hcen hπ hm hsep hik.symm hij (Ne.symm hjk) t s,
      TorusLift.x_neg hXkj]
  have hcomm : ⁅X π i j s, X π k i t⁆ * ⁅X π k i t, X π i l 1⁆ =
      ⁅X π k i t, X π i l 1⁆ * ⁅X π i j s, X π k i t⁆ := by
    rw [hab, hbc]
    exact X_commute_overlap hcen hπ hm hsep (Ne.symm hjk) hkl hjk (Ne.symm hkl) (Or.inl rfl) _ _
  have hcen' : ⁅⁅X π i j s, X π k i t⁆, X π i l 1⁆ ∈ Subgroup.center E := by
    rw [hab]
    exact X_comm_mem_center hcen hπ hm hsep (Ne.symm hjk) hil (Ne.symm hij) (Ne.symm hkl) _ _
  rw [← hbc, commutatorElement_assoc
    (X_commute_overlap hcen hπ hm hsep hij hil hij.symm hil.symm (Or.inl rfl) s 1) hcomm
    ((Subgroup.mem_center_iff.1 hcen') _).symm, hab]

theorem X_comm_disjoint_B {i j k l : Fin (m + 1)} (hij : i ≠ j) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (s t : F) :
    ⁅X π i j s, X π k l t⁆ = ⁅X π k j t, X π i l (1 * s * 1)⁆ := by
  have hbc : ⁅X π k j t, X π j l 1⁆ = X π k l t := by
    rw [X_chain hcen hπ hm hsep (Ne.symm hjk) hjl hkl t 1, one_mul, mul_one]
  have hac : ⁅X π i j s, X π j l 1⁆ = X π i l (1 * s * 1) := X_chain hcen hπ hm hsep hij hjl hil s 1
  have hcomm : ⁅X π i j s, X π j l 1⁆ * ⁅X π k j t, X π j l 1⁆ =
      ⁅X π k j t, X π j l 1⁆ * ⁅X π i j s, X π j l 1⁆ := by
    rw [hac, hbc]
    exact X_commute_overlap hcen hπ hm hsep hil hkl (Ne.symm hkl) (Ne.symm hil)
      (Or.inr (Or.inr (Or.inr rfl))) _ _
  rw [← hbc, commutatorElement_swap
    (X_commute_overlap hcen hπ hm hsep hij (Ne.symm hjk) hjk (Ne.symm hij)
      (Or.inr (Or.inr (Or.inr rfl))) s t) hcomm, hac]

theorem X_commute_of_card_three [Finite F] (hF : Nat.card F = 3) {i j k l : Fin (m + 1)}
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (s t : F) :
    X π i j s * X π k l t = X π k l t * X π i j s := by
  by_cases hov : k = i ∨ k = j ∨ l = i ∨ l = j
  · exact X_commute_overlap hcen hπ hm hsep hij hkl hjk hli hov s t
  push Not at hov
  obtain ⟨hki, hkj, hli', hlj⟩ := hov
  have hX := (X_spec hcen hπ hm hsep (Ne.symm hjk)).1
  have hY := (X_spec hcen hπ hm hsep (Ne.symm hli)).1
  have hH : ∀ u v, ⁅X π k j u, X π i l v⁆ ∈ Subgroup.center E := fun u v =>
    X_comm_mem_center hcen hπ hm hsep (Ne.symm hjk) (Ne.symm hli) (Ne.symm hij) (Ne.symm hkl) u v
  have h1 : ∀ u u' v, ⁅X π k j (u + u'), X π i l v⁆ = ⁅X π k j u, X π i l v⁆ *
      ⁅X π k j u', X π i l v⁆ := fun u u' v => by
    rw [hX, TorusLift.commutatorElement_mul_left_of_central (hH u' v)]
  have h2 : ∀ u v v', ⁅X π k j u, X π i l (v + v')⁆ = ⁅X π k j u, X π i l v⁆ *
      ⁅X π k j u, X π i l v'⁆ := fun u v v' => by
    rw [hY, TorusLift.commutatorElement_mul_right_of_central (hH u v')]
  have hsym : ⁅X π k j (-1), X π i l 1⁆ = ⁅X π k j 1, X π i l 1⁆ := by
    have hA := X_comm_disjoint_A hcen hπ hm hsep hij (Ne.symm hki) (Ne.symm hli) hjk hkl 1 1
    have hB := X_comm_disjoint_B hcen hπ hm hsep hij (Ne.symm hli) hjk (Ne.symm hlj) hkl 1 1
    rw [mul_one, mul_one] at hA hB
    exact hA.symm.trans hB
  have hone := eq_one_of_biadditive_three (H := fun u v => ⁅X π k j u, X π i l v⁆) hF h1 h2 hsym t
    (1 * s * 1)
  rw [← commutatorElement_eq_one_iff_mul_comm, X_comm_disjoint_B hcen hπ hm hsep hij
    (Ne.symm hli) hjk (Ne.symm hlj) hkl]
  exact hone

end Lift

theorem sl_exists_section_of_card_three [Finite F] (hm : 3 ≤ m) (hF : Nat.card F = 3)
    {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g := by
  have : Fintype F := Fintype.ofFinite F
  have hch : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h
    rw [Fintype.card_eq_nat_card, hF] at this
    exact absurd this (by decide)
  have hne : ((-1 : Fˣ) : F) ≠ 1 := by
    rw [Units.val_neg, Units.val_one]
    exact Ring.neg_one_ne_one_of_char_ne_two hch
  have hsep := separatingOverlap_of_three_le hm (-1) hne
  have hm2 : 2 ≤ m := by omega
  exact exists_section_of_lifts (X π) (fun _ _ h => (X_spec hcen hπ hm2 hsep h).1)
    (fun _ _ _ _ hij hkl hjk hli => X_commute_of_card_three hcen hπ hm2 hsep hF hij hkl hjk hli)
    (fun _ _ _ hij hjl hil => X_chain hcen hπ hm2 hsep hij hjl hil)
    (fun _ _ h => (X_spec hcen hπ hm2 hsep h).2.1) hm2

end CFSG.LieType.Steinberg.CentralExt.SLClosed
