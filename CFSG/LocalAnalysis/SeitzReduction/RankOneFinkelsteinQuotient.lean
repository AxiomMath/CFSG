module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinBasic
public import Mathlib.Data.Int.Star

public section

namespace CFSG.SeitzReduction.RankOne.Finkelstein

open CFSG.ComponentClassification.GMS78.Finkelstein

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U}

namespace Hyp

variable (h : Hyp U n t y)
include h

theorem fix_normal : (fixSubgroup t).Normal :=
  Subgroup.normal_of_le_center h.fix_le_center

omit h in
theorem map_fix_of_comm {s : MulAut U} (hs : t * s = s * t) :
    (fixSubgroup t).map (s : U →* U) = fixSubgroup t := by
  have hle : (fixSubgroup t).map (s : U →* U) ≤ fixSubgroup t := by
    rintro _ ⟨a, ha, rfl⟩
    show t (s a) = s a
    rw [← MulAut.mul_apply, hs, MulAut.mul_apply, show t a = a from ha]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective s.injective])

theorem psi_mul_of_mem {u : U} (hu : psi t u ∈ fixSubgroup t) (v : U) :
    psi t (u * v) = psi t u * psi t v := by
  have hc := h.mem_center_of_mem_fix hu v⁻¹
  simp only [psi, map_mul, mul_inv_rev] at hc ⊢
  calc v⁻¹ * u⁻¹ * (t u * t v) = (v⁻¹ * (u⁻¹ * t u)) * t v := by group
    _ = ((u⁻¹ * t u) * v⁻¹) * t v := by rw [hc]
    _ = u⁻¹ * t u * (v⁻¹ * t v) := by group

theorem psi_inv_of_mem {u : U} (hu : psi t u ∈ fixSubgroup t) : psi t u⁻¹ = (psi t u)⁻¹ := by
  have h1 := h.psi_mul_of_mem hu u⁻¹
  rw [mul_inv_cancel, psi_eq_one_iff.mpr (one_mem _), eq_comm, mul_eq_one_iff_eq_inv'] at h1
  exact h1

omit [Finite U] in
theorem psi_pow_y (k : ℕ) (u : U) : psi t ((y ^ k) u) = (y ^ k) (psi t u) := by
  rw [psi, psi, h.t_pow_y, ← map_inv, ← map_mul]

variable [(fixSubgroup t).Normal]

omit h in
@[expose] noncomputable def quotAut (s : MulAut U)
    (hs : (fixSubgroup t).map (s : U →* U) = fixSubgroup t) : MulAut (U ⧸ fixSubgroup t) :=
  QuotientGroup.congr (fixSubgroup t) (fixSubgroup t) s hs

omit h [Finite U] in
theorem quotAut_mk (s : MulAut U) (hs : (fixSubgroup t).map (s : U →* U) = fixSubgroup t)
    (u : U) : quotAut s hs (u : U ⧸ fixSubgroup t) = ((s u : U) : U ⧸ fixSubgroup t) :=
  QuotientGroup.congr_mk _ _ _ _ u

omit h [Finite U] in
theorem quotAut_pow_mk (s : MulAut U) (hs : (fixSubgroup t).map (s : U →* U) = fixSubgroup t)
    (k : ℕ) (u : U) :
    (quotAut s hs ^ k) (u : U ⧸ fixSubgroup t) = (((s ^ k) u : U) : U ⧸ fixSubgroup t) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, quotAut_mk, pow_succ', MulAut.mul_apply]

omit h in
theorem quotAut_mk_eq_iff (u : U) :
    quotAut t (map_fix_of_comm (s := t) rfl) (u : U ⧸ fixSubgroup t) = (u : U ⧸ fixSubgroup t) ↔
      psi t u ∈ fixSubgroup t := by
  rw [quotAut_mk, eq_comm, QuotientGroup.eq]
  rfl

theorem quot_pow_eq_iff {a : U} (ha : psi t a ∈ fixSubgroup t) (b : U) (k : ℕ) :
    (quotAut y (map_fix_of_comm (s := y) h.comm) ^ k) (a : U ⧸ fixSubgroup t) =
        (b : U ⧸ fixSubgroup t) ↔ (y ^ k) (psi t a) = psi t b := by
  rw [quotAut_pow_mk, QuotientGroup.eq]
  set c := (y ^ k) a with hc
  have hcA : psi t c ∈ fixSubgroup t := by
    rw [hc, h.psi_pow_y]
    exact h.pow_mem_fix k ha
  have hmem : c⁻¹ * b ∈ fixSubgroup t ↔ psi t (c⁻¹ * b) = 1 := psi_eq_one_iff.symm
  rw [hmem, h.psi_mul_of_mem (by rw [h.psi_inv_of_mem hcA]; exact inv_mem hcA),
    h.psi_inv_of_mem hcA, inv_mul_eq_one, hc, h.psi_pow_y]

theorem quot (hA : fixSubgroup t ≠ ⊤) :
    Hyp (U ⧸ fixSubgroup t) n (quotAut t (map_fix_of_comm (s := t) rfl))
      (quotAut y (map_fix_of_comm (s := y) h.comm)) := by
  set tb := quotAut t (map_fix_of_comm (s := t) rfl) with htb
  set yb := quotAut y (map_fix_of_comm (s := y) h.comm) with hyb
  have hfixb : ∀ x : U ⧸ fixSubgroup t, tb x = x → x ≠ 1 →
      ∃ u : U, (u : U ⧸ fixSubgroup t) = x ∧ psi t u ∈ fixSubgroup t ∧ psi t u ≠ 1 := by
    intro x hx hx1
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨u, rfl, (quotAut_mk_eq_iff u).mp hx, fun h1 => hx1 ?_⟩
    exact (QuotientGroup.eq_one_iff u).mpr (psi_eq_one_iff.mp h1)
  have hreg : ∀ a b : U ⧸ fixSubgroup t, tb a = a → tb b = b → a ≠ 1 → b ≠ 1 →
      ∃! k : ℕ, k < 2 ^ n - 1 ∧ (yb ^ k) a = b := by
    intro a b ha hb ha1 hb1
    obtain ⟨a, rfl, haA, ha1'⟩ := hfixb a ha ha1
    obtain ⟨b, rfl, hbA, hb1'⟩ := hfixb b hb hb1
    obtain ⟨k, ⟨hk, hkab⟩, hu⟩ := h.reg _ _ haA hbA ha1' hb1'
    refine ⟨k, ⟨hk, (h.quot_pow_eq_iff haA b k).mpr hkab⟩, fun k' ⟨hk', hk'ab⟩ => ?_⟩
    exact hu k' ⟨hk', (h.quot_pow_eq_iff haA b k').mp hk'ab⟩
  have hsq : tb ^ 2 = 1 := by
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [pow_two, MulAut.mul_apply, htb, quotAut_mk, quotAut_mk, h.t_t, MulAut.one_apply]
  have hfix1 : ∃ x : U ⧸ fixSubgroup t, tb x = x ∧ x ≠ 1 := by
    have heven : 2 ∣ Nat.card (U ⧸ fixSubgroup t) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h.pgroup
      have hdvd : Nat.card (U ⧸ fixSubgroup t) ∣ 2 ^ m :=
        hm ▸ Subgroup.card_quotient_dvd_card _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_eq_one] at hj
        exact hA hj
      rw [hj]
      exact dvd_pow_self 2 hj0
    have hinv : Function.Involutive tb := fun x => by
      rw [← MulAut.mul_apply, ← pow_two, hsq, MulAut.one_apply]
    obtain ⟨x, hx1, hx⟩ := exists_ne_fixed_of_involutive hinv heven (x₀ := 1) (map_one tb)
    exact ⟨x, hx, hx1⟩
  refine ⟨h.pgroup.to_quotient _, h.two_le, hsq, ?_, ?_, hreg⟩
  · ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, MulAut.mul_apply, htb, hyb, quotAut_mk, quotAut_mk, quotAut_mk,
      quotAut_mk, h.t_y]
  · have hpos : 0 < 2 ^ n - 1 := by have := h.three_le; omega
    rw [orderOf_eq_iff hpos]
    refine ⟨?_, fun k hk hk0 hyk => ?_⟩
    · ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hyb, quotAut_pow_mk, ← h.order, pow_orderOf_eq_one, MulAut.one_apply, MulAut.one_apply]
    · obtain ⟨x, hx, hx1⟩ := hfix1
      obtain ⟨k₀, -, hu⟩ := hreg x x hx hx hx1 hx1
      have e1 : k = k₀ := hu k ⟨hk, by rw [hyk, MulAut.one_apply]⟩
      have e2 : 0 = k₀ := hu 0 ⟨hpos, by rw [pow_zero, MulAut.one_apply]⟩
      omega

omit [(fixSubgroup t).Normal] in
theorem natCard_eq_quot_mul :
    letI := h.fix_normal
    Nat.card U = Nat.card (U ⧸ fixSubgroup t) * 2 ^ n := by
  have := h.fix_normal
  rw [← h.natCard_fix]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

end Hyp

theorem Hyp.exists_natCard_eq {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U}
    (h : Hyp U n t y) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card U = 2 ^ (n * m) := by
  suffices H : ∀ N : ℕ, ∀ (V : Type) [Group V] [Finite V] (t y : MulAut V), Hyp V n t y →
      Nat.card V = N → ∃ m : ℕ, 1 ≤ m ∧ Nat.card V = 2 ^ (n * m) from H _ U t y h rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ t y h hN
    have := h.fix_normal
    by_cases hA : fixSubgroup t = ⊤
    · refine ⟨1, le_rfl, ?_⟩
      rw [mul_one, ← h.natCard_fix, hA, Subgroup.card_top]
    · have hq := h.quot hA
      have hcard := h.natCard_eq_quot_mul
      have hlt : Nat.card (V ⧸ fixSubgroup t) < N := by
        rw [← hN, hcard]
        have h1 : 0 < Nat.card (V ⧸ fixSubgroup t) := Nat.card_pos
        have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.two_le; omega)
        nlinarith
      obtain ⟨m, -, hm⟩ := ih _ hlt _ _ _ hq rfl
      refine ⟨m + 1, by omega, ?_⟩
      rw [hcard, hm, ← pow_add, mul_add, mul_one]

end CFSG.SeitzReduction.RankOne.Finkelstein
