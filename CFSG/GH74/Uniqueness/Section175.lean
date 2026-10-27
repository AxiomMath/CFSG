module

public import CFSG.GH74.Uniqueness.Section173Basic
public import CFSG.GH74.Uniqueness.Bender.LinearOdd

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem Sec175.linear_arith {q c N : ℕ} (hq : 1 < q) (hc : c ≡ 1 [MOD q])
    (hc1 : c ≠ 1) (hN : N = q - 1 ∨ N = q + 1) (hdvd : c ∣ N) : c = q + 1 := by
  have hmod : c % q = 1 := by
    have := hc; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt hq
  have hcq := Nat.div_add_mod c q
  rw [hmod] at hcq
  have hk1 : 1 ≤ c / q := by
    rcases Nat.eq_zero_or_pos (c / q) with h | h
    · rw [h] at hcq; omega
    · exact h
  have hcq1 : q + 1 ≤ c := by nlinarith
  have hN0 : 0 < N := by omega
  have hcN : c ≤ N := Nat.le_of_dvd hN0 hdvd
  omega

theorem ZDSetup.lemma175
    (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (h171 : Lemma171Stmt Z M)
    (h172 : Lemma172Stmt Z M) : Lemma175Stmt Z M := by
  intro c n e hB
  obtain ⟨A, s, hAB, hAodd, hsB, hs2, hs1, hsA, hcEq, hc1, hc2, -, -⟩ :=
    S.exists_pair_B0 h166 h172 c hB
  have he : e = 1 := by
    rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact he
    · omega
    · omega
  subst he
  set F : Subgroup X := cenHull Z c.u with hF
  have hBF : Bender.BenderType ↥F n 1 1 := S.benderType_of_benderSub hB (Or.inl rfl)
  have hn2 : 2 ≤ n := hBF.two_le.2
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    exact hc2 (Subgroup.relIndex_bot_right _)
  obtain ⟨hcard', hA'1, -, -, hsN⟩ := Sec173.subgroupOf_facts hAB hsB hs2 hs1 hsA hA1
  have hA'odd : Odd (Nat.card ↥(A.subgroupOf F)) := by rw [hcard']; exact hAodd
  obtain ⟨T, w, hAT, -, -, hTcard, -, -, -, -, hinv⟩ := hBF.linear_odd_subgroup hA'odd hA'1
  have hinvX : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹ := by
    intro a ha
    have h1 := hinv ⟨s, hsB⟩ (Subtype.ext hs2) (fun h => hs1 (congrArg Subtype.val h)) hsN
      ⟨a, hAB ha⟩ (hAT (Subgroup.mem_subgroupOf.mpr ha))
    exact congrArg Subtype.val h1
  have hc : (centralizer ({s} : Set X)).relIndex A = Nat.card A :=
    Sec173.relIndex_eq_card_of_inv hAodd hinvX
  have hdvd : Nat.card A ∣ Nat.card T := by
    rw [← hcard']
    exact Subgroup.card_dvd_of_le hAT
  rw [hc] at hc1 hc2 hcEq
  have hcq : Nat.card A = 2 ^ n + 1 := Sec175.linear_arith hq hc1 hc2 hTcard hdvd
  set H : Subgroup X := c.D ⊓ centralizer ({c.t, c.u} : Set X) with hH
  have hHu : H ≤ c.D ⊓ centralizer ({c.u} : Set X) := by
    refine inf_le_inf_left _ fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact hx y (Set.mem_insert_of_mem _ hy)
  have hHtu : H ≤ c.D ⊓ centralizer ({c.t * c.u} : Set X) := by
    refine inf_le_inf_left _ fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hx c.t (Set.mem_insert _ _)
    have h2 := hx c.u (Set.mem_insert_of_mem _ rfl)
    calc x * (c.t * c.u) = (x * c.t) * c.u := by group
      _ = c.t * x * c.u := by rw [h1]
      _ = c.t * (x * c.u) := by group
      _ = c.t * (c.u * x) := by rw [h2]
      _ = c.t * c.u * x := by group
  have e1 := Subgroup.relIndex_mul_card H (c.D ⊓ centralizer ({c.u} : Set X))
  have e2 := Subgroup.relIndex_mul_card H (c.D ⊓ centralizer ({c.t * c.u} : Set X))
  rw [inf_eq_left.mpr hHu] at e1
  rw [inf_eq_left.mpr hHtu] at e2
  have h172a := (h172 c n 1 1 hB).1
  rw [h172a] at e1
  rw [hcEq, hcq] at e2
  obtain ⟨hΩ, h171⟩ := h171 c n 1 1 hB
  rw [← e1, ← e2, pow_one] at h171
  have hHpos : 0 < Nat.card H := Nat.card_pos
  set q : ℕ := 2 ^ n with hqdef
  set Ω : ℕ := (omega M).ncard with hΩdef
  rw [pow_one] at hΩ
  have key : (Ω - (q + 1)) * ((q + 1) * Nat.card H) = (q * (q - 1)) * ((q + 1) * Nat.card H) := by
    rw [h171]
    ring
  have hpos : 0 < (q + 1) * Nat.card H := Nat.mul_pos (by omega) hHpos
  have key' := Nat.eq_of_mul_eq_mul_right hpos key
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  rw [hk] at key' hΩ ⊢
  rw [show k + 1 - 1 = k by omega] at key'
  have : Ω = (k + 1) * k + (k + 1 + 1) := by omega
  rw [this]
  ring

end CFSG.GH74.Uniqueness
