module

public import CFSG.CGT.Timmesfeld75.Sec7OneDihedral
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

structure Endgame710 {X : Type} [Group X] [Finite X] (D : Set X) (M L : Subgroup X) (q : ℕ) :
    Prop where
  conj_mem : ∀ d ∈ D, ∀ g : X, g * d * g⁻¹ ∈ D
  sq_eq_one : ∀ d ∈ D, d * d = 1
  ne_one : ∀ d ∈ D, d ≠ 1
  order : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)) ∨
    ∃ k : ℕ, Odd k ∧ orderOf (d * e) = 2 * k
  four : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D
  M_comm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  M_sq : ∀ a ∈ M, a * a = 1
  M_gen : Subgroup.closure (D ∩ (M : Set X)) = M
  M_card : Nat.card M = q ^ 4
  gen : ∀ e ∈ D, e ∉ M → Subgroup.closure ((M : Set X) ∪ {e}) = ⊤
  exists_out : ∃ y ∈ D, y ∉ M
  H3 : ∀ β ∈ D, β ∈ M → ∀ d ∈ D, d * β = β * d → d ∈ M
  q_pow : ∃ m : ℕ, 2 ≤ m ∧ q = 2 ^ m
  card_Delta : Nat.card (D ∩ (M : Set X) : Set X) = (q + 1) * (q ^ 2 - 1)
  L_le : L ≤ M
  L_card : Nat.card L = q ^ 2
  L_D : ∀ l ∈ L, l ≠ 1 → l ∈ D
  L_TI : ∀ g : X, ∀ l ∈ L, l ≠ 1 → g * l * g⁻¹ ∈ L → ∀ l' ∈ L, g * l' * g⁻¹ ∈ L
  count65 : ∀ e ∈ D, e ∈ M → e ∉ L → Nat.card {l : X | l ∈ L ∧ e * l ∈ D} ≤ q

theorem isPGroup_two_zpowers_of_mul_self {K : Type*} [Group K] {b : K} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hb2]

theorem mem_smul_sylow_iff {H : Type*} [Group H] {p : ℕ} (P : Sylow p H) (g x : H) :
    x ∈ (g • P : Sylow p H) ↔ g⁻¹ * x * g ∈ P :=
  Subgroup.mem_pointwise_smul_iff_inv_smul_mem

theorem exists_fixed_conj {X : Type} [Group X] [Finite X] (P : Subgroup X) (hP : IsPGroup 2 P)
    (Δ : Set X) (hΔ : ∀ s ∈ P, ∀ d ∈ Δ, s * d * s⁻¹ ∈ Δ) (hodd : Odd (Nat.card Δ)) :
    ∃ d ∈ Δ, ∀ s ∈ P, s * d * s⁻¹ = d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P Δ :=
    { smul := fun s d => ⟨(s : X) * d * (s : X)⁻¹, hΔ s s.2 d d.2⟩
      one_smul := fun d => Subtype.ext (by
        change ((1 : P) : X) * (d : X) * ((1 : P) : X)⁻¹ = d
        simp)
      mul_smul := fun s t d => Subtype.ext (by
        change ((s * t : P) : X) * (d : X) * ((s * t : P) : X)⁻¹ =
          (s : X) * ((t : X) * (d : X) * (t : X)⁻¹) * (s : X)⁻¹
        simp [mul_assoc]) }
  have hnd : ¬ 2 ∣ Nat.card Δ := by
    obtain ⟨c, hc⟩ := hodd
    omega
  obtain ⟨⟨d, hd⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Δ hnd
  refine ⟨d, hd, fun s hs => ?_⟩
  have := MulAction.mem_fixedPoints.1 hfix ⟨s, hs⟩
  exact congrArg Subtype.val this

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem q_ge : 4 ≤ q := by
  obtain ⟨m, hm, rfl⟩ := h.q_pow
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem q_even : Even q := by
  obtain ⟨m, hm, rfl⟩ := h.q_pow
  exact (Nat.even_pow.2 ⟨even_two, by omega⟩)

theorem inv_eq {d : X} (hd : d ∈ D) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (h.sq_eq_one d hd)

theorem exists_mem_delta : ∃ β ∈ D, β ∈ M := by
  have hq := h.q_ge
  have hL : 1 < Nat.card L := by
    rw [h.L_card]
    nlinarith
  have hnt : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 hL
  obtain ⟨⟨l, hl⟩, hne⟩ := exists_ne (1 : L)
  have hl1 : l ≠ 1 := fun h' => hne (Subtype.ext h')
  exact ⟨l, h.L_D l hl hl1, h.L_le hl⟩

theorem isPGroup_M : IsPGroup 2 M := by
  obtain ⟨m, -, hq⟩ := h.q_pow
  exact IsPGroup.of_card (n := 4 * m) (by rw [h.M_card, hq, ← pow_mul]; ring_nf)

theorem exists_sylow : ∃ S : Sylow 2 X, M ≤ S := h.isPGroup_M.exists_le_sylow

theorem order_ne_four {d β : X} (hd : d ∈ D) (hdM : d ∉ M) (hβ : β ∈ D) (hβM : β ∈ M) :
    orderOf (d * β) ≠ 4 := by
  intro ho
  have hε := h.four d hd β hβ ho
  have hd2 := h.sq_eq_one d hd
  have hβ2 := h.sq_eq_one β hβ
  have hk : (d * β) ^ (2 * 2) = 1 := by
    rw [show 2 * 2 = 4 from rfl, ← ho]
    exact pow_orderOf_eq_one _
  obtain ⟨hcd, hcβ⟩ := dihedral_center_comm hd2 hβ2 (k := 2) hk
  have hεM : (d * β) ^ 2 ∈ M := h.H3 β hβ hβM _ hε hcβ.symm
  exact hdM (h.H3 _ hε hεM d hd hcd)

theorem order_cases {d β : X} (hd : d ∈ D) (hdM : d ∉ M) (hβ : β ∈ D) (hβM : β ∈ M) :
    ∃ k : ℕ, Odd k ∧ 3 ≤ k ∧ (orderOf (d * β) = k ∨ orderOf (d * β) = 2 * k) := by
  have hd2 := h.sq_eq_one d hd
  have hβ2 := h.sq_eq_one β hβ
  have hpos : 0 < orderOf (d * β) := orderOf_pos _
  rcases h.order d hd β hβ with h4 | hodd | ⟨k, hk, hk2⟩
  · exact absurd h4 (h.order_ne_four hd hdM hβ hβM)
  · refine ⟨orderOf (d * β), hodd, ?_, Or.inl rfl⟩
    obtain ⟨c, hc⟩ := hodd
    by_contra hlt
    have h1 : orderOf (d * β) = 1 := by omega
    have : d * β = 1 := orderOf_eq_one_iff.1 h1
    have hdβ : d = β := by
      calc d = d * β * β⁻¹ := by group
        _ = β⁻¹ := by rw [this, one_mul]
        _ = β := h.inv_eq hβ
    exact hdM (hdβ ▸ hβM)
  · refine ⟨k, hk, ?_, Or.inr hk2⟩
    by_contra hlt
    obtain ⟨c, hc⟩ := hk
    have hk1 : k = 1 := by omega
    subst hk1
    have h2 : (d * β) * (d * β) = 1 := by
      have h22 : orderOf (d * β) = 2 := by simpa using hk2
      have : (d * β) ^ 2 = 1 := by rw [← h22]; exact pow_orderOf_eq_one _
      rwa [pow_two] at this
    have hcomm : d * β = β * d := by
      have h3 : d * β = (d * β)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [h3, dihedral_inv hd2 hβ2]
    exact hdM (h.H3 β hβ hβM d hd hcomm)

theorem mem_M_of_mem_sylow (S : Sylow 2 X) (hMS : M ≤ S) {d : X} (hd : d ∈ D) (hdS : d ∈ S) :
    d ∈ M := by
  by_contra hdM
  obtain ⟨β, hβ, hβM⟩ := h.exists_mem_delta
  obtain ⟨k, hk, hk3, hcase⟩ := h.order_cases hd hdM hβ hβM
  have hmem : d * β ∈ (S : Subgroup X) := (S : Subgroup X).mul_mem hdS (hMS hβM)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨d * β, hmem⟩
  have hj' : orderOf (d * β) = 2 ^ j := by
    rw [← hj]
    exact (Subgroup.orderOf_mk _ _).symm
  have hkdvd : k ∣ 2 ^ j := by
    rcases hcase with h1 | h1
    · rw [← hj', h1]
    · rw [← hj', h1]
      exact dvd_mul_left k 2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkdvd
  obtain ⟨c, hc⟩ := hk
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp at hi
    omega
  · have : 2 ∣ k := by
      rw [hi]
      exact dvd_pow_self 2 (by omega)
    omega

theorem exists_conj_mem {d : X} (hd : d ∈ D) : ∃ g : X, g⁻¹ * d * g ∈ M := by
  obtain ⟨S, hMS⟩ := h.exists_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := (isPGroup_two_zpowers_of_mul_self (h.sq_eq_one d hd)).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X S S'
  have hdS' : d ∈ (g • S : Sylow 2 X) := hS' (Subgroup.mem_zpowers d)
  have hdS : g⁻¹ * d * g ∈ S := (mem_smul_sylow_iff S g d).1 hdS'
  exact ⟨g, h.mem_M_of_mem_sylow S hMS (by
    simpa [mul_assoc] using h.conj_mem d hd g⁻¹) hdS⟩

theorem odd_card_delta : Odd (Nat.card (D ∩ (M : Set X) : Set X)) := by
  rw [h.card_Delta]
  have hq := h.q_ge
  obtain ⟨m, hm, hqm⟩ := h.q_pow
  have h1 : Odd (q + 1) := h.q_even.add_one
  have h2 : Odd (q ^ 2 - 1) := by
    have : Even (q ^ 2) := (Nat.even_pow.2 ⟨h.q_even, by norm_num⟩)
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    obtain ⟨c, hc⟩ := this
    exact ⟨c - 1, by omega⟩
  exact h1.mul h2

theorem exists_fixed (S : Sylow 2 X) (hMS : M ≤ S) :
    ∃ γ ∈ D, γ ∈ M ∧ ∀ s ∈ S, s * γ * s⁻¹ = γ := by
  have hΔ : ∀ s ∈ (S : Subgroup X), ∀ d ∈ (D ∩ (M : Set X) : Set X),
      s * d * s⁻¹ ∈ (D ∩ (M : Set X) : Set X) := by
    intro s hs d hd
    refine ⟨h.conj_mem d hd.1 s, h.mem_M_of_mem_sylow S hMS (h.conj_mem d hd.1 s) ?_⟩
    exact (S : Subgroup X).mul_mem ((S : Subgroup X).mul_mem hs (hMS hd.2))
      ((S : Subgroup X).inv_mem hs)
  obtain ⟨γ, hγ, hfix⟩ := exists_fixed_conj (S : Subgroup X) S.isPGroup' _ hΔ h.odd_card_delta
  exact ⟨γ, hγ.1, hγ.2, hfix⟩

end Endgame710

end CFSG.CGT.T75F
