module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Count
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Classical

variable {G : Type*} [Group G] {K : Type*} [Field K]

section Kernel

variable [Finite G]

theorem nine_le_card_ker (hG : Nat.card G = 27) (ψ : G →* Kˣ) (hψ : ∀ x, ψ x ^ 3 = 1) :
    9 ≤ Nat.card ψ.ker := by
  have h1 := index_ker_le_three ψ hψ
  have e := Subgroup.card_mul_index ψ.ker
  rw [hG] at e
  by_contra hlt
  have : Nat.card ψ.ker * ψ.ker.index ≤ 8 * 3 := Nat.mul_le_mul (by omega) h1
  omega

omit [Finite G] in
theorem card_ker_le_nine (hG : Nat.card G = 27) (ψ : G →* Kˣ) (hψ1 : ψ ≠ 1) :
    Nat.card ψ.ker ≤ 9 := by
  have e := Subgroup.card_mul_index ψ.ker
  rw [hG] at e
  have hne : ψ.ker ≠ ⊤ := fun h =>
    hψ1 (MonoidHom.ext fun x => (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x))
  have hidx : ψ.ker.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hdvd : Nat.card ψ.ker ∈ Nat.divisors 27 :=
    Nat.mem_divisors.2 ⟨⟨_, e.symm⟩, by norm_num⟩
  have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [hd] at hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdvd
  rcases hdvd with h | h | h | h
  · omega
  · omega
  · omega
  · rw [h] at e
    exact absurd (by omega) hidx

theorem three_le_card_inf (hG : Nat.card G = 27) (ψ φ : G →* Kˣ) (hψ : ∀ x, ψ x ^ 3 = 1)
    (hφ : ∀ x, φ x ^ 3 = 1) : 3 ≤ Nat.card (ψ.ker ⊓ φ.ker : Subgroup G) := by
  have h1 := nine_le_card_ker hG ψ hψ
  have h2 := three_mul_card_inf_ge hG ψ φ hψ hφ
  omega

end Kernel

section Double

theorem sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ x, DecidablePred (P x)] [∀ k, DecidablePred fun x => P x k] :
    ∑ x, (Finset.univ.filter fun k => P x k).card =
      ∑ k, (Finset.univ.filter fun x => P x k).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem sum_card_filter_sq {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ x, DecidablePred (P x)] [∀ k l, DecidablePred fun x => P x k ∧ P x l] :
    ∑ x, (Finset.univ.filter fun k => P x k).card ^ 2 =
      ∑ k, ∑ l, (Finset.univ.filter fun x => P x k ∧ P x l).card := by
  simp only [Finset.card_filter, sq, Finset.sum_mul_sum, ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_comm

end Double

section Chars

variable [Fintype G] {n : ℕ} (c : Fin n → G →* Kˣ)

theorem card_filter_eq_card_ker (i k : Fin n) :
    (Finset.univ.filter fun x => c k x = c i x).card = Nat.card (c k * (c i)⁻¹).ker := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp [MonoidHom.mem_ker, mul_inv_eq_one]

theorem card_filter_and_eq_card_inf (i k l : Fin n) :
    (Finset.univ.filter fun x => c k x = c i x ∧ c l x = c i x).card =
      Nat.card ((c k * (c i)⁻¹).ker ⊓ (c l * (c i)⁻¹).ker : Subgroup G) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp [MonoidHom.mem_ker, mul_inv_eq_one]

variable {c} (hc : ∀ k x, c k x ^ 3 = 1)
include hc

omit [Fintype G] in
theorem pow_three_ratio (i k : Fin n) (x : G) : (c k * (c i)⁻¹) x ^ 3 = 1 := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, hc, hc, inv_one, mul_one]

theorem nine_le_card_filter (hG : Nat.card G = 27) (i k : Fin n) :
    9 ≤ (Finset.univ.filter fun x => c k x = c i x).card := by
  rw [card_filter_eq_card_ker]
  exact nine_le_card_ker hG _ (pow_three_ratio hc i k)

omit hc in
theorem card_filter_le_nine (hG : Nat.card G = 27) {i k : Fin n} (hik : c k ≠ c i) :
    (Finset.univ.filter fun x => c k x = c i x).card ≤ 9 := by
  rw [card_filter_eq_card_ker]
  refine card_ker_le_nine hG _ fun h1 => hik ?_
  ext x
  have := congrArg (fun φ : G →* Kˣ => φ x) h1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply, mul_inv_eq_one] at this
  rw [this]

theorem three_le_card_filter_and (hG : Nat.card G = 27) (i k l : Fin n) :
    3 ≤ (Finset.univ.filter fun x => c k x = c i x ∧ c l x = c i x).card := by
  rw [card_filter_and_eq_card_inf]
  exact three_le_card_inf hG _ _ (pow_three_ratio hc i k) (pow_three_ratio hc i l)

theorem exists_four_of_eq_chars (hG : Nat.card G = 27) (hn : 6 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (hcij : c i = c j) :
    ∃ x : G, x ≠ 1 ∧ 4 ≤ (Finset.univ.filter fun k => c k x = c i x).card := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_card_filter_comm (fun (x : G) (k : Fin n) => c k x = c i x)
  have hfull : ∀ k ∈ ({i, j} : Finset (Fin n)),
      (Finset.univ.filter fun x => c k x = c i x).card = 27 := by
    intro k hk
    have hk' : c k = c i := by
      rcases Finset.mem_insert.1 hk with rfl | hk'
      · rfl
      · rw [Finset.mem_singleton.1 hk', hcij]
    rw [Finset.filter_true_of_mem fun x _ => by rw [hk'], Finset.card_univ,
      ← Nat.card_eq_fintype_card, hG]
  have hlow : ∑ k : Fin n, (9 + if k ∈ ({i, j} : Finset (Fin n)) then 18 else 0) ≤
      ∑ k, (Finset.univ.filter fun x => c k x = c i x).card := by
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : k ∈ ({i, j} : Finset (Fin n))
    · simp only [hk, ↓reduceIte]
      rw [hfull k hk]
    · simp only [hk, ↓reduceIte, add_zero]
      exact nine_le_card_filter hc hG i k
  have hsplit : ∑ k : Fin n, (9 + if k ∈ ({i, j} : Finset (Fin n)) then 18 else 0) =
      9 * n + 36 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_pair hij, smul_eq_mul]
    ring
  have hup : ∑ x : G, (Finset.univ.filter fun k => c k x = c i x).card ≤ n + 3 * 26 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    have h1 : (Finset.univ.filter fun k => c k 1 = c i 1).card = n := by simp
    rw [h1]
    refine Nat.add_le_add_left ?_ _
    calc ∑ x ∈ Finset.univ.erase (1 : G), (Finset.univ.filter fun k => c k x = c i x).card
        ≤ ∑ x ∈ Finset.univ.erase (1 : G), 3 := by
          refine Finset.sum_le_sum fun x hx => ?_
          exact Nat.lt_succ_iff.1 (hcon x (Finset.mem_erase.1 hx).1)
      _ = 3 * 26 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            ← Nat.card_eq_fintype_card, hG, smul_eq_mul, mul_comm]
  omega

end Chars

section Six

theorem sum_first_six (i : Fin 6) : (∑ k : Fin 6, if k = i then 27 else 9) = 72 := by
  revert i
  decide

theorem sum_second_six (i : Fin 6) : 222 ≤ ∑ k : Fin 6, ∑ l : Fin 6,
    (if k = i ∧ l = i then 27 else if k = i ∨ l = i ∨ k = l then 9 else 3) := by
  revert i
  decide

variable [Fintype G]

theorem exists_four_of_six (hG : Nat.card G = 27) (hK : Nat.card Kˣ = 3) {c : Fin 6 → G →* Kˣ}
    (hc : ∀ k x, c k x ^ 3 = 1) (hinj : Function.Injective c) :
    ∃ x : G, x ≠ 1 ∧ ∃ i, 4 ≤ (Finset.univ.filter fun k => c k x = c i x).card := by
  by_contra hcon
  push Not at hcon
  have : Finite Kˣ := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype Kˣ := Fintype.ofFinite _
  obtain ⟨e⟩ : Nonempty (Kˣ ≃ Fin 3) := by
    refine ⟨Fintype.equivFinOfCardEq ?_⟩
    rw [← Nat.card_eq_fintype_card, hK]
  set N : Fin 6 → G → ℕ := fun i x => (Finset.univ.filter fun k => c k x = c i x).card with hN
  have hN1 : ∀ i, N i 1 = 6 := fun i => by simp [hN]
  have hfirst : ∀ i, ∑ x, N i x = 72 := by
    intro i
    simp only [hN]
    rw [sum_card_filter_comm (fun (x : G) (k : Fin 6) => c k x = c i x)]
    have hk : ∀ k, (Finset.univ.filter fun x => c k x = c i x).card = if k = i then 27 else 9 := by
      intro k
      split_ifs with hki
      · subst hki
        rw [Finset.filter_true_of_mem fun x _ => rfl, Finset.card_univ,
          ← Nat.card_eq_fintype_card, hG]
      · exact le_antisymm (card_filter_le_nine hG fun h' => hki (hinj h'))
          (nine_le_card_filter hc hG i k)
    simp only [hk]
    exact sum_first_six i
  have hsecond : ∀ i, 222 ≤ ∑ x, N i x ^ 2 := by
    intro i
    simp only [hN]
    rw [sum_card_filter_sq (fun (x : G) (k : Fin 6) => c k x = c i x)]
    have hkl : ∀ k l, (if k = i ∧ l = i then 27 else if k = i ∨ l = i ∨ k = l then 9 else 3) ≤
        (Finset.univ.filter fun x => c k x = c i x ∧ c l x = c i x).card := by
      intro k l
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Finset.filter_true_of_mem fun x _ => ⟨rfl, rfl⟩, Finset.card_univ,
          ← Nat.card_eq_fintype_card, hG]
      · rcases h2 with rfl | rfl | rfl
        · simpa using nine_le_card_filter hc hG k l
        · simpa using nine_le_card_filter hc hG l k
        · simpa using nine_le_card_filter hc hG i k
      · exact three_le_card_filter_and hc hG i k l
    exact le_trans (sum_second_six i)
      (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hkl k l)
  have hpoint : ∀ x : G, x ≠ 1 → 54 + 2 * ∑ i, N i x ^ 2 ≤ 9 * ∑ i, N i x := by
    intro x hx
    set s : Fin 3 → ℕ := fun t => (Finset.univ.filter fun k => e (c k x) = t).card with hs
    have hNs : ∀ i, N i x = s (e (c i x)) := by
      intro i
      simp only [hN, hs]
      congr 1
      ext k
      simp [e.injective.eq_iff]
    have hsum6 : ∑ t, s t = 6 := by
      simp only [hs]
      rw [← Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (e (c k x)))]
      simp
    have hs3 : ∀ t, s t ≤ 3 := by
      intro t
      by_cases h0 : s t = 0
      · omega
      · obtain ⟨k, hk⟩ : ∃ k, e (c k x) = t := by
          by_contra hno
          push Not at hno
          apply h0
          simp only [hs]
          exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun k _ => hno k)
        rw [← hk, ← hNs]
        exact Nat.lt_succ_iff.1 (hcon x hx k)
    have hfib : ∀ g : ℕ → ℕ, ∑ i, g (N i x) = ∑ t, s t * g (s t) := by
      intro g
      simp only [hNs]
      rw [← Finset.sum_fiberwise Finset.univ (fun i => e (c i x)) (fun i => g (s (e (c i x))))]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
        smul_eq_mul]
    have h2 := hfib fun m => m ^ 2
    have h1 := hfib fun m => m
    rw [h1, h2]
    rw [Fin.sum_univ_three] at hsum6 ⊢
    rw [Fin.sum_univ_three]
    have ha := hs3 0
    have hb := hs3 1
    have hd := hs3 2
    generalize s 0 = a at *
    generalize s 1 = b at *
    generalize s 2 = d at *
    interval_cases a <;> interval_cases b <;> interval_cases d <;> omega
  have hS1 : ∑ x ∈ Finset.univ.erase (1 : G), ∑ i, N i x = 396 := by
    rw [Finset.sum_comm]
    have : ∀ i, ∑ x ∈ Finset.univ.erase (1 : G), N i x = 66 := by
      intro i
      have := Finset.add_sum_erase Finset.univ (N i) (Finset.mem_univ (1 : G))
      rw [hfirst i, hN1 i] at this
      omega
    simp only [this]
    decide
  have hS2 : 1116 ≤ ∑ x ∈ Finset.univ.erase (1 : G), ∑ i, N i x ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ i, 186 ≤ ∑ x ∈ Finset.univ.erase (1 : G), N i x ^ 2 := by
      intro i
      have := Finset.add_sum_erase Finset.univ (fun x => N i x ^ 2) (Finset.mem_univ (1 : G))
      have h2 := hsecond i
      rw [hN1 i] at this
      omega
    calc 1116 = ∑ _i : Fin 6, 186 := by decide
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  have hcard : (Finset.univ.erase (1 : G)).card = 26 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      hG]
  have htot : ∑ x ∈ Finset.univ.erase (1 : G), (54 + 2 * ∑ i, N i x ^ 2) ≤
      ∑ x ∈ Finset.univ.erase (1 : G), 9 * ∑ i, N i x :=
    Finset.sum_le_sum fun x hx => hpoint x (Finset.mem_erase.1 hx).1
  rw [Finset.sum_add_distrib, Finset.sum_const, hcard, ← Finset.mul_sum, ← Finset.mul_sum, hS1,
    smul_eq_mul] at htot
  omega

end Six

end CFSG.HardMathSupport.Timmesfeld.CrossChar
