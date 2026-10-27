module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Types7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57R3
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm

@[expose] def e7t : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 3, 2, 1, 5, 4, 6], [1, 0, 3, 2, 4, 5, 6], [2, 1, 0, 3, 5, 4, 6],
    [2, 3, 0, 1, 4, 5, 6], [3, 2, 1, 0, 4, 5, 6]]

@[expose] def odd7t : List (List ℕ) :=
  [[0, 1, 2, 3, 5, 4, 6], [0, 3, 2, 1, 4, 5, 6], [2, 1, 0, 3, 4, 5, 6], [1, 0, 3, 2, 5, 4, 6],
    [2, 3, 0, 1, 5, 4, 6], [3, 2, 1, 0, 5, 4, 6]]

set_option maxRecDepth 100000 in
theorem l7t_split : ∀ t ∈ l7t, t ∈ e7t ∨ t ∈ odd7t := by decide +kernel

theorem e7t_len : e7t.length = 6 := by decide

set_option maxRecDepth 100000 in
theorem e7t_ne_range : ∀ a ∈ e7t, a ≠ List.range 7 → a ∈ nt7t := by decide +kernel

theorem sign_of_tab_odd {x : Perm (Fin 7)} (h : tab x ∈ odd7t) : Perm.sign x = -1 := by
  simp only [odd7t, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h
  · have : x = swap 4 5 := tab_inj (by rw [h]; decide)
    rw [this, Equiv.Perm.sign_swap (by decide)]
  · have : x = swap 1 3 := tab_inj (by rw [h]; decide)
    rw [this, Equiv.Perm.sign_swap (by decide)]
  · have : x = swap 0 2 := tab_inj (by rw [h]; decide)
    rw [this, Equiv.Perm.sign_swap (by decide)]
  · have : x = swap 0 1 * swap 2 3 * swap 4 5 := tab_inj (by rw [h]; decide)
    rw [this, map_mul, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  · have : x = swap 0 2 * swap 1 3 * swap 4 5 := tab_inj (by rw [h]; decide)
    rw [this, map_mul, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  · have : x = swap 0 3 * swap 1 2 * swap 4 5 := tab_inj (by rw [h]; decide)
    rw [this, map_mul, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide

theorem tab_mem_e7t {x : Perm (Fin 7)} (h : tab x ∈ l7t) (hx : x ∈ alternatingGroup (Fin 7)) :
    tab x ∈ e7t := by
  rcases l7t_split _ h with h1 | h1
  · exact h1
  · exfalso
    have h2 := sign_of_tab_odd h1
    rw [Equiv.Perm.mem_alternatingGroup] at hx
    rw [hx] at h2
    exact absurd h2 (by decide)

set_option maxRecDepth 100000 in
theorem klein7_cases : ∀ a ∈ e7t, ∀ b ∈ e7t, a ≠ List.range 7 → b ≠ List.range 7 → a ≠ b →
    tmul a b = tmul b a →
    (([1, 0, 3, 2, 4, 5, 6] ∈ [a, b, tmul a b] ∧ [2, 3, 0, 1, 4, 5, 6] ∈ [a, b, tmul a b] ∧
        [3, 2, 1, 0, 4, 5, 6] ∈ [a, b, tmul a b]) ∨
      ([0, 3, 2, 1, 5, 4, 6] ∈ [a, b, tmul a b] ∧ [2, 1, 0, 3, 5, 4, 6] ∈ [a, b, tmul a b] ∧
        [2, 3, 0, 1, 4, 5, 6] ∈ [a, b, tmul a b])) := by
  decide +kernel

@[expose] def Type7A (X : Set (Perm (Fin 7))) (c : ℕ) : Prop :=
  (c = 4 ∧ ∃ a b c' d : Fin 7, [a, b, c', d].Nodup ∧ swap a b * swap c' d ∈ X ∧
    swap a c' * swap b d ∈ X ∧ swap a d * swap b c' ∈ X) ∨
  (c = 4 ∧ ∃ a b c' d e f : Fin 7, [a, b, c', d, e, f].Nodup ∧ swap a b * swap c' d ∈ X ∧
    swap a b * swap e f ∈ X ∧ swap c' d * swap e f ∈ X)

theorem Type7A_conj (σ : Perm (Fin 7)) {T B : Set (Perm (Fin 7))} {c : ℕ}
    (hTB : ∀ x, x ∈ T → σ * x * σ⁻¹ ∈ B) (h : Type7A T c) : Type7A B c := by
  have hnd : ∀ l : List (Fin 7), l.Nodup → (l.map σ).Nodup := fun l hl =>
    hl.map σ.injective
  rcases h with ⟨hc, a, b, c', d, hnd4, h1, h2, h3⟩ |
    ⟨hc, a, b, c', d, e, f, hnd6, h1, h2, h3⟩
  · refine Or.inl ⟨hc, σ a, σ b, σ c', σ d, ?_, ?_, ?_, ?_⟩
    · simpa using hnd [a, b, c', d] hnd4
    · have := hTB _ h1
      rwa [conj_swap_mul_swap] at this
    · have := hTB _ h2
      rwa [conj_swap_mul_swap] at this
    · have := hTB _ h3
      rwa [conj_swap_mul_swap] at this
  · refine Or.inr ⟨hc, σ a, σ b, σ c', σ d, σ e, σ f, ?_, ?_, ?_, ?_⟩
    · simpa using hnd [a, b, c', d, e, f] hnd6
    · have := hTB _ h1
      rwa [conj_swap_mul_swap] at this
    · have := hTB _ h2
      rwa [conj_swap_mul_swap] at this
    · have := hTB _ h3
      rwa [conj_swap_mul_swap] at this

theorem hsel7A : ∀ T : Finset (Perm (Fin 7)), (∀ x ∈ T, tab x ∈ e7t) → 1 ∈ T →
    (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) → (∃ k, T.card = 2 ^ k) → T.card ≠ 1 →
    (T.card = 2 ∧ ∃ e ∈ entries7, (∀ t ∈ e.T, t ∈ T) ∧ e.cs.length ≤ 3) ∨
      Type7A (↑T) T.card := by
  classical
  intro T hL h1 hcl hk hne
  obtain ⟨k, hk⟩ := hk
  have hle : T.card ≤ 6 := (card_le_of_tab T e7t hL).trans (by rw [e7t_len])
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  ·
    left
    have hcard : T.card = 2 := by simpa using hk
    refine ⟨hcard, ?_⟩
    obtain ⟨b, hbT, hb1⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) 1
    obtain ⟨e, he, hTt, hlen⟩ :=
      dC_7 (tab b) (e7t_ne_range _ (hL b hbT) (tab_ne_range hb1))
    refine ⟨e, List.mem_append_left _ he, ?_, hlen⟩
    intro t ht
    rw [entry_single (table7_ok e he) hTt t ht]
    exact hbT
  ·
    right
    have hcard : T.card = 4 := by simpa using hk
    have h3 : 1 < (T.erase 1).card := by rw [Finset.card_erase_of_mem h1]; omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h3
    have hxT : x ∈ T := Finset.mem_of_mem_erase hx
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy
    have hx1 : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hy1 : y ≠ 1 := Finset.ne_of_mem_erase hy
    have hxy' : x * y ∈ T := (hcl x hxT y hyT).1
    have hcases := klein7_cases (tab x) (hL x hxT) (tab y) (hL y hyT) (tab_ne_range hx1)
      (tab_ne_range hy1) (fun h => hxy (tab_inj h))
      (by rw [← tab_mul, ← tab_mul, (hcl x hxT y hyT).2])
    have hl : ∀ t ∈ [tab x, tab y, tmul (tab x) (tab y)], ∃ p ∈ T, tab p = t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨x, hxT, rfl⟩
      · exact ⟨y, hyT, rfl⟩
      · exact ⟨x * y, hxy', tab_mul x y⟩
    have t0123 : tab (swap 0 1 * swap 2 3 : Perm (Fin 7)) = [1, 0, 3, 2, 4, 5, 6] := by decide
    have t0213 : tab (swap 0 2 * swap 1 3 : Perm (Fin 7)) = [2, 3, 0, 1, 4, 5, 6] := by decide
    have t0312 : tab (swap 0 3 * swap 1 2 : Perm (Fin 7)) = [3, 2, 1, 0, 4, 5, 6] := by decide
    have t4513 : tab (swap 4 5 * swap 1 3 : Perm (Fin 7)) = [0, 3, 2, 1, 5, 4, 6] := by decide
    have t4502 : tab (swap 4 5 * swap 0 2 : Perm (Fin 7)) = [2, 1, 0, 3, 5, 4, 6] := by decide
    have t1302 : tab (swap 1 3 * swap 0 2 : Perm (Fin 7)) = [2, 3, 0, 1, 4, 5, 6] := by decide
    rcases hcases with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
    · left
      exact ⟨hcard, 0, 1, 2, 3, by decide, mem_of_tab_mem _ (by rw [t0123]; exact h1') hl,
        mem_of_tab_mem _ (by rw [t0213]; exact h2') hl,
        mem_of_tab_mem _ (by rw [t0312]; exact h3') hl⟩
    · right
      exact ⟨hcard, 4, 5, 1, 3, 0, 2, by decide, mem_of_tab_mem _ (by rw [t4513]; exact h1') hl,
        mem_of_tab_mem _ (by rw [t4502]; exact h2') hl,
        mem_of_tab_mem _ (by rw [t1302]; exact h3') hl⟩

theorem cert_conj_closure {n : ℕ} (hn : 3 ≤ n) (σ : Perm (Fin n)) (e : GenEntry n) (he : e.Ok)
    {B : Subgroup (Perm (Fin n))} (hB : ∀ t ∈ e.T, σ * t * σ⁻¹ ∈ B) :
    alternatingGroup (Fin n) ≤ Subgroup.closure
      {x | ∃ c ∈ e.conjugators.map (fun c => σ * c * σ⁻¹), ∃ b ∈ B, x = c * b * c⁻¹} := by
  set X : Set (Perm (Fin n)) :=
    {x | ∃ c ∈ e.conjugators.map (fun c => σ * c * σ⁻¹), ∃ b ∈ B, x = c * b * c⁻¹} with hX
  have hcl : Subgroup.closure {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹} ≤
      (Subgroup.closure X).comap (MulAut.conj σ).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c', hc', t, ht, rfl⟩
    show σ * (c' * t * c'⁻¹) * σ⁻¹ ∈ Subgroup.closure X
    apply Subgroup.subset_closure
    refine ⟨σ * c' * σ⁻¹, List.mem_map.2 ⟨c', hc', rfl⟩, σ * t * σ⁻¹, hB t ht, ?_⟩
    group
  intro a ha
  have ha' : σ⁻¹ * a * σ ∈ alternatingGroup (Fin n) :=
    (alternatingGroup.normal (α := Fin n)).conj_mem _ ha σ⁻¹ |> fun h => by simpa using h
  have := hcl (e.alt_le_closure hn he ha')
  have h3 : σ * (σ⁻¹ * a * σ) * σ⁻¹ ∈ Subgroup.closure X := this
  simpa [mul_assoc] using h3

theorem exists_family_le {n r₀ : ℕ} {B : Subgroup (Perm (Fin n))}
    (h : ∃ cs : List (Perm (Fin n)), (∀ c ∈ cs, c ∈ alternatingGroup (Fin n)) ∧
      cs.length ≤ r₀ ∧
      alternatingGroup (Fin n) ≤ Subgroup.closure {x | ∃ c ∈ cs, ∃ b ∈ B, x = c * b * c⁻¹}) :
    ∃ (r : ℕ) (f : Fin r → Perm (Fin n)), (∀ i, f i ∈ alternatingGroup (Fin n)) ∧ r ≤ r₀ ∧
      alternatingGroup (Fin n) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} := by
  obtain ⟨cs, hcs, hN, hcl⟩ := h
  refine ⟨cs.length, fun i => cs.get i, fun i => hcs _ (List.get_mem _ _), hN, ?_⟩
  refine hcl.trans (Subgroup.closure_mono ?_)
  rintro _ ⟨c, hc, b, hb, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
  exact ⟨i, b, hb, rfl⟩

theorem exists_T {B : Subgroup (Perm (Fin 7))} (hB1 : B ≠ ⊥)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ B, a * a = 1) :
    ∃ (σ : Perm (Fin 7)) (T : Finset (Perm (Fin 7))), (∀ x, x ∈ T ↔ σ * x * σ⁻¹ ∈ B) ∧
      (∀ x ∈ T, tab x ∈ l7t) ∧ 1 ∈ T ∧ (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) ∧
      (∃ k, T.card = 2 ^ k) ∧ T.card ≠ 1 ∧ Nat.card B = T.card := by
  classical
  have hB2 : IsPGroup 2 B := isPGroup_two_of_sq B h2
  obtain ⟨σ, hσ⟩ := exists_conj_mem P7 card_P7 hB2
  set T : Finset (Perm (Fin 7)) := Finset.univ.filter (fun x => σ * x * σ⁻¹ ∈ B) with hT
  have hmemT : ∀ x, x ∈ T ↔ σ * x * σ⁻¹ ∈ B := fun x => by simp [hT]
  have hsq : ∀ x, x ∈ T → x * x = 1 := by
    intro x hx
    have h := h2 _ ((hmemT x).1 hx)
    have : σ * (x * x) * σ⁻¹ = 1 := by
      calc σ * (x * x) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * x * σ⁻¹) := by group
        _ = 1 := h
    simpa using this
  have hLT : ∀ x ∈ T, tab x ∈ l7t := by
    intro x hx
    have hxP : x ∈ P7 := by simpa [mul_assoc] using hσ _ ((hmemT x).1 hx)
    have hx' : tab x ∈ p7t := hxP
    apply l7t_sub _ hx'
    rw [← tab_mul, hsq x hx, tab_one]
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have h := hc _ ((hmemT x).1 hx) _ ((hmemT y).1 hy)
    have : σ * (x * y) * σ⁻¹ = σ * (y * x) * σ⁻¹ := by
      calc σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
        _ = (σ * y * σ⁻¹) * (σ * x * σ⁻¹) := h
        _ = σ * (y * x) * σ⁻¹ := by group
    simpa using this
  have hmulT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T := by
    intro x hx y hy
    refine (hmemT _).2 ?_
    have e : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
    rw [e]
    exact B.mul_mem ((hmemT x).1 hx) ((hmemT y).1 hy)
  have h1T : (1 : Perm (Fin 7)) ∈ T := by
    refine (hmemT _).2 ?_
    simp
  have hcard : Nat.card B = T.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun b => ⟨σ⁻¹ * (b : Perm (Fin 7)) * σ, ?_⟩
        invFun := fun x => ⟨σ * (x : Perm (Fin 7)) * σ⁻¹, (hmemT x).1 x.2⟩
        left_inv := fun b => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
    rw [hmemT]
    simp [mul_assoc]
  have hne : T.card ≠ 1 := by
    intro h
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    have hbT : σ⁻¹ * (b : Perm (Fin 7)) * σ ∈ T := by
      rw [hmemT]
      simp [mul_assoc]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have e1 : (1 : Perm (Fin 7)) = a := by rw [ha] at h1T; simpa using h1T
    have e2 : σ⁻¹ * (b : Perm (Fin 7)) * σ = a := by rw [ha] at hbT; simpa using hbT
    apply hb1
    apply Subtype.ext
    have : σ⁻¹ * (b : Perm (Fin 7)) * σ = 1 := by rw [e2, ← e1]
    calc (b : Perm (Fin 7)) = σ * (σ⁻¹ * (b : Perm (Fin 7)) * σ) * σ⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hk : ∃ k, T.card = 2 ^ k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hB2.exists_card_eq
    exact ⟨k, by rw [← hcard]; exact hk⟩
  exact ⟨σ, T, hmemT, hLT, h1T, fun x hx y hy => ⟨hmulT x hx y hy, hcomm x hx y hy⟩, hk, hne, hcard⟩

theorem classify7A {B : Subgroup (Perm (Fin 7))} (hB1 : B ≠ ⊥) (hA : B ≤ alternatingGroup (Fin 7))
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ B, a * a = 1) :
    (Nat.card B = 2 ∧ ∃ (r : ℕ) (f : Fin r → Perm (Fin 7)),
      (∀ i, f i ∈ alternatingGroup (Fin 7)) ∧ r ≤ 3 ∧
      alternatingGroup (Fin 7) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹}) ∨
      Type7A (↑B) (Nat.card B) := by
  classical
  obtain ⟨σ, T, hmemT, hLT, h1T, hcl, hk, hne, hcard⟩ := exists_T hB1 hc h2
  have hLT' : ∀ x ∈ T, tab x ∈ e7t := by
    intro x hx
    apply tab_mem_e7t (hLT x hx)
    have h := hA ((hmemT x).1 hx)
    have := (alternatingGroup.normal (α := Fin 7)).conj_mem _ h σ⁻¹
    simpa [mul_assoc] using this
  rcases hsel7A T hLT' h1T hcl hk hne with ⟨hc2, e, he, hTe, hlen⟩ | hres
  · left
    refine ⟨by rw [hcard]; exact hc2, ?_⟩
    refine exists_family_le ⟨e.conjugators.map fun c => σ * c * σ⁻¹, ?_, ?_, ?_⟩
    · intro c hc'
      obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
      exact (alternatingGroup.normal (α := Fin 7)).conj_mem _
        (e.conjugators_mem (entries7_ok e he) c' hc'') σ
    · rw [List.length_map]
      unfold GenEntry.conjugators
      rw [List.length_map]
      exact hlen
    · exact cert_conj_closure (by norm_num) σ e (entries7_ok e he)
        (fun t ht => (hmemT t).1 (hTe t ht))
  · right
    rw [hcard]
    exact Type7A_conj σ (fun x hx => (hmemT x).1 (Finset.mem_coe.1 hx)) hres

end CFSG.QuasithinUnique.B42A57
