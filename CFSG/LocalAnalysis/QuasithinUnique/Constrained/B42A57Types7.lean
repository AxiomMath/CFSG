module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm

@[expose] def Res7 (X : Set (Perm (Fin 7))) (c : ℕ) : Prop :=
  (c = 2 ∧ ∃ a b : Fin 7, a ≠ b ∧ swap a b ∈ X) ∨
  (c = 4 ∧ ∃ a b c' d : Fin 7, [a, b, c', d].Nodup ∧ swap a b ∈ X ∧ swap c' d ∈ X) ∨
  (c = 8 ∧ ∃ a b c' d e f : Fin 7, [a, b, c', d, e, f].Nodup ∧ swap a b ∈ X ∧ swap c' d ∈ X ∧
    swap e f ∈ X) ∨
  (c = 8 ∧ ∃ a b c' d e f : Fin 7, [a, b, c', d, e, f].Nodup ∧ swap e f ∈ X ∧
    swap a b * swap c' d ∈ X ∧ swap a c' * swap b d ∈ X)

theorem Res7_conj (σ : Perm (Fin 7)) {T B : Set (Perm (Fin 7))} {c : ℕ}
    (hTB : ∀ x, x ∈ T → σ * x * σ⁻¹ ∈ B) (h : Res7 T c) : Res7 B c := by
  have hsw : ∀ a b : Fin 7, σ * swap a b * σ⁻¹ = swap (σ a) (σ b) := fun a b => by
    rw [Equiv.swap_apply_apply]
  have hnd : ∀ l : List (Fin 7), l.Nodup → (l.map σ).Nodup := fun l hl =>
    hl.map σ.injective
  rcases h with ⟨hc, a, b, hab, hT⟩ | ⟨hc, a, b, c', d, hnd4, h1, h2⟩ |
    ⟨hc, a, b, c', d, e, f, hnd6, h1, h2, h3⟩ | ⟨hc, a, b, c', d, e, f, hnd6, h1, h2, h3⟩
  · refine Or.inl ⟨hc, σ a, σ b, fun h => hab (σ.injective h), ?_⟩
    rw [← hsw]
    exact hTB _ hT
  · refine Or.inr (Or.inl ⟨hc, σ a, σ b, σ c', σ d, ?_, ?_, ?_⟩)
    · simpa using hnd [a, b, c', d] hnd4
    · rw [← hsw]; exact hTB _ h1
    · rw [← hsw]; exact hTB _ h2
  · refine Or.inr (Or.inr (Or.inl ⟨hc, σ a, σ b, σ c', σ d, σ e, σ f, ?_, ?_, ?_, ?_⟩))
    · simpa using hnd [a, b, c', d, e, f] hnd6
    · rw [← hsw]; exact hTB _ h1
    · rw [← hsw]; exact hTB _ h2
    · rw [← hsw]; exact hTB _ h3
  · refine Or.inr (Or.inr (Or.inr ⟨hc, σ a, σ b, σ c', σ d, σ e, σ f, ?_, ?_, ?_, ?_⟩))
    · simpa using hnd [a, b, c', d, e, f] hnd6
    · rw [← hsw]; exact hTB _ h1
    · have := hTB _ h2
      rwa [show σ * (swap a b * swap c' d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c') (σ d) by
        rw [← hsw, ← hsw]; group] at this
    · have := hTB _ h3
      rwa [show σ * (swap a c' * swap b d) * σ⁻¹ = swap (σ a) (σ c') * swap (σ b) (σ d) by
        rw [← hsw, ← hsw]; group] at this

theorem trans7_swap : ∀ t ∈ trans7t, ∃ a b : Fin 7, a ≠ b ∧ tab (swap a b) = t := by
  decide +kernel

theorem trans7_disjoint : ∀ t ∈ trans7t, ∀ s ∈ trans7t, t ≠ s →
    ∃ a b c d : Fin 7, [a, b, c, d].Nodup ∧ tab (swap a b) = t ∧ tab (swap c d) = s := by
  decide +kernel

theorem rank3_cases : ∀ a ∈ l7t, ∀ b ∈ l7t, ∀ c ∈ l7t,
    a ≠ List.range 7 → b ≠ List.range 7 → b ≠ a → c ≠ List.range 7 → c ≠ a → c ≠ b →
    c ≠ tmul a b → tmul a b = tmul b a → tmul a c = tmul c a → tmul b c = tmul c b →
    (([0, 1, 2, 3, 5, 4, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c] ∧
      [0, 3, 2, 1, 4, 5, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c] ∧
      [2, 1, 0, 3, 4, 5, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c]) ∨
    ([0, 1, 2, 3, 5, 4, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c] ∧
      [1, 0, 3, 2, 4, 5, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c] ∧
      [2, 3, 0, 1, 4, 5, 6] ∈ [a, b, c, tmul a b, tmul a c, tmul b c, tmul (tmul a b) c])) := by
  decide +kernel

theorem mem_of_tab_mem {T : Finset (Perm (Fin 7))} {l : List (List ℕ)} (p0 : Perm (Fin 7))
    (hmem : tab p0 ∈ l) (hl : ∀ t ∈ l, ∃ p ∈ T, tab p = t) : p0 ∈ T := by
  obtain ⟨p, hp, hpt⟩ := hl _ hmem
  rw [← tab_inj hpt]
  exact hp

theorem hsel7R : ∀ T : Finset (Perm (Fin 7)), (∀ x ∈ T, tab x ∈ l7t) → 1 ∈ T →
    (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) → (∃ k, T.card = 2 ^ k) → T.card ≠ 1 →
    (∃ e ∈ entries7, (∀ t ∈ e.T, t ∈ T) ∧ T.card ^ e.cs.length ≤ 2 ^ 4) ∨
      Res7 (↑T) T.card := by
  classical
  intro T hL h1 hcl hk hne
  have hsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    apply tab_inj
    rw [tab_mul, tab_one]
    exact l7t_sq _ (hL x hx)
  obtain ⟨k, hk⟩ := hk
  have hle : T.card ≤ 12 := (card_le_of_tab T l7t hL).trans (by rw [l7t_len])
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  ·
    have hcard : T.card = 2 := by simpa using hk
    obtain ⟨b, hbT, hb1⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) 1
    rcases dA_7 (tab b) (hL b hbT) (tab_ne_range hb1) with htr | hnt
    · right
      left
      refine ⟨hcard, ?_⟩
      obtain ⟨a, a', hne', htab⟩ := trans7_swap _ htr
      have : swap a a' = b := tab_inj htab
      exact ⟨a, a', hne', by rw [this]; exact hbT⟩
    · left
      obtain ⟨e, he, hTt, hlen⟩ := dC_7 (tab b) hnt
      refine ⟨e, List.mem_append_left _ he, ?_, ?_⟩
      · intro t ht
        rw [entry_single (table7_ok e he) hTt t ht]
        exact hbT
      · rw [hcard]
        calc 2 ^ e.cs.length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hlen
          _ ≤ 2 ^ 4 := by norm_num
  ·
    have hcard : T.card = 4 := by simpa using hk
    by_cases hRR : ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ tab u ∈ trans7t ∧ tab v ∈ trans7t
    · right
      right
      left
      obtain ⟨u, huT, v, hvT, huv, hu, hv⟩ := hRR
      obtain ⟨a, b, c', d, hnd, hta, htb⟩ := trans7_disjoint _ hu _ hv (fun h => huv (tab_inj h))
      have e1 : swap a b = u := tab_inj hta
      have e2 : swap c' d = v := tab_inj htb
      exact ⟨hcard, a, b, c', d, hnd, by rw [e1]; exact huT, by rw [e2]; exact hvT⟩
    · left
      push Not at hRR
      have h3 : 1 < (T.erase 1).card := by rw [Finset.card_erase_of_mem h1]; omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h3
      have hxT : x ∈ T := Finset.mem_of_mem_erase hx
      have hyT : y ∈ T := Finset.mem_of_mem_erase hy
      have hx1 : x ≠ 1 := Finset.ne_of_mem_erase hx
      have hy1 : y ≠ 1 := Finset.ne_of_mem_erase hy
      have hxy' : x * y ∈ T := (hcl x hxT y hyT).1
      have hne1 : x * y ≠ 1 := mul_ne_one_of_ne (hsq x hxT) hxy
      have hxne : x ≠ x * y := fun h => hy1 (by simpa using h)
      have hyne : y ≠ x * y := fun h => hx1 (by simpa using h)
      have hpair : ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ tab a ∈ nt7t ∧ tab b ∈ nt7t := by
        rcases dA_7 (tab x) (hL x hxT) (tab_ne_range hx1) with hxt | hxn
        · rcases dA_7 (tab y) (hL y hyT) (tab_ne_range hy1) with hyt | hyn
          · exact absurd hyt (hRR x hxT y hyT hxy hxt)
          · have hxyn : tab (x * y) ∈ nt7t := by
              rcases dA_7 (tab (x * y)) (hL _ hxy') (tab_ne_range hne1) with ht | hn
              · exact absurd ht (hRR x hxT (x * y) hxy' hxne hxt)
              · exact hn
            exact ⟨y, hyT, x * y, hxy', hyne, hyn, hxyn⟩
        · rcases dA_7 (tab y) (hL y hyT) (tab_ne_range hy1) with hyt | hyn
          · have hxyn : tab (x * y) ∈ nt7t := by
              rcases dA_7 (tab (x * y)) (hL _ hxy') (tab_ne_range hne1) with ht | hn
              · exact absurd ht (hRR y hyT (x * y) hxy' hyne hyt)
              · exact hn
            exact ⟨x, hxT, x * y, hxy', hxne, hxn, hxyn⟩
          · exact ⟨x, hxT, y, hyT, hxy, hxn, hyn⟩
      obtain ⟨a, haT, b, hbT, hab, ha, hb⟩ := hpair
      obtain ⟨e, he, hTt, hlen⟩ := dD_7 (tab a) ha (tab b) hb (fun h => hab (tab_inj h))
        (by rw [← tab_mul, ← tab_mul, (hcl a haT b hbT).2])
      refine ⟨e, List.mem_append_right _ he, ?_, ?_⟩
      · intro t ht
        rcases entry_pair (pairs7_ok e he) hTt t ht with rfl | rfl | rfl
        · exact haT
        · exact hbT
        · exact (hcl a haT b hbT).1
      · rw [hcard]
        calc 4 ^ e.cs.length ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hlen
          _ = 2 ^ 4 := by norm_num
  ·
    have hcard : T.card = 8 := by simpa using hk
    right
    obtain ⟨a, haT, ha1⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) 1
    have hT7 : (T.erase 1).card = 7 := by rw [Finset.card_erase_of_mem h1]; omega
    have hb0 : 0 < ((T.erase 1).erase a).card := by
      have := Finset.pred_card_le_card_erase (s := T.erase 1) (a := a)
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hb0
    simp only [Finset.mem_erase] at hb
    obtain ⟨hbne, hb1, hbT⟩ := hb
    have habT : a * b ∈ T := (hcl a haT b hbT).1
    have hc0 : 0 < ((((T.erase 1).erase a).erase b).erase (a * b)).card := by
      have h1' := Finset.pred_card_le_card_erase (s := T.erase 1) (a := a)
      have h2' := Finset.pred_card_le_card_erase (s := (T.erase 1).erase a) (a := b)
      have h3' := Finset.pred_card_le_card_erase (s := ((T.erase 1).erase a).erase b) (a := a * b)
      omega
    obtain ⟨c, hc⟩ := Finset.card_pos.1 hc0
    simp only [Finset.mem_erase] at hc
    obtain ⟨hcab, hcb, hca, hc1, hcT⟩ := hc
    have hab_comm : tmul (tab a) (tab b) = tmul (tab b) (tab a) := by
      rw [← tab_mul, ← tab_mul, (hcl a haT b hbT).2]
    have hac_comm : tmul (tab a) (tab c) = tmul (tab c) (tab a) := by
      rw [← tab_mul, ← tab_mul, (hcl a haT c hcT).2]
    have hbc_comm : tmul (tab b) (tab c) = tmul (tab c) (tab b) := by
      rw [← tab_mul, ← tab_mul, (hcl b hbT c hcT).2]
    have hl8 : ∀ t ∈ [tab a, tab b, tab c, tmul (tab a) (tab b), tmul (tab a) (tab c),
        tmul (tab b) (tab c), tmul (tmul (tab a) (tab b)) (tab c)], ∃ p ∈ T, tab p = t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨a, haT, rfl⟩
      · exact ⟨b, hbT, rfl⟩
      · exact ⟨c, hcT, rfl⟩
      · exact ⟨a * b, habT, tab_mul a b⟩
      · exact ⟨a * c, (hcl a haT c hcT).1, tab_mul a c⟩
      · exact ⟨b * c, (hcl b hbT c hcT).1, tab_mul b c⟩
      · exact ⟨a * b * c, (hcl _ habT c hcT).1, by rw [tab_mul, tab_mul]⟩
    have t45 : tab (swap 4 5 : Perm (Fin 7)) = [0, 1, 2, 3, 5, 4, 6] := by decide
    have t13 : tab (swap 1 3 : Perm (Fin 7)) = [0, 3, 2, 1, 4, 5, 6] := by decide
    have t02 : tab (swap 0 2 : Perm (Fin 7)) = [2, 1, 0, 3, 4, 5, 6] := by decide
    have t0123 : tab (swap 0 1 * swap 2 3 : Perm (Fin 7)) = [1, 0, 3, 2, 4, 5, 6] := by decide
    have t0213 : tab (swap 0 2 * swap 1 3 : Perm (Fin 7)) = [2, 3, 0, 1, 4, 5, 6] := by decide
    rcases rank3_cases (tab a) (hL a haT) (tab b) (hL b hbT) (tab c) (hL c hcT)
      (tab_ne_range ha1) (tab_ne_range hb1) (fun h => hbne (tab_inj h)) (tab_ne_range hc1)
      (fun h => hca (tab_inj h)) (fun h => hcb (tab_inj h))
      (fun h => hcab (tab_inj (by rw [tab_mul]; exact h))) hab_comm hac_comm hbc_comm with
      ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
    · right
      right
      left
      refine ⟨hcard, 4, 5, 1, 3, 0, 2, by decide, ?_, ?_, ?_⟩
      · exact mem_of_tab_mem (swap 4 5) (by rw [t45]; exact h1') hl8
      · exact mem_of_tab_mem (swap 1 3) (by rw [t13]; exact h2') hl8
      · exact mem_of_tab_mem (swap 0 2) (by rw [t02]; exact h3') hl8
    · right
      right
      right
      refine ⟨hcard, 0, 1, 2, 3, 4, 5, by decide, ?_, ?_, ?_⟩
      · exact mem_of_tab_mem (swap 4 5) (by rw [t45]; exact h1') hl8
      · exact mem_of_tab_mem (swap 0 1 * swap 2 3) (by rw [t0123]; exact h2') hl8
      · exact mem_of_tab_mem (swap 0 2 * swap 1 3) (by rw [t0213]; exact h3') hl8

theorem classify7 {B : Subgroup (Perm (Fin 7))} (hB1 : B ≠ ⊥)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ B, a * a = 1) :
    (∃ (r : ℕ) (f : Fin r → Perm (Fin 7)), (∀ i, f i ∈ alternatingGroup (Fin 7)) ∧
      Nat.card B ^ r ≤ 2 ^ 4 ∧
      alternatingGroup (Fin 7) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹}) ∨
      Res7 (↑B) (Nat.card B) := by
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
  rcases hsel7R T hLT h1T (fun x hx y hy => ⟨hmulT x hx y hy, hcomm x hx y hy⟩) hk hne with
    ⟨e, he, hTe, hbound⟩ | hres
  · left
    have heok := entries7_ok e he
    refine exists_family ⟨e.conjugators.map fun c => σ * c * σ⁻¹, ?_, ?_, ?_⟩
    · intro c hc'
      obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
      exact (alternatingGroup.normal (α := Fin 7)).conj_mem _ (e.conjugators_mem heok c' hc'') σ
    · rw [List.length_map, hcard]
      unfold GenEntry.conjugators
      rw [List.length_map]
      exact hbound
    · set X : Set (Perm (Fin 7)) :=
        {x | ∃ c ∈ e.conjugators.map (fun c => σ * c * σ⁻¹), ∃ b ∈ B, x = c * b * c⁻¹} with hX
      have hcl : Subgroup.closure
          {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹} ≤
          (Subgroup.closure X).comap (MulAut.conj σ).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro _ ⟨c', hc', t, ht, rfl⟩
        show σ * (c' * t * c'⁻¹) * σ⁻¹ ∈ Subgroup.closure X
        apply Subgroup.subset_closure
        refine ⟨σ * c' * σ⁻¹, List.mem_map.2 ⟨c', hc', rfl⟩, σ * t * σ⁻¹,
          (hmemT t).1 (hTe t ht), ?_⟩
        group
      intro a ha
      have ha' : σ⁻¹ * a * σ ∈ alternatingGroup (Fin 7) :=
        (alternatingGroup.normal (α := Fin 7)).conj_mem _ ha σ⁻¹ |> fun h => by simpa using h
      have := hcl (e.alt_le_closure (by norm_num) heok ha')
      have h3 : σ * (σ⁻¹ * a * σ) * σ⁻¹ ∈ Subgroup.closure X := this
      simpa [mul_assoc] using h3
  · right
    rw [hcard]
    exact Res7_conj σ (fun x hx => (hmemT x).1 (Finset.mem_coe.1 hx)) hres

end CFSG.QuasithinUnique.B42A57
