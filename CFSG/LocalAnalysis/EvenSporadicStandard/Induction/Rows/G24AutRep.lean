module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev PP : Type := Equiv.Perm (Fin nn)

theorem rep_conjA {c ci t : Array ℕ} {C T : PP} (hc : Rep nn c C) (hci : Rep nn ci C⁻¹)
    (ht : Rep nn t T) : Rep nn (conjA c ci t) (C * T * C⁻¹) := by
  have := rep_compA hc (rep_compA ht hci)
  rwa [← mul_assoc] at this

theorem ordAux_iff {t : Array ℕ} {a : PP} (ht : Rep nn t a) :
    ∀ (d j : ℕ) (p : Array ℕ), Rep nn p (a ^ j) →
      (ordAux t d p = true ↔ (∀ i, j ≤ i → i < j + d → a ^ i ≠ 1) ∧ a ^ (j + d) = 1) := by
  intro d
  induction d with
  | zero =>
    intro j p hp
    rw [ordAux, eqA_iff hp rep_idA]
    constructor
    · intro h
      exact ⟨fun i h1 h2 => by omega, by simpa using h⟩
    · rintro ⟨-, h⟩
      simpa using h
  | succ d ih =>
    intro j p hp
    have hp' : Rep nn (compA nn t p) (a ^ (j + 1)) := by
      rw [pow_succ']
      exact rep_compA ht hp
    rw [ordAux, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, eqA_iff hp rep_idA,
      ih (j + 1) _ hp']
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i hji hij => ?_, by rwa [show j + (d + 1) = j + 1 + d by omega]⟩
      rcases Nat.eq_or_lt_of_le hji with h | h
      · rw [← h]
        exact h1
      · exact h2 i (by omega) (by omega)
    · rintro ⟨h1, h2⟩
      exact ⟨h1 j le_rfl (by omega), fun i hji hij => h1 i (by omega) (by omega),
        by rwa [show j + 1 + d = j + (d + 1) by omega]⟩

theorem ordIs_iff {t : Array ℕ} {a : PP} (ht : Rep nn t a) (v : ℕ) :
    ordIs t v = true ↔ 0 < v ∧ orderOf a = v := by
  unfold ordIs
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    have := (ordAux_iff ht (v - 1) 1 t (by rwa [pow_one])).1 h
    rw [orderOf_eq_iff hv]
    refine ⟨by rw [show v = 1 + (v - 1) by omega]; exact this.2, fun m hm hm0 => ?_⟩
    exact this.1 m (by omega) (by omega)
  · rintro ⟨hv, h⟩
    refine ⟨hv, (ordAux_iff ht (v - 1) 1 t (by rwa [pow_one])).2 ⟨fun i hi1 hi2 => ?_, ?_⟩⟩
    · exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    · rw [show 1 + (v - 1) = v by omega, ← h]
      exact pow_orderOf_eq_one a

theorem rep_prodA {ls : Array (Array ℕ)} {gs : ℕ → PP}
    (h : ∀ l < ls.size, Rep nn ls[l]! (gs l)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < ls.size) → Rep nn (prodA ls w) (w.map gs).prod
  | [], _ => by simpa [prodA] using (rep_idA (n := nn))
  | l :: w, hw => by
    have := rep_compA (h l (hw l (by simp)))
      (rep_prodA h w fun l' hl' => hw l' (by simp [hl']))
    simpa [prodA] using this

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) (j : ℕ)
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos a _ hj]

theorem arr3_get {α : Type*} [Inhabited α] (a b c : α) :
    (#[a, b, c] : Array α)[0]! = a ∧ (#[a, b, c] : Array α)[1]! = b ∧
      (#[a, b, c] : Array α)[2]! = c := ⟨rfl, rfl, rfl⟩

section BuildList

variable (init : Array ℕ) (par : Array ℕ) (op : ℕ → Array ℕ → Array ℕ)

private theorem buildList_aux :
    ∀ m, m ≤ par.size → (((List.range m).foldl
        (fun acc k => acc.push (op k acc[par[k]!]!)) #[init]).size = m + 1) ∧
      ((List.range m).foldl (fun acc k => acc.push (op k acc[par[k]!]!)) #[init])[0]! = init ∧
      ∀ k < m, par[k]! ≤ k →
        ((List.range m).foldl (fun acc k => acc.push (op k acc[par[k]!]!)) #[init])[k + 1]! =
          op k (((List.range m).foldl
            (fun acc k => acc.push (op k acc[par[k]!]!)) #[init])[par[k]!]!) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hsz, h0, hstep⟩ := ih (by omega)
    set A := (List.range m).foldl (fun acc k => acc.push (op k acc[par[k]!]!)) #[init] with hA
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hA]
    refine ⟨by simp [hsz], ?_, ?_⟩
    · rw [getElem!_pos _ 0 (by simp [hsz]), Array.getElem_push_lt (by omega),
        ← getElem!_pos A 0 (by omega), h0]
    · intro k hk hpk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · have hlt : k + 1 < A.size := by omega
        have hp : par[k]! < A.size := by omega
        rw [getElem!_pos _ (k + 1) (by simp [hsz]; omega), Array.getElem_push_lt hlt,
          getElem!_pos _ (par[k]!) (by simp [hsz]; omega), Array.getElem_push_lt hp,
          ← getElem!_pos A (k + 1) hlt, ← getElem!_pos A (par[k]!) hp]
        exact hstep k hk' hpk
      · have hp : par[k]! < A.size := by omega
        have e1 : (A.push (op k A[par[k]!]!))[k + 1]! = op k A[par[k]!]! := by
          rw [getElem!_pos _ (k + 1) (by simp [hsz])]
          simp [Array.getElem_push, hsz]
        have e2 : (A.push (op k A[par[k]!]!))[par[k]!]! = A[par[k]!]! := by
          rw [getElem!_pos _ (par[k]!) (by simp [hsz]; omega), Array.getElem_push_lt hp,
            ← getElem!_pos A _ hp]
        rw [e1, e2]

theorem buildList_size : (buildList init par op).size = par.size + 1 :=
  (buildList_aux init par op par.size le_rfl).1

theorem buildList_zero : (buildList init par op)[0]! = init :=
  (buildList_aux init par op par.size le_rfl).2.1

theorem buildList_succ {k : ℕ} (hk : k < par.size) (hpk : par[k]! ≤ k) :
    (buildList init par op)[k + 1]! = op k ((buildList init par op)[par[k]!]!) :=
  (buildList_aux init par op par.size le_rfl).2.2 k hk hpk

end BuildList

end CFSG.EvenSporadicStandard.G24Aut
