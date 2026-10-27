module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

@[expose] def tab {n : ℕ} (σ : Perm (Fin n)) : List ℕ := List.ofFn (fun i => (σ i : ℕ))

@[expose] def mulT (a b : List ℕ) : List ℕ := b.map (fun j => a.getD j 0)

@[expose] def oneT (n : ℕ) : List ℕ := List.range n

@[expose] def invT (n : ℕ) (a : List ℕ) : List ℕ := (List.range n).map (fun j => a.idxOf j)

@[expose] def cjT (s a : List ℕ) : List ℕ := mulT (mulT s a) (invT 6 s)

@[expose] def suppT (n : ℕ) (a : List ℕ) : ℕ :=
  (List.range n).countP (fun i => !decide (a.getD i 0 = i))

theorem tab_getD {n : ℕ} (σ : Perm (Fin n)) (j : Fin n) : (tab σ).getD j 0 = σ j := by
  simp [tab]

theorem tab_mul {n : ℕ} (σ τ : Perm (Fin n)) : tab (σ * τ) = mulT (tab σ) (tab τ) := by
  simp [tab, mulT, List.map_ofFn, Function.comp_def]

theorem tab_one {n : ℕ} : tab (1 : Perm (Fin n)) = oneT n := by
  simp [tab, oneT, List.ofFn_eq_map]

theorem tab_injective {n : ℕ} : Function.Injective (tab : Perm (Fin n) → List ℕ) := by
  intro σ τ h
  refine Equiv.ext fun j => Fin.ext ?_
  have := congrArg (fun l => l.getD j 0) h
  simpa only [tab_getD] using this

theorem tab_inv {n : ℕ} (σ : Perm (Fin n)) : tab σ⁻¹ = invT n (tab σ) := by
  have hnd : (tab σ).Nodup := by
    simp only [tab]
    rw [List.nodup_ofFn]
    intro i j h
    exact σ.injective (Fin.ext h)
  refine List.ext_getElem (by simp [tab, invT]) fun k h1 h2 => ?_
  have hk : k < n := by simpa [tab] using h1
  have hlt : ((σ⁻¹ ⟨k, hk⟩ : Fin n) : ℕ) < (tab σ).length := by simp [tab]
  have hget : (tab σ)[((σ⁻¹ ⟨k, hk⟩ : Fin n) : ℕ)]'hlt = k := by simp [tab]
  have := hnd.idxOf_getElem ((σ⁻¹ ⟨k, hk⟩ : Fin n) : ℕ) hlt
  rw [hget] at this
  have h3 : (invT n (tab σ))[k]'h2 = (tab σ).idxOf k := by simp [invT]
  rw [h3, this]
  simp [tab]

theorem tab_conj (σ a : Perm (Fin 6)) : tab (σ * a * σ⁻¹) = cjT (tab σ) (tab a) := by
  rw [cjT, ← tab_inv, ← tab_mul, ← tab_mul]

theorem sum_ite_eq_countP (p : ℕ → Prop) [DecidablePred p] (l : List ℕ) :
    (l.map (fun i => if p i then 0 else 1)).sum = l.countP (fun i => !decide (p i)) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [h, ih, List.countP_cons] <;> omega

theorem suppT_tab {n : ℕ} (σ : Perm (Fin n)) : suppT n (tab σ) = σ.support.card := by
  have h1 : σ.support.card = ∑ i ∈ Finset.range n, if (tab σ).getD i 0 = i then 0 else 1 := by
    rw [Equiv.Perm.support, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tab_getD]
    simp [Fin.ext_iff]
  have h2 : (∑ i ∈ Finset.range n, if (tab σ).getD i 0 = i then 0 else 1) =
      ((List.range n).map (fun i => if (tab σ).getD i 0 = i then 0 else 1)).sum := by
    simp [Finset.sum, Finset.range_val, Multiset.range]
  rw [h1, h2, sum_ite_eq_countP]
  simp [suppT]

theorem mem_map_tab_iff {n : ℕ} {l : List (Perm (Fin n))} {s : Perm (Fin n)} :
    tab s ∈ l.map tab ↔ s ∈ l :=
  List.mem_map_of_injective tab_injective

@[expose] def allP (n : ℕ) : List (Perm (Fin n)) := permsOfList (List.finRange n)

theorem mem_allP {n : ℕ} (σ : Perm (Fin n)) : σ ∈ allP n :=
  mem_permsOfList_of_mem (fun x _ => List.mem_finRange x)

@[expose] def allT (n : ℕ) : List (List ℕ) := (allP n).map tab

theorem mem_allT {n : ℕ} (σ : Perm (Fin n)) : tab σ ∈ allT n := List.mem_map_of_mem (mem_allP σ)

theorem exists_of_mem_allT {n : ℕ} {a : List ℕ} (h : a ∈ allT n) : ∃ σ : Perm (Fin n), tab σ = a :=
  let ⟨σ, _, hσ⟩ := List.mem_map.1 h
  ⟨σ, hσ⟩

@[expose] def c2T : List (List ℕ) :=
  (allT 6).filter (fun a => decide (mulT a a = oneT 6) && decide (suppT 6 a = 4))

theorem mem_c2T {s : Perm (Fin 6)} (hs : s * s = 1) (h4 : s.support.card = 4) : tab s ∈ c2T := by
  simp only [c2T, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨mem_allT s, by rw [← tab_mul, hs, tab_one], by rw [suppT_tab, h4]⟩

theorem orderOf_eq_four_iff {G : Type*} [Group G] (g : G) :
    orderOf g = 4 ↔ (g * g) * (g * g) = 1 ∧ g * g ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, fun h2 => ?_⟩
    · have := pow_orderOf_eq_one g
      rw [h] at this
      simpa [pow_succ, mul_assoc] using this
    · have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using h2)
      rw [h] at this
      omega
  · rintro ⟨h4, h2⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g)
      (by simpa [sq] using h2) (by simpa [pow_succ, mul_assoc] using h4)
    simpa using this

@[expose] def Compat (s t : Perm (Fin 6)) : Prop := orderOf (s * t) ≠ 4

@[expose] def CompatT (a b : List ℕ) : Prop :=
  ¬ (mulT (mulT (mulT a b) (mulT a b)) (mulT (mulT a b) (mulT a b)) = oneT 6 ∧
      mulT (mulT a b) (mulT a b) ≠ oneT 6)

instance (a b : List ℕ) : Decidable (CompatT a b) := inferInstanceAs (Decidable (¬ _))

theorem compat_iff (s t : Perm (Fin 6)) : Compat s t ↔ CompatT (tab s) (tab t) := by
  unfold Compat CompatT
  rw [Ne, orderOf_eq_four_iff]
  simp only [← tab_mul, ← tab_one, ne_eq, tab_injective.eq_iff]

@[expose] def Good (l : List (Perm (Fin 6))) : Prop :=
  (∀ s ∈ l, ∀ t ∈ l, Compat s t) ∧ (∀ s ∈ l, ∀ t ∈ l, s * t * s⁻¹ ∈ l)

@[expose] def GoodT (l : List (List ℕ)) : Prop :=
  (∀ a ∈ l, ∀ b ∈ l, CompatT a b) ∧ (∀ a ∈ l, ∀ b ∈ l, ∃ u ∈ l, mulT a b = mulT u a)

instance (l : List (List ℕ)) : Decidable (GoodT l) := inferInstanceAs (Decidable (_ ∧ _))

theorem conj_mem_iff (l : List (Perm (Fin 6))) (s t : Perm (Fin 6)) :
    s * t * s⁻¹ ∈ l ↔ ∃ u ∈ l.map tab, mulT (tab s) (tab t) = mulT u (tab s) := by
  constructor
  · intro h
    refine ⟨tab (s * t * s⁻¹), mem_map_tab_iff.2 h, ?_⟩
    rw [← tab_mul, ← tab_mul, inv_mul_cancel_right]
  · rintro ⟨u, hu, h⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    rw [← tab_mul, ← tab_mul] at h
    have := tab_injective h
    rw [this, mul_inv_cancel_right]
    exact hw

theorem good_iff (l : List (Perm (Fin 6))) : Good l ↔ GoodT (l.map tab) := by
  unfold Good GoodT
  simp only [List.forall_mem_map, compat_iff, conj_mem_iff]

@[expose] def dt (a b c d : Fin 6) : Perm (Fin 6) := swap a b * swap c d

@[expose] def orbit (V : List (Perm (Fin 6))) (r : Perm (Fin 6)) : List (Perm (Fin 6)) :=
  r :: V.map (fun v => v * r * v⁻¹)

@[expose] def mk (V reps : List (Perm (Fin 6))) : List (Perm (Fin 6)) :=
  V ++ reps.flatMap (orbit V)

theorem mem_mk {V reps : List (Perm (Fin 6))} {s : Perm (Fin 6)} :
    s ∈ mk V reps ↔ s ∈ V ∨ ∃ r ∈ reps, s ∈ orbit V r := by
  simp [mk]

end CFSG.GF2Type.Aschbacher1976Full.HS.Six
