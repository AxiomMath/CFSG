module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.Sporadic.Schreier

variable {M : Type*} [Group M]

section Checks

variable [DecidableEq M]

theorem twoConstrainedCheck_of {KL UL : List M} {k : ℕ} (K U : Subgroup M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (hU : ∀ u, u ∈ UL ↔ u ∈ U) (hUK : U ≤ K)
    (hpow : ∀ u ∈ U, u ^ 2 ^ k = 1) (hnorm : ∀ g ∈ K, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hself : ∀ g ∈ K, (∀ u ∈ U, g * u = u * g) → g ∈ U) :
    twoConstrainedCheck KL UL k = true := by
  simp only [twoConstrainedCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', hK, hU]
  refine ⟨⟨⟨⟨⟨⟨U.one_mem, fun x hx y hy => U.mul_mem hx hy⟩, fun x hx => U.inv_mem hx⟩,
    fun u hu => hUK hu⟩, fun u hu => hpow u hu⟩, fun g hg u hu => hnorm g hg u hu⟩,
    fun g hg => ?_⟩
  by_cases h : ∀ u ∈ U, g * u = u * g
  · exact Or.inr (hself g hg h)
  · left
    simpa [List.all_eq_false, hU] using h

theorem length_eq_card {L : List M} (H : Subgroup M) (hH : ∀ g, g ∈ L ↔ g ∈ H)
    (hnd : L.Nodup) : L.length = Nat.card H := by
  classical
  rw [show Nat.card H = Nat.card (↥(L.toFinset)) from ?_, Nat.card_eq_fintype_card,
    Fintype.card_coe, List.toFinset_card_of_nodup hnd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simpa using (hH g).symm)

theorem indexTwoCheck_of {r : M} {KL NL : List M} (K N : Subgroup M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (hN : ∀ u, u ∈ NL ↔ u ∈ N) (hKn : KL.Nodup) (hNn : NL.Nodup)
    (hNK : N ≤ K) (hcard : Nat.card K = 2 * Nat.card N) (hr : r ∉ N) :
    indexTwoCheck r KL NL = true := by
  simp only [indexTwoCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, hK, hN]
  refine ⟨⟨⟨⟨⟨⟨N.one_mem, fun x hx y hy => N.mul_mem hx hy⟩, fun x hx => N.inv_mem hx⟩,
    fun u hu => hNK hu⟩, ?_⟩, hNn⟩, hr⟩
  rw [length_eq_card K hK hKn, length_eq_card N hN hNn, hcard]

end Checks

theorem closure_subset_of_left_closed [Finite M] (S F : Set M) (h1 : (1 : M) ∈ F)
    (hmul : ∀ s ∈ S, ∀ z ∈ F, s * z ∈ F) : (Subgroup.closure S : Set M) ⊆ F := by
  intro x hx
  have key : ∀ z ∈ F, x * z ∈ F := by
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact hmul s hs
    | one => simpa using fun z hz => hz
    | mul a b _ _ ha hb => exact fun z hz => by rw [mul_assoc]; exact ha _ (hb z hz)
    | inv a _ ha =>
      intro z hz
      let f : F → F := fun y => ⟨a * y, ha y y.2⟩
      have hf : Function.Injective f := fun y y' e =>
        Subtype.ext (mul_left_cancel (congrArg Subtype.val e))
      obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
      have e : a * y = z := congrArg Subtype.val hy
      rw [← e, inv_mul_cancel_left]
      exact y.2
  simpa using key 1 h1

theorem closure_subset_of_right_closed [Finite M] (S F : Set M) (h1 : (1 : M) ∈ F)
    (hmul : ∀ s ∈ S, ∀ z ∈ F, z * s ∈ F) : (Subgroup.closure S : Set M) ⊆ F := by
  intro x hx
  have key : ∀ z ∈ F, z * x ∈ F := by
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact hmul s hs
    | one => simpa using fun z hz => hz
    | mul a b _ _ ha hb => exact fun z hz => by rw [← mul_assoc]; exact hb _ (ha z hz)
    | inv a _ ha =>
      intro z hz
      let f : F → F := fun y => ⟨y * a, ha y y.2⟩
      have hf : Function.Injective f := fun y y' e =>
        Subtype.ext (mul_right_cancel (congrArg Subtype.val e))
      obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
      have e : y * a = z := congrArg Subtype.val hy
      rw [← e, mul_inv_cancel_right]
      exact y.2
  simpa using key 1 h1

theorem card_le_of_subset [Finite M] (H : Subgroup M) (A : Finset M) (hA : ∀ a ∈ A, a ∈ H) :
    A.card ≤ Nat.card H := by
  have hfin : (H : Set M).Finite := Set.toFinite _
  rw [show Nat.card H = Nat.card (H : Set M) from rfl, Nat.card_eq_card_finite_toFinset hfin]
  exact Finset.card_le_card fun a ha => hfin.mem_toFinset.2 (hA a ha)

theorem normalizes_of_gens (S : Set M) (U : Subgroup M)
    (hS : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U ∧ s⁻¹ * u * s ∈ U) :
    ∀ g ∈ Subgroup.closure S, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
  intro g hg
  have key : (∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧ ∀ u ∈ U, g⁻¹ * u * g ∈ U := by
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact ⟨fun u hu => (hS s hs u hu).1, fun u hu => (hS s hs u hu).2⟩
    | one => exact ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩
    | mul a b _ _ ha hb =>
      refine ⟨fun u hu => ?_, fun u hu => ?_⟩
      · have := ha.1 _ (hb.1 u hu)
        simpa [mul_assoc] using this
      · have := hb.2 _ (ha.2 u hu)
        simpa [mul_assoc] using this
    | inv a _ ha => exact ⟨fun u hu => by simpa using ha.2 u hu, fun u hu => by simpa using ha.1 u hu⟩
  exact key.1

theorem evalCodes_mem {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (S : List (Equiv.Perm (Fin n)))
    (hS : ∀ s ∈ S, s ∈ H) : ∀ w : List ℤ, evalCodes S w ∈ H
  | [] => H.one_mem
  | z :: w => by
    have hget : ∀ j, S.getD j 1 ∈ H := fun j => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[j]? with
      | none => exact H.one_mem
      | some s => exact hS s (List.mem_of_getElem? h)
    rw [evalCodes]
    refine H.mul_mem ?_ (evalCodes_mem H S hS w)
    split
    · exact hget _
    · exact H.inv_mem (hget _)

section Closure

variable {n : ℕ}

@[expose] def stepL (gens : List (Equiv.Perm (Fin n))) (L : List (Equiv.Perm (Fin n))) :
    List (Equiv.Perm (Fin n)) :=
  (L ++ L.flatMap fun x => gens.map fun g => tab (x * g)).eraseDups

@[expose] def roundL (gens : List (Equiv.Perm (Fin n))) (i : ℕ) : List (Equiv.Perm (Fin n)) :=
  (List.range i).foldl (fun L _ => stepL gens L) [1]

theorem permClosureList_eq (gens : List (Equiv.Perm (Fin n))) (fuel : ℕ) :
    permClosureList gens fuel = roundL gens fuel := rfl

theorem roundL_succ (gens : List (Equiv.Perm (Fin n))) (i : ℕ) :
    roundL gens (i + 1) = stepL gens (roundL gens i) := by
  rw [roundL, List.range_succ, List.foldl_append]
  rfl

theorem mem_stepL {gens L : List (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)} :
    x ∈ stepL gens L ↔ x ∈ L ∨ ∃ y ∈ L, ∃ g ∈ gens, x = y * g := by
  rw [stepL, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  simp only [List.mem_map, tab_eq]
  constructor
  · rintro (h | ⟨y, hy, g, hg, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, g, hg, rfl⟩
  · rintro (h | ⟨y, hy, g, hg, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, g, hg, rfl⟩

theorem one_mem_roundL (gens : List (Equiv.Perm (Fin n))) :
    ∀ i, (1 : Equiv.Perm (Fin n)) ∈ roundL gens i
  | 0 => by simp [roundL]
  | i + 1 => by
    rw [roundL_succ, mem_stepL]
    exact Or.inl (one_mem_roundL gens i)

theorem roundL_subset (gens : List (Equiv.Perm (Fin n))) :
    ∀ i, ∀ x ∈ roundL gens i, x ∈ Subgroup.closure {g | g ∈ gens}
  | 0, x, hx => by
    have : x = 1 := by simpa [roundL] using hx
    rw [this]
    exact Subgroup.one_mem _
  | i + 1, x, hx => by
    rw [roundL_succ, mem_stepL] at hx
    rcases hx with hx | ⟨y, hy, g, hg, rfl⟩
    · exact roundL_subset gens i x hx
    · exact Subgroup.mul_mem _ (roundL_subset gens i y hy) (Subgroup.subset_closure hg)

theorem mem_permClosureList_iff (gens : List (Equiv.Perm (Fin n))) (fuel : ℕ)
    (hcard : Nat.card (Subgroup.closure {g | g ∈ gens}) ≤ fuel + 1) (x : Equiv.Perm (Fin n)) :
    x ∈ permClosureList gens fuel ↔ x ∈ Subgroup.closure {g | g ∈ gens} := by
  classical
  set H := Subgroup.closure {g | g ∈ gens} with hH
  have grow : ∀ i, i + 1 ≤ (roundL gens i).toFinset.card ∨ ∀ y ∈ H, y ∈ roundL gens i := by
    intro i
    induction i with
    | zero => left; simp [roundL]
    | succ i ih =>
      rcases ih with ih | ih
      · by_cases hcl : ∀ y ∈ roundL gens i, ∀ g ∈ gens, y * g ∈ roundL gens i
        · right
          intro y hy
          have hsub := closure_subset_of_right_closed {g | g ∈ gens} {y | y ∈ roundL gens i}
            (one_mem_roundL gens i) (fun s hs z hz => hcl z hz s hs) hy
          rw [roundL_succ, mem_stepL]
          exact Or.inl hsub
        · left
          push Not at hcl
          obtain ⟨y, hy, g, hg, hyg⟩ := hcl
          have hss : (roundL gens i).toFinset ⊂ (roundL gens (i + 1)).toFinset := by
            rw [Finset.ssubset_iff_of_subset]
            · refine ⟨y * g, ?_, ?_⟩
              · rw [List.mem_toFinset, roundL_succ, mem_stepL]
                exact Or.inr ⟨y, hy, g, hg, rfl⟩
              · rwa [List.mem_toFinset]
            · intro z hz
              rw [List.mem_toFinset] at hz ⊢
              rw [roundL_succ, mem_stepL]
              exact Or.inl hz
          have := Finset.card_lt_card hss
          omega
      · right
        intro y hy
        rw [roundL_succ, mem_stepL]
        exact Or.inl (ih y hy)
  rw [permClosureList_eq]
  refine ⟨fun h => roundL_subset gens fuel x h, fun hx => ?_⟩
  rcases grow fuel with h | h
  · by_contra hnot
    have hA : ∀ a ∈ insert x (roundL gens fuel).toFinset, a ∈ H := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hx
      · exact roundL_subset gens fuel a (List.mem_toFinset.1 ha)
    have h1 := card_le_of_subset H _ hA
    rw [Finset.card_insert_of_notMem (by rwa [List.mem_toFinset])] at h1
    omega
  · exact h x hx

theorem permClosureList_nodup (gens : List (Equiv.Perm (Fin n))) (fuel : ℕ) :
    (permClosureList gens fuel).Nodup := by
  rw [permClosureList_eq]
  cases fuel with
  | zero => simp [roundL]
  | succ i =>
    rw [roundL_succ, stepL]
    generalize (roundL gens i ++ (roundL gens i).flatMap fun x => gens.map fun g => tab (x * g)) = l
    induction h : l.length using Nat.strong_induction_on generalizing l with
    | _ m ih =>
      match l with
      | [] => exact List.nodup_nil
      | a :: as =>
        rw [List.eraseDups_cons]
        refine List.nodup_cons.2 ⟨?_, ih _ ?_ _ rfl⟩
        · rw [List.mem_eraseDups, List.mem_filter]
          simp
        · rw [← h, List.length_cons]
          exact Nat.lt_succ_of_le (List.length_filter_le _ _)

end Closure

end CFSG.ClassicalInvolution.ListBridge

end
