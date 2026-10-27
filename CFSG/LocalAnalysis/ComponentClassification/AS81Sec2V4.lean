module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.ComponentClassification.AS81.Sec2V4

open Equiv

@[expose] def act (σ : Perm (Fin 5)) (v : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun k => v (σ⁻¹ k)

@[expose] def IsEven (v : Fin 5 → ZMod 2) : Prop := ∑ k, v k = 0

instance (v : Fin 5 → ZMod 2) : Decidable (IsEven v) :=
  inferInstanceAs (Decidable (∑ k, v k = 0))

theorem act_apply (σ : Perm (Fin 5)) (v : Fin 5 → ZMod 2) (k : Fin 5) :
    act σ v k = v (σ⁻¹ k) := rfl

theorem act_add (σ : Perm (Fin 5)) (v w : Fin 5 → ZMod 2) :
    act σ (v + w) = act σ v + act σ w := rfl

theorem act_zero (σ : Perm (Fin 5)) : act σ 0 = 0 := rfl

theorem act_one' (σ : Perm (Fin 5)) : act σ 1 = 1 := rfl

theorem act_one (v : Fin 5 → ZMod 2) : act 1 v = v := rfl

theorem act_mul (σ τ : Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    act (σ * τ) v = act σ (act τ v) := by
  funext k
  simp [act, mul_inv_rev, Perm.mul_apply]

theorem act_inv_act (σ : Perm (Fin 5)) (v : Fin 5 → ZMod 2) : act σ⁻¹ (act σ v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (σ : Perm (Fin 5)) (v : Fin 5 → ZMod 2) : act σ (act σ⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem isEven_act {v : Fin 5 → ZMod 2} (hv : IsEven v) (σ : Perm (Fin 5)) :
    IsEven (act σ v) := by
  unfold IsEven act at *
  rw [Equiv.sum_comp σ⁻¹ v]
  exact hv

theorem isEven_add {v w : Fin 5 → ZMod 2} (hv : IsEven v) (hw : IsEven w) : IsEven (v + w) := by
  unfold IsEven at *
  simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]

theorem isEven_zero : IsEven 0 := by decide

theorem act_single (σ : Perm (Fin 5)) (i : Fin 5) (c : ZMod 2) :
    act σ (Pi.single i c) = Pi.single (σ i) c := by
  funext k
  simp only [act, Pi.single_apply, Perm.inv_eq_iff_eq]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem exists_apply_eq {i j a b : Fin 5} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ ∈ alternatingGroup (Fin 5), σ i = a ∧ σ j = b := by
  have : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5)
      (Nat.card (Fin 5) - 2) := alternatingGroup.isMultiplyPretransitive (Fin 5)
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 5) - 2) (by simp) (by simp)
  let x : Fin 2 ↪ Fin 5 := ⟨![i, j], by
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin 5 := ⟨![a, b], by
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) x y
  refine ⟨σ, σ.2, ?_, ?_⟩
  · exact congrArg (fun e : Fin 2 ↪ Fin 5 => e 0) hσ
  · exact congrArg (fun e : Fin 2 ↪ Fin 5 => e 1) hσ

theorem exists_apply_eq' (i a : Fin 5) : ∃ σ ∈ alternatingGroup (Fin 5), σ i = a := by
  obtain ⟨σ, hσ, h, -⟩ := exists_apply_eq (i := i) (j := i + 1) (a := a) (b := a + 1)
    (by revert i; decide) (by revert a; decide)
  exact ⟨σ, hσ, h⟩

@[expose] def pair (i j : Fin 5) : Fin 5 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem act_pair (σ : Perm (Fin 5)) (i j : Fin 5) : act σ (pair i j) = pair (σ i) (σ j) := by
  rw [pair, act_add, act_single, act_single, pair]

theorem isEven_pair (i j : Fin 5) : IsEven (pair i j) := by
  revert i j
  decide

theorem even_cases : ∀ v : Fin 5 → ZMod 2, IsEven v → v ≠ 0 →
    (∃ i j, i ≠ j ∧ v = pair i j) ∨ ∃ m, v = 1 + Pi.single m 1 := by
  decide

theorem even_eq_sum : ∀ v : Fin 5 → ZMod 2, IsEven v →
    v = v 1 • pair 0 1 + v 2 • pair 0 2 + v 3 • pair 0 3 + v 4 • pair 0 4 := by
  decide

theorem smul_mem {N : AddSubgroup (Fin 5 → ZMod 2)} (c : ZMod 2) {v : Fin 5 → ZMod 2}
    (hv : v ∈ N) : c • v ∈ N := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul]
    exact N.zero_mem
  · rw [one_smul]
    exact hv

theorem ne_add_one : ∀ m : Fin 5, m ≠ m + 1 := by decide

theorem compl_add_compl : ∀ m : Fin 5,
    (1 + Pi.single m (1 : ZMod 2)) + (1 + Pi.single (m + 1) 1) = pair m (m + 1) := by
  decide

theorem mem_of_invariant {N : AddSubgroup (Fin 5 → ZMod 2)}
    (hN : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ N, act σ v ∈ N) {v : Fin 5 → ZMod 2}
    (hv : v ∈ N) (hve : IsEven v) (hv0 : v ≠ 0) {w : Fin 5 → ZMod 2} (hw : IsEven w) :
    w ∈ N := by
  obtain ⟨i, j, hij, hp⟩ : ∃ i j, i ≠ j ∧ pair i j ∈ N := by
    rcases even_cases v hve hv0 with ⟨i, j, hij, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨i, j, hij, hv⟩
    · obtain ⟨σ, hσ, hσm⟩ := exists_apply_eq' m (m + 1)
      refine ⟨m, m + 1, ne_add_one m, ?_⟩
      have h := N.add_mem hv (hN σ hσ _ hv)
      rw [act_add, act_one', act_single, hσm] at h
      rwa [compl_add_compl m] at h
  have hall : ∀ a b : Fin 5, a ≠ b → pair a b ∈ N := by
    intro a b hab
    obtain ⟨σ, hσ, ha, hb⟩ := exists_apply_eq hij hab
    have h := hN σ hσ _ hp
    rwa [act_pair, ha, hb] at h
  rw [even_eq_sum w hw]
  exact N.add_mem (N.add_mem (N.add_mem (smul_mem _ (hall 0 1 (by decide)))
    (smul_mem _ (hall 0 2 (by decide)))) (smul_mem _ (hall 0 3 (by decide))))
    (smul_mem _ (hall 0 4 (by decide)))

section Pair

variable {N : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))}

@[expose] def act₂ (σ : Perm (Fin 5)) (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) :
    (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) :=
  (act σ m.1, act σ m.2)

theorem card_even : Nat.card {v : Fin 5 → ZMod 2 // IsEven v} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def fst₀ (N : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))) :
    AddSubgroup (Fin 5 → ZMod 2) where
  carrier := {v | (v, 0) ∈ N}
  add_mem' := by
    intro a b ha hb
    have := N.add_mem ha hb
    simpa using this
  zero_mem' := N.zero_mem
  neg_mem' := by
    intro a ha
    have := N.neg_mem ha
    simpa using this

@[expose] def snd' (N : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))) :
    AddSubgroup (Fin 5 → ZMod 2) :=
  N.map (AddMonoidHom.snd _ _)

variable (hNe : ∀ m ∈ N, IsEven m.1 ∧ IsEven m.2)
  (hN : ∀ σ ∈ alternatingGroup (Fin 5), ∀ m ∈ N, act₂ σ m ∈ N)

include hN in
theorem fst₀_invariant : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ fst₀ N, act σ v ∈ fst₀ N := by
  intro σ hσ v hv
  have := hN σ hσ _ hv
  show (act σ v, 0) ∈ N
  simpa [act₂, act_zero] using this

include hN in
theorem snd'_invariant : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ snd' N, act σ v ∈ snd' N := by
  rintro σ hσ _ ⟨m, hm, rfl⟩
  exact ⟨act₂ σ m, hN σ hσ m hm, rfl⟩

include hNe hN in
theorem card_le_of_pair_invariant (hN0 : N ≠ ⊥) : 16 ≤ Nat.card N := by
  by_cases h1 : ∃ v ∈ fst₀ N, v ≠ 0
  · obtain ⟨v, hv, hv0⟩ := h1
    have hall : ∀ w : {v : Fin 5 → ZMod 2 // IsEven v}, ((w : Fin 5 → ZMod 2), 0) ∈ N :=
      fun w => mem_of_invariant (fst₀_invariant hN) hv (hNe _ hv).1 hv0 w.2
    rw [← card_even]
    refine Nat.card_le_card_of_injective (fun w => ⟨(w.1, 0), hall w⟩) fun a b h => ?_
    have := congrArg (fun m : N => (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1) h
    exact Subtype.ext this
  · push Not at h1
    obtain ⟨m, hm0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hN0
    have hm2 : (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).2 ≠ 0 := by
      intro h
      apply hm0
      have h' : (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1 = 0 := h1 _ (by
        show ((m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1, 0) ∈ N
        rw [← h]
        exact m.2)
      exact Subtype.ext (Prod.ext h' h)
    have hall : ∀ w : {v : Fin 5 → ZMod 2 // IsEven v}, (w : Fin 5 → ZMod 2) ∈ snd' N :=
      fun w => mem_of_invariant (snd'_invariant hN) ⟨m, m.2, rfl⟩ (hNe _ m.2).2 hm2 w.2
    rw [← card_even]
    choose f hf using fun w : {v : Fin 5 → ZMod 2 // IsEven v} => AddSubgroup.mem_map.mp (hall w)
    refine Nat.card_le_card_of_injective (fun w => ⟨f w, (hf w).1⟩) fun a b h => ?_
    have ha := (hf a).2
    have hb := (hf b).2
    have := congrArg (fun m : N => (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).2) h
    simp only at this
    apply Subtype.ext
    rw [← ha, ← hb]
    exact this

include hNe hN in
theorem exists_proj_of_pair_invariant (hcard : Nat.card N = 16) :
    ∃ π : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) →+ (Fin 5 → ZMod 2),
      (∀ σ m, π (act₂ σ m) = act σ (π m)) ∧ (∀ m ∈ N, π m = 0 → m = 0) ∧
        (∀ m ∈ N, IsEven (π m)) ∧ ∀ v, IsEven v → ∃ m ∈ N, π m = v := by
  by_cases h1 : ∃ v ∈ fst₀ N, v ≠ 0
  · obtain ⟨v, hv, hv0⟩ := h1
    have hall : ∀ w, IsEven w → (w, (0 : Fin 5 → ZMod 2)) ∈ N :=
      fun w hw => mem_of_invariant (fst₀_invariant hN) hv (hNe _ hv).1 hv0 hw
    have hsub : ∀ m ∈ N, m.2 = 0 := by
      intro m hm
      by_contra hm2
      have hinj : Function.Injective (fun w : Option {v : Fin 5 → ZMod 2 // IsEven v} =>
          (match w with
            | none => (⟨m, hm⟩ : N)
            | some w => ⟨((w : Fin 5 → ZMod 2), 0), hall w w.2⟩ : N)) := by
        intro a b h
        rcases a with _ | a <;> rcases b with _ | b
        · rfl
        · exfalso
          have := congrArg (fun m : N => (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).2) h
          exact hm2 this
        · exfalso
          have := congrArg (fun m : N => (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).2) h
          exact hm2 this.symm
        · have := congrArg (fun m : N => (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1) h
          exact congrArg some (Subtype.ext this)
      have hle := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, ← Nat.card_eq_fintype_card,
        card_even, hcard] at hle
      omega
    refine ⟨AddMonoidHom.fst _ _, fun σ m => rfl, fun m hm h => Prod.ext h (hsub m hm),
      fun m hm => (hNe m hm).1, fun w hw => ⟨(w, 0), hall w hw, rfl⟩⟩
  · push Not at h1
    have hN0 : N ≠ ⊥ := by
      intro h
      rw [h, AddSubgroup.card_bot] at hcard
      omega
    obtain ⟨m, hm0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hN0
    have hm2 : (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).2 ≠ 0 := by
      intro h
      apply hm0
      have h' : (m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1 = 0 := h1 _ (by
        show ((m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)).1, 0) ∈ N
        rw [← h]
        exact m.2)
      exact Subtype.ext (Prod.ext h' h)
    refine ⟨AddMonoidHom.snd _ _, fun σ m => rfl, fun m hm h => ?_, fun m hm => (hNe m hm).2,
      fun w hw => ?_⟩
    · have h' : m.1 = 0 := h1 _ (by
        show (m.1, 0) ∈ N
        have e : m = (m.1, 0) := Prod.ext rfl h
        rw [← e]
        exact hm)
      exact Prod.ext h' h
    · exact AddSubgroup.mem_map.mp
        (mem_of_invariant (snd'_invariant hN) ⟨m, m.2, rfl⟩ (hNe _ m.2).2 hm2 hw)

end Pair

@[expose] def q₀ (v : Fin 5 → ZMod 2) : ZMod 2 :=
  v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 0 * v 4 + v 1 * v 2 + v 1 * v 3 + v 1 * v 4 +
    v 2 * v 3 + v 2 * v 4 + v 3 * v 4

local instance decEqPerm : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

local instance decMemAlt : DecidablePred (fun σ : Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Perm.sign.decidableMemKer

@[expose] def movedVec (σ : Perm (Fin 5)) : Fin 5 → ZMod 2 := fun k => if σ k = k then 0 else 1

@[expose] def IsInvAlt (a : Perm (Fin 5)) : Prop := a ∈ alternatingGroup (Fin 5) ∧ a ^ 2 = 1 ∧ a ≠ 1

local instance (a : Perm (Fin 5)) : Decidable (IsInvAlt a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[expose] def PairCond (a b : Perm (Fin 5)) : Prop :=
  IsInvAlt a ∧ IsInvAlt b ∧ a ≠ b ∧ a * b = b * a

local instance (a b : Perm (Fin 5)) : Decidable (PairCond a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

@[expose] def PairFix (a b : Perm (Fin 5)) : Prop :=
  act a (movedVec a) = movedVec a ∧ act b (movedVec a) = movedVec a ∧ IsEven (movedVec a) ∧
    movedVec a ≠ 0 ∧ q₀ (movedVec a) = 0 ∧
      ∀ v, IsEven v → act a v = v → act b v = v → v = 0 ∨ v = movedVec a

local instance (a b : Perm (Fin 5)) : Decidable (PairFix a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem pairFix_of_pairCond : ∀ a b : Perm (Fin 5), PairCond a b → PairFix a b := by
  decide +kernel

theorem fixed_pair {a b : Perm (Fin 5)} (ha : a ∈ alternatingGroup (Fin 5))
    (hb : b ∈ alternatingGroup (Fin 5)) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    act a (movedVec a) = movedVec a ∧ act b (movedVec a) = movedVec a ∧ IsEven (movedVec a) ∧
      movedVec a ≠ 0 ∧ q₀ (movedVec a) = 0 ∧
        ∀ v, IsEven v → act a v = v → act b v = v → v = 0 ∨ v = movedVec a :=
  pairFix_of_pairCond a b ⟨⟨ha, ha2, ha1⟩, ⟨hb, hb2, hb1⟩, hab, hc⟩

theorem sq_eq_one_of_pow_four : ∀ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) → σ ^ 4 = 1 →
    σ ^ 2 = 1 := by
  decide +kernel

theorem exists_fixed_iff (E : Subgroup (alternatingGroup (Fin 5))) (hE : Nat.card E = 4) :
    ∃ v₀, IsEven v₀ ∧ v₀ ≠ 0 ∧ q₀ v₀ = 0 ∧ ∀ v, IsEven v →
      ((∀ e ∈ E, act (e : Perm (Fin 5)) v = v) ↔ v = 0 ∨ v = v₀) := by
  classical
  have hsq : ∀ e ∈ E, (e : Perm (Fin 5)) ^ 2 = 1 := by
    intro e he
    have h4 : (⟨e, he⟩ : E) ^ 4 = 1 := by
      rw [← hE]
      exact pow_card_eq_one'
    have h4' : (e : Perm (Fin 5)) ^ 4 = 1 := by
      have := congrArg (fun x : E => ((x : alternatingGroup (Fin 5)) : Perm (Fin 5))) h4
      simpa using this
    exact sq_eq_one_of_pow_four _ e.2 h4'
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card E ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun x y => Subtype.ext ((h x x.2).trans (h y y.2).symm)⟩
    omega
  obtain ⟨b, hbE, hb1, hba⟩ : ∃ b ∈ E, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : ∀ x : E, x = 1 ∨ x = ⟨a, haE⟩ := by
      intro x
      by_cases hx : (x : alternatingGroup (Fin 5)) = 1
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext (h x x.2 hx))
    have : Nat.card E ≤ 2 := by
      have hinj : Function.Injective (fun x : E => if x = 1 then (0 : Fin 2) else 1) := by
        intro x y hxy
        rcases hsub x with rfl | rfl <;> rcases hsub y with rfl | rfl <;> simp_all
      simpa using Nat.card_le_card_of_injective _ hinj
    omega
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (by simpa [sq] using hsq x hx))
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    calc x * y = (x * y)⁻¹ := (hinv _ (E.mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv y hy, hinv x hx]
  have hne : ∀ x y : alternatingGroup (Fin 5), x ≠ y → (x : Perm (Fin 5)) ≠ y :=
    fun x y h h' => h (Subtype.ext h')
  have hpair : ∀ e ∈ E, e ≠ 1 → e ≠ a → act (e : Perm (Fin 5)) (movedVec a) = movedVec a ∧
      ∀ v, IsEven v → act (a : Perm (Fin 5)) v = v → act (e : Perm (Fin 5)) v = v →
        v = 0 ∨ v = movedVec a := by
    intro e he he1 hea
    obtain ⟨-, h2, -, -, -, h5⟩ := fixed_pair a.2 e.2 (hsq a haE) (hsq e he) (hne _ _ ha1)
      (hne _ _ he1) (hne _ _ hea.symm) (congrArg Subtype.val (hcomm a haE e he))
    exact ⟨h2, h5⟩
  obtain ⟨hfa, -, hev, hne0, hq0, -⟩ := fixed_pair a.2 b.2 (hsq a haE) (hsq b hbE)
    (hne _ _ ha1) (hne _ _ hb1) (hne _ _ hba.symm) (congrArg Subtype.val (hcomm a haE b hbE))
  refine ⟨movedVec a, hev, hne0, hq0, fun v hv => ⟨fun h => (hpair b hbE hb1 hba).2 v hv (h a haE)
    (h b hbE), ?_⟩⟩
  rintro (rfl | rfl) e he
  · exact act_zero _
  · by_cases he1 : e = 1
    · rw [he1]
      exact act_one _
    · by_cases hea : e = a
      · rw [hea]
        exact hfa
      · exact (hpair e he he1 hea).1

theorem q₀_add_eq_one : ∀ v w : Fin 5 → ZMod 2, IsEven v → IsEven w → v ≠ 0 → w ≠ 0 → v ≠ w →
    q₀ v = 0 → q₀ w = 0 → q₀ (v + w) = 1 := by
  decide

theorem q₀_pair : ∀ i j : Fin 5, i ≠ j → q₀ (pair i j) = 1 := by
  decide

theorem q₀_compl : ∀ m : Fin 5, q₀ (1 + Pi.single m 1) = 0 := by
  decide

theorem pair_add_pair :
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → pair a b + pair a c = pair b c := by
  decide

theorem compl_eq : ∀ m : Fin 5,
    (1 + Pi.single m 1 : Fin 5 → ZMod 2) = pair (m + 1) (m + 2) + pair (m + 3) (m + 4) ∧
      pair (m + 3) (m + 4) = pair (m + 1) (m + 3) + pair (m + 1) (m + 4) := by
  decide

theorem three_mul (a : ZMod 2) : a + a + a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

theorem eq_q₀ {q : (Fin 5 → ZMod 2) → ZMod 2}
    (hinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEven v → q (act σ v) = q v)
    (hadd : ∀ u v w, IsEven u → IsEven v → IsEven w →
      q (u + v + w) + q (u + v) + q w = (q (u + w) + q u + q w) + (q (v + w) + q v + q w))
    (hne : ∃ v w, IsEven v ∧ IsEven w ∧ q (v + w) + q v + q w ≠ 0)
    {u : Fin 5 → ZMod 2} (hu : IsEven u) : q u = q₀ u := by
  have h0 : q 0 = 0 := by
    have h := hadd 0 0 0 isEven_zero isEven_zero isEven_zero
    simp only [add_zero] at h
    generalize q 0 = c at h ⊢
    revert c
    decide
  have hpair : ∀ i j, i ≠ j → q (pair i j) = q (pair 0 1) := by
    intro i j hij
    obtain ⟨σ, hσ, hi, hj⟩ := exists_apply_eq (i := 0) (j := 1) (by decide) hij
    rw [← hi, ← hj, ← act_pair, hinv σ hσ _ (isEven_pair 0 1)]
  have hpol : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      q (pair a b + pair a c) + q (pair a b) + q (pair a c) = q (pair 0 1) := by
    intro a b c hab hac hbc
    rw [pair_add_pair a b c hab hac hbc, hpair b c hbc, hpair a b hab, hpair a c hac, three_mul]
  have hcompl : ∀ m : Fin 5, q (1 + Pi.single m 1) = 0 := by
    intro m
    obtain ⟨e1, e2⟩ := compl_eq m
    have hd : ∀ x y : Fin 5, x ≠ y → m + x ≠ m + y := fun x y h h' => h (add_left_cancel h')
    have h12 : m + 1 ≠ m + 2 := hd 1 2 (by decide)
    have h13 : m + 1 ≠ m + 3 := hd 1 3 (by decide)
    have h14 : m + 1 ≠ m + 4 := hd 1 4 (by decide)
    have h23 : m + 2 ≠ m + 3 := hd 2 3 (by decide)
    have h24 : m + 2 ≠ m + 4 := hd 2 4 (by decide)
    have h34 : m + 3 ≠ m + 4 := hd 3 4 (by decide)
    have hA := hadd (pair (m + 1) (m + 3)) (pair (m + 1) (m + 4)) (pair (m + 1) (m + 2))
      (isEven_pair _ _) (isEven_pair _ _) (isEven_pair _ _)
    rw [← e2] at hA
    have c1 : pair (m + 1) (m + 3) + pair (m + 1) (m + 2) =
        pair (m + 1) (m + 2) + pair (m + 1) (m + 3) := add_comm _ _
    have c2 : pair (m + 1) (m + 4) + pair (m + 1) (m + 2) =
        pair (m + 1) (m + 2) + pair (m + 1) (m + 4) := add_comm _ _
    have c3 : pair (m + 3) (m + 4) + pair (m + 1) (m + 2) =
        pair (m + 1) (m + 2) + pair (m + 3) (m + 4) := add_comm _ _
    rw [c1, c2, c3] at hA
    have p1 := hpol (m + 1) (m + 2) (m + 3) h12 h13 h23
    have p2 := hpol (m + 1) (m + 2) (m + 4) h12 h14 h24
    rw [e1]
    have hq34 : q (pair (m + 3) (m + 4)) = q (pair 0 1) := hpair _ _ h34
    have hq12 : q (pair (m + 1) (m + 2)) = q (pair 0 1) := hpair _ _ h12
    have hq13 : q (pair (m + 1) (m + 3)) = q (pair 0 1) := hpair _ _ h13
    have hq14 : q (pair (m + 1) (m + 4)) = q (pair 0 1) := hpair _ _ h14
    rw [hq34, hq12, hq13, hq14] at hA
    rw [hq12, hq13] at p1
    rw [hq12, hq14] at p2
    generalize q (pair 0 1) = α at hA p1 p2
    generalize q (pair (m + 1) (m + 2) + pair (m + 1) (m + 3)) = β₁ at hA p1
    generalize q (pair (m + 1) (m + 2) + pair (m + 1) (m + 4)) = β₂ at hA p2
    generalize q (pair (m + 1) (m + 2) + pair (m + 3) (m + 4)) = γ at hA ⊢
    revert α β₁ β₂ γ
    decide
  have hq : ∀ u, IsEven u → q u = q (pair 0 1) * q₀ u := by
    intro u hu
    by_cases hu0 : u = 0
    · have : q₀ 0 = 0 := by decide
      rw [hu0, h0, this, mul_zero]
    · rcases even_cases u hu hu0 with ⟨i, j, hij, rfl⟩ | ⟨m, rfl⟩
      · rw [hpair i j hij, q₀_pair i j hij, mul_one]
      · rw [hcompl m, q₀_compl m, mul_zero]
  have hα : q (pair 0 1) = 1 := by
    obtain ⟨a, b, ha, hb, hab⟩ := hne
    rw [hq _ (isEven_add ha hb), hq a ha, hq b hb] at hab
    rcases zmod2_cases (q (pair 0 1)) with h | h
    · rw [h] at hab
      simp at hab
    · exact h
  rw [hq u hu, hα, one_mul]

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_mul_card_le_of_inf_eq_bot
    {N₁ N₂ : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))}
    (h₁ : ∀ m ∈ N₁, IsEven m.1 ∧ IsEven m.2) (h₂ : ∀ m ∈ N₂, IsEven m.1 ∧ IsEven m.2)
    (hinf : N₁ ⊓ N₂ = ⊥) : Nat.card N₁ * Nat.card N₂ ≤ 256 := by
  let f : N₁ × N₂ → {m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) // IsEven m.1 ∧ IsEven m.2} :=
    fun p => ⟨p.1 + p.2, ⟨isEven_add (h₁ _ p.1.2).1 (h₂ _ p.2.2).1,
      isEven_add (h₁ _ p.1.2).2 (h₂ _ p.2.2).2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) + b = a' + b' :=
      congrArg Subtype.val h
    have hmem : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) - a' ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.sub_mem a.2 a'.2, ?_⟩
      have e : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
      rw [e]
      exact N₂.sub_mem b'.2 b.2
    rw [hinf, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    have hb : (b : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) = b' := by
      rw [hmem] at h'
      exact add_left_cancel h'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  have hcard : Nat.card {m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) // IsEven m.1 ∧ IsEven m.2} =
      256 := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivProd (p := IsEven) (q := IsEven)), Nat.card_prod,
      card_even]
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hcard] at hle

theorem exists_add_of_inf_eq_bot {N₁ N₂ : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))}
    (h₁ : ∀ m ∈ N₁, IsEven m.1 ∧ IsEven m.2) (h₂ : ∀ m ∈ N₂, IsEven m.1 ∧ IsEven m.2)
    (hinf : N₁ ⊓ N₂ = ⊥) (hc₁ : 16 ≤ Nat.card N₁) (hc₂ : 16 ≤ Nat.card N₂)
    {m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)} (hm : IsEven m.1 ∧ IsEven m.2) :
    ∃ a ∈ N₁, ∃ b ∈ N₂, a + b = m := by
  let f : N₁ × N₂ → {m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) // IsEven m.1 ∧ IsEven m.2} :=
    fun p => ⟨p.1 + p.2, ⟨isEven_add (h₁ _ p.1.2).1 (h₂ _ p.2.2).1,
      isEven_add (h₁ _ p.1.2).2 (h₂ _ p.2.2).2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) + b = a' + b' :=
      congrArg Subtype.val h
    have hmem : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) - a' ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.sub_mem a.2 a'.2, ?_⟩
      have e : (a : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
      rw [e]
      exact N₂.sub_mem b'.2 b.2
    rw [hinf, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    have hb : (b : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)) = b' := by
      rw [hmem] at h'
      exact add_left_cancel h'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  have hcard : Nat.card {m : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) // IsEven m.1 ∧ IsEven m.2} =
      256 := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivProd (p := IsEven) (q := IsEven)), Nat.card_prod,
      card_even]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hcard] at hle
  have hbij : Function.Bijective f := by
    refine (Function.Injective.bijective_of_nat_card_le hf ?_)
    rw [Nat.card_prod, hcard]
    nlinarith
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨m, hm⟩
  exact ⟨a, a.2, b, b.2, congrArg Subtype.val hab⟩

theorem eq_of_le_of_invariant {M N : AddSubgroup ((Fin 5 → ZMod 2) × (Fin 5 → ZMod 2))}
    (hNM : N ≤ M) (hN0 : N ≠ ⊥) (hNinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ m ∈ N, act₂ σ m ∈ N)
    {π : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) →+ (Fin 5 → ZMod 2)}
    (hπ : ∀ σ m, π (act₂ σ m) = act σ (π m)) (hinj : ∀ m ∈ M, π m = 0 → m = 0)
    (hMe : ∀ m ∈ M, IsEven (π m)) : N = M := by
  refine le_antisymm hNM fun m hm => ?_
  have hinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ N.map π, act σ v ∈ N.map π := by
    rintro σ hσ _ ⟨n, hn, rfl⟩
    exact ⟨act₂ σ n, hNinv σ hσ n hn, hπ σ n⟩
  obtain ⟨n, hn0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hN0
  have hπn : π n ≠ 0 := fun h => hn0 (Subtype.ext (hinj n (hNM n.2) h))
  have hmem := mem_of_invariant hinv ⟨n, n.2, rfl⟩ (hMe n (hNM n.2)) hπn (hMe m hm)
  obtain ⟨k, hk, hkm⟩ := hmem
  have h0 : k - m = 0 := hinj _ (M.sub_mem (hNM hk) hm) (by rw [map_sub, hkm, sub_self])
  rw [sub_eq_zero] at h0
  exact h0 ▸ hk

end CFSG.ComponentClassification.AS81.Sec2V4
