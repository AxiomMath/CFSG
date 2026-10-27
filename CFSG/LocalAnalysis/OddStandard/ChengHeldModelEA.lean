module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelBase

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

@[expose] def eaInvs (M : RegModel) : Array ℕ :=
  ((List.range M.N).filter fun a => a != 0 && M.m a a == 0).toArray

@[expose] def eaL (M : RegModel) : ℕ → Array (Array ℕ)
  | 0 => #[]
  | 1 => (eaInvs M).map fun a => #[0, a]
  | k + 2 => M.eaNext (eaInvs M) (eaL M (k + 1))

theorem eaCounts_eq (M : RegModel) :
    M.eaCounts = [(eaL M 1).size, (eaL M 2).size, (eaL M 3).size, (eaL M 4).size,
      (eaL M 5).size, (eaL M 6).size] := by
  unfold RegModel.eaCounts eaL eaInvs
  rfl

theorem eaMask_foldl_testBit (l : List ℕ) (init i : ℕ) :
    (l.foldl (fun m j => m ||| 1 <<< j) init).testBit i = (init.testBit i || decide (i ∈ l)) := by
  induction l generalizing init with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

theorem eaMask_testBit (E : Array ℕ) (i : ℕ) : (eaMask E).testBit i = decide (i ∈ E.toList) := by
  unfold RegModel.eaMask
  rw [← Array.foldl_toList, eaMask_foldl_testBit]
  simp

theorem mem_iff_of_eaMask_eq {E E' : Array ℕ} (h : eaMask E = eaMask E') (i : ℕ) :
    i ∈ E.toList ↔ i ∈ E'.toList := by
  have h1 := eaMask_testBit E i
  rw [h, eaMask_testBit] at h1
  simpa using h1.symm

@[expose] def eaNextStep (M : RegModel) (E : Array ℕ) (s : Std.HashSet ℕ × Array (Array ℕ))
    (a : ℕ) : Std.HashSet ℕ × Array (Array ℕ) :=
  if (!(eaMask E).testBit a && E.all fun e => M.m a e == M.m e a) = true then
    if (!s.1.contains (eaMask (E ++ E.map fun e => M.m a e))) = true then
      (s.1.insert (eaMask (E ++ E.map fun e => M.m a e)), s.2.push (E ++ E.map fun e => M.m a e))
    else (s.1, s.2)
  else (s.1, s.2)

theorem eaNext_ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem eaNext_eq_foldl (M : RegModel) (invs : Array ℕ) (L : Array (Array ℕ)) :
    M.eaNext invs L = (L.foldl (fun s E => invs.foldl (eaNextStep M E) s) (∅, #[])).2 := by
  unfold RegModel.eaNext
  simp only [Id.run, eaNext_ite_pure_yield, Array.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem eaNext_foldl_preserve {σ α : Type} (f : σ → α → σ) (P : σ → Prop)
    (hP : ∀ s x, P s → P (f s x)) (l : List α) : ∀ s, P s → P (l.foldl f s) := by
  induction l with
  | nil => exact fun s hs => hs
  | cons x l ih => exact fun s hs => ih _ (hP s x hs)

theorem eaNext_foldl_reach {σ α : Type} (f : σ → α → σ) (I Q : σ → Prop)
    (hI : ∀ s x, I s → I (f s x)) (hQ : ∀ s x, I s → Q s → Q (f s x)) (l : List α) {x0 : α}
    (hx0 : x0 ∈ l) (h0 : ∀ s, I s → Q (f s x0)) : ∀ s, I s → Q (l.foldl f s) := by
  induction l with
  | nil => simp at hx0
  | cons x l ih =>
    intro s hs
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx0 with rfl | hx
    · exact (eaNext_foldl_preserve f (fun s => I s ∧ Q s)
        (fun s x h => ⟨hI s x h.1, hQ s x h.1 h.2⟩) l _ ⟨hI _ _ hs, h0 s hs⟩).2
    · exact ih hx _ (hI s x hs)

theorem eaNextStep_inv (M : RegModel) (E : Array ℕ) (s : Std.HashSet ℕ × Array (Array ℕ))
    (a : ℕ) (hs : ∀ m, s.1.contains m = true → ∃ X ∈ s.2, eaMask X = m) :
    ∀ m, (eaNextStep M E s a).1.contains m = true → ∃ X ∈ (eaNextStep M E s a).2,
      eaMask X = m := by
  unfold eaNextStep
  split_ifs with h1 h2
  · intro m hm
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with hm | hm
    · exact ⟨_, Array.mem_push_self, hm⟩
    · obtain ⟨X, hX, hXm⟩ := hs m hm
      exact ⟨X, Array.mem_push_of_mem _ hX, hXm⟩
  · exact hs
  · exact hs

theorem eaNextStep_mono (M : RegModel) (E : Array ℕ) (s : Std.HashSet ℕ × Array (Array ℕ))
    (a : ℕ) {X : Array ℕ} (hX : X ∈ s.2) : X ∈ (eaNextStep M E s a).2 := by
  unfold eaNextStep
  split_ifs
  · exact Array.mem_push_of_mem _ hX
  · exact hX
  · exact hX

theorem eaNextStep_hit (M : RegModel) (E : Array ℕ) (s : Std.HashSet ℕ × Array (Array ℕ))
    (a : ℕ) (hs : ∀ m, s.1.contains m = true → ∃ X ∈ s.2, eaMask X = m)
    (hbit : (eaMask E).testBit a = false) (hall : (E.all fun e => M.m a e == M.m e a) = true) :
    ∃ X ∈ (eaNextStep M E s a).2, eaMask X = eaMask (E ++ E.map fun e => M.m a e) := by
  unfold eaNextStep
  split_ifs with h1 h2
  · exact ⟨_, Array.mem_push_self, rfl⟩
  · exact hs _ (by simpa using h2)
  · simp [hbit, hall] at h1

theorem eaNext_complete (M : RegModel) {invs : Array ℕ} {L : Array (Array ℕ)} {E : Array ℕ}
    (hE : E ∈ L) {a : ℕ} (ha : a ∈ invs) (hbit : (eaMask E).testBit a = false)
    (hall : (E.all fun e => M.m a e == M.m e a) = true) :
    ∃ X ∈ M.eaNext invs L, eaMask X = eaMask (E ++ E.map fun e => M.m a e) := by
  rw [eaNext_eq_foldl, ← Array.foldl_toList]
  let I : Std.HashSet ℕ × Array (Array ℕ) → Prop := fun s =>
    ∀ m, s.1.contains m = true → ∃ X ∈ s.2, eaMask X = m
  let Q : Std.HashSet ℕ × Array (Array ℕ) → Prop := fun s =>
    ∃ X ∈ s.2, eaMask X = eaMask (E ++ E.map fun e => M.m a e)
  have hI : ∀ (E' : Array ℕ) s, I s → I (invs.foldl (eaNextStep M E') s) := fun E' s hs => by
    rw [← Array.foldl_toList]
    exact eaNext_foldl_preserve _ I (fun s a' h => eaNextStep_inv M E' s a' h) _ s hs
  have hQ : ∀ (E' : Array ℕ) s, I s → Q s → Q (invs.foldl (eaNextStep M E') s) :=
    fun E' s _ hs => by
      rw [← Array.foldl_toList]
      exact eaNext_foldl_preserve _ Q (fun s a' ⟨X, hX, hXm⟩ =>
        ⟨X, eaNextStep_mono M E' s a' hX, hXm⟩) _ s hs
  have h0 : ∀ s, I s → Q (invs.foldl (eaNextStep M E) s) := fun s hs => by
    rw [← Array.foldl_toList]
    exact eaNext_foldl_reach _ I Q (fun s a' h => eaNextStep_inv M E s a' h)
      (fun s a' _ ⟨X, hX, hXm⟩ => ⟨X, eaNextStep_mono M E s a' hX, hXm⟩) _
      (Array.mem_def.1 ha) (fun s hs => eaNextStep_hit M E s a hs hbit hall) s hs
  exact eaNext_foldl_reach (fun s E' => invs.foldl (eaNextStep M E') s) I Q
    (fun s E' h => hI E' s h) (fun s E' h hq => hQ E' s h hq) _ (Array.mem_def.1 hE) h0 _
    (fun m hm => by simp at hm)

theorem eaL_exists_coset {H : Type} [Group H] [Finite H] {E F : Subgroup H} (hFE : F ≤ E)
    (hcard : Nat.card E = 2 * Nat.card F) :
    ∃ a ∈ E, a ∉ F ∧ ∀ h ∈ E, h ∈ F ∨ a⁻¹ * h ∈ F := by
  have hF0 : 0 < Nat.card F := Nat.card_pos
  have hidx : (F.subgroupOf E).index = 2 := by
    have h1 := (F.subgroupOf E).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv, hcard] at h1
    have h2 : Nat.card F * (F.subgroupOf E).index = Nat.card F * 2 := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hF0 h2
  obtain ⟨a, haE, haF⟩ : ∃ a ∈ E, a ∉ F := by
    by_contra hcon
    have := Subgroup.card_le_of_le (show E ≤ F from fun x hx => by
      by_contra hxF
      exact hcon ⟨x, hx, hxF⟩)
    omega
  refine ⟨a, haE, haF, fun h hh => ?_⟩
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, haE⟩ : E)⁻¹) (b := ⟨h, hh⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_mem_iff] at key
  by_cases hhF : h ∈ F
  · exact Or.inl hhF
  · exact Or.inr (key.2 (iff_of_false haF hhF))

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem pt_mem_eaInvs (R : Rep M H) {a : H} (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    R.pt a ∈ eaInvs M := by
  unfold eaInvs
  simp only [List.mem_toArray, List.mem_filter, List.mem_range]
  refine ⟨R.pt_lt a, ?_⟩
  have h0 : R.pt a ≠ 0 := fun h => ha1 (R.pt_inj (h.trans R.pt_one.symm))
  have hm : M.m (R.pt a) (R.pt a) = 0 := by rw [← R.pt_mul, ha2, R.pt_one]
  simp [h0, hm]

theorem eaL_complete_aux (R : Rep M H) (k : ℕ) : ∀ E : Subgroup H,
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E = 2 ^ (k + 1) →
    ∃ l ∈ eaL M (k + 1), ∀ e, e ∈ l.toList ↔ ∃ h ∈ E, R.pt h = e := by
  have := R.finite
  induction k with
  | zero =>
    intro E _ h2 hcard
    obtain ⟨a, haE, ha1, hEa⟩ := eaL_exists_coset (F := ⊥) bot_le
      (by rw [hcard, Subgroup.card_bot]; rfl)
    rw [Subgroup.mem_bot] at ha1
    refine ⟨#[0, R.pt a], ?_, fun e => ?_⟩
    · exact Array.mem_map.2 ⟨R.pt a, R.pt_mem_eaInvs ha1 (h2 a haE), rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨1, E.one_mem, R.pt_one⟩
        · exact ⟨a, haE, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        rcases hEa h hh with h1 | h1
        · left
          rw [Subgroup.mem_bot.1 h1, R.pt_one]
        · right
          rw [inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)]
  | succ k ih =>
    intro E hab h2 hcard
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := k + 1)
      (by rw [hcard]; exact pow_dvd_pow 2 (by omega))
    have hFE : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
    have hFc : Nat.card (K.map E.subtype) = 2 ^ (k + 1) := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    obtain ⟨l, hl, hlF⟩ := ih (K.map E.subtype) (fun a ha b hb => hab a (hFE ha) b (hFE hb))
      (fun a ha => h2 a (hFE ha)) hFc
    obtain ⟨a, haE, haF, hEa⟩ := eaL_exists_coset hFE (by rw [hcard, hFc]; ring)
    have ha1 : a ≠ 1 := fun h => haF (h ▸ (K.map E.subtype).one_mem)
    have hbit : (eaMask l).testBit (R.pt a) = false := by
      rw [eaMask_testBit, decide_eq_false_iff_not, hlF]
      rintro ⟨h, hh, hpt⟩
      exact haF (R.pt_inj hpt ▸ hh)
    have hall : (l.all fun e => M.m (R.pt a) e == M.m e (R.pt a)) = true := by
      rw [Array.all_eq_true']
      intro e he
      obtain ⟨f, hf, rfl⟩ := (hlF e).1 (Array.mem_def.1 he)
      rw [← R.pt_mul, ← R.pt_mul, hab a haE f (hFE hf)]
      simp
    obtain ⟨X, hX, hXm⟩ := eaNext_complete M hl (R.pt_mem_eaInvs ha1 (h2 a haE)) hbit hall
    refine ⟨X, hX, fun e => ?_⟩
    rw [mem_iff_of_eaMask_eq hXm]
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map, hlF]
    constructor
    · rintro (⟨h, hh, rfl⟩ | ⟨e', ⟨f, hf, rfl⟩, rfl⟩)
      · exact ⟨h, hFE hh, rfl⟩
      · exact ⟨a * f, E.mul_mem haE (hFE hf), R.pt_mul a f⟩
    · rintro ⟨h, hh, rfl⟩
      rcases hEa h hh with hF | hF
      · exact Or.inl ⟨h, hF, rfl⟩
      · exact Or.inr ⟨R.pt (a⁻¹ * h), ⟨_, hF, rfl⟩, by rw [← R.pt_mul, mul_inv_cancel_left]⟩

theorem eaL_complete (R : Rep M H) (k : ℕ) (hk : 1 ≤ k) (E : Subgroup H)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 2 ^ k) :
    ∃ l ∈ eaL M k, ∀ h : H, h ∈ E ↔ R.pt h ∈ l.toList := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, hl, hlE⟩ := eaL_complete_aux R j E hab h2 hcard
  refine ⟨l, hl, fun h => ?_⟩
  rw [hlE]
  exact ⟨fun hh => ⟨h, hh, rfl⟩, fun ⟨h', hh', hpt⟩ => R.pt_inj hpt ▸ hh'⟩

end Rep

end CFSG.OddStandard.ChengHeld.Model
