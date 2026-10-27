module

public import CFSG.GroupActions.ExchangeMatsumoto

public section

namespace CFSG.GroupActions.Exchange

variable {W : Type*} [Group W] {S : Set W}

theorem wordProd_reverse (hS2 : ∀ s ∈ S, orderOf s = 2) (l : List S) :
    wordProd S l.reverse = (wordProd S l)⁻¹ := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.reverse_cons, wordProd_append, ih, wordProd_singleton, wordProd_cons, mul_inv_rev,
      inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 s)]

theorem exists_wordProd_eq_of_mem_closure (hS2 : ∀ s ∈ S, orderOf s = 2) {w : W}
    (hw : w ∈ Subgroup.closure S) : ∃ l : List S, wordProd S l = w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact ⟨[⟨x, hx⟩], wordProd_singleton _⟩
  | one => exact ⟨[], wordProd_nil⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨l', rfl⟩ := hy
    exact ⟨l ++ l', wordProd_append l l'⟩
  | inv x _ hx =>
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l.reverse, wordProd_reverse hS2 l⟩

theorem coe_ne_one (hS2 : ∀ s ∈ S, orderOf s = 2) (s : S) : (s : W) ≠ 1 := by
  intro h
  have := hS2 s s.2
  rw [h, orderOf_one] at this
  omega

theorem wordLength_one : wordLength S 1 = 0 :=
  Nat.le_zero.1 (wordLength_wordProd_le (S := S) [])

theorem isReduced_singleton (hS2 : ∀ s ∈ S, orderOf s = 2) (s : S) : IsReduced S [s] :=
  isReduced_iff.2 fun l' hl' => by
    rw [List.length_singleton, Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff]
    rintro rfl
    rw [wordProd_nil, wordProd_singleton] at hl'
    exact coe_ne_one hS2 s hl'.symm

theorem IsReduced.cons_or_exists (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
    (s : S) {l : List S} (hl : IsReduced S l) :
    IsReduced S (s :: l) ∨
      ∃ l' : List S, IsReduced S (s :: l') ∧ wordProd S (s :: l') = wordProd S l := by
  rcases lt_or_ge (wordLength S (wordProd S l)) (wordLength S ((s : W) * wordProd S l)) with
    h | h
  · refine Or.inl (le_antisymm ?_ (wordLength_wordProd_le _))
    rw [List.length_cons, hl.length_eq, wordProd_cons]
    exact h
  · have hne : l ≠ [] := by
      rintro rfl
      have h1 := (isReduced_singleton hS2 s).length_eq
      rw [wordProd_singleton, List.length_singleton] at h1
      rw [wordProd_nil, mul_one, wordLength_one, ← h1] at h
      omega
    rcases exchange_append (p := []) (σ := l) hS2 hex hl hne h with ⟨j, hj, -⟩ | ⟨l', hl', hp⟩
    · exact absurd hj (Nat.not_lt_zero j)
    · exact Or.inr ⟨l', hl', hp⟩

section Lift

variable {M : Type*} [Monoid M] {f : S → M} {F : W → M}

theorem apply_coe_mul_wordProd (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
    (hf2 : ∀ s, f s * f s = 1)
    (hF : ∀ l : List S, IsReduced S l → F (wordProd S l) = (l.map f).prod) (s : S)
    (l : List S) : F (s * wordProd S l) = f s * F (wordProd S l) := by
  obtain ⟨r, hr, hrl⟩ := exists_isReduced_wordProd_eq l
  rw [← hrl]
  rcases hr.cons_or_exists hS2 hex s with hsr | ⟨r', hsr', hp⟩
  · rw [← wordProd_cons, hF _ hsr, hF _ hr, List.map_cons, List.prod_cons]
  · rw [← hp, hF _ hsr', wordProd_cons, ← mul_assoc, coe_mul_self_eq_one hS2, one_mul,
      hF _ hsr'.of_cons, List.map_cons, List.prod_cons, ← mul_assoc, hf2, one_mul]

theorem apply_wordProd_mul_wordProd (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
    (hf2 : ∀ s, f s * f s = 1)
    (hF : ∀ l : List S, IsReduced S l → F (wordProd S l) = (l.map f).prod) (l l' : List S) :
    F (wordProd S l * wordProd S l') = (l.map f).prod * F (wordProd S l') := by
  induction l with
  | nil => rw [wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons s l ih =>
    rw [wordProd_cons, mul_assoc, ← wordProd_append, apply_coe_mul_wordProd hS2 hex hf2 hF,
      wordProd_append, ih, List.map_cons, List.prod_cons, mul_assoc]

end Lift

theorem exchange_coxeter_universal_property (hS2 : ∀ s ∈ S, orderOf s = 2)
    (hgen : Subgroup.closure S = ⊤) (hex : ExchangeCondition S) {M : Type*} [Group M]
    (f : S → M) (hf2 : ∀ s, f s ^ 2 = 1) (hf : BraidRel S f) :
    ∃! F : W →* M, ∀ s : S, F s = f s := by
  have hword : ∀ w : W, ∃ l : List S, IsReduced S l ∧ wordProd S l = w := fun w => by
    obtain ⟨l, rfl⟩ :=
      exists_wordProd_eq_of_mem_closure hS2 (by rw [hgen]; exact Subgroup.mem_top w)
    exact exists_isReduced_wordProd_eq l
  choose L hL hLw using hword
  have hF : ∀ l : List S, IsReduced S l → ((L (wordProd S l)).map f).prod = (l.map f).prod :=
    fun l hl => matsumoto_braid_invariance hS2 hex f hf (hL _) hl (hLw _)
  have hmul := apply_wordProd_mul_wordProd (F := fun w => ((L w).map f).prod) hS2 hex
    (fun s => by rw [← sq, hf2]) hF
  obtain ⟨F, hFs⟩ : ∃ F : W →* M, ∀ s : S, F s = f s :=
    ⟨MonoidHom.mk' (fun w => ((L w).map f).prod) fun u v => by
        simpa only [hLw] using hmul (L u) (L v),
      fun s => by simpa using hF [s] (isReduced_singleton hS2 s)⟩
  exact ⟨F, hFs, fun G hG => MonoidHom.eq_of_eqOn_dense hgen fun x hx =>
    (hG ⟨x, hx⟩).trans (hFs ⟨x, hx⟩).symm⟩

end CFSG.GroupActions.Exchange
