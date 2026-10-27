module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem St.live_lt {st : St} {c : ℕ} (h : st.live c = true) : 0 < c ∧ c < st.next := by
  simp only [St.live, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem St.live_one {L : ℕ} {st : St} (h : st.complete L = true) : st.live 1 = true := by
  unfold St.complete at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem St.complete_step {L : ℕ} {st : St} (hc : st.complete L = true) {c x : ℕ}
    (hl : st.live c = true) (hx : x < L) : st.live (st.tab.getD (c * L + x) 0) = true := by
  unfold St.complete at hc
  rw [Bool.and_eq_true, allBelow_iff] at hc
  obtain ⟨-, hrow⟩ := hc
  have hr := hrow c (St.live_lt hl).2
  simp only [hl, Bool.not_true, Bool.false_or, allBelow_iff] at hr
  exact hr x hx

theorem St.tab_ne_zero {L : ℕ} {st : St} (hc : st.complete L = true) {c x : ℕ}
    (hl : st.live c = true) (hx : x < L) : st.tab.getD (c * L + x) 0 ≠ 0 := by
  have := (St.live_lt (St.complete_step hc hl hx)).1
  omega

@[expose] def invConsistent (L : ℕ) (inv : Array ℕ) (st : St) : Bool :=
  allBelow (fun c => !st.live c || allBelow (fun x =>
    st.tab.getD (st.tab.getD (c * L + x) 0 * L + inv.getD x 0) 0 == c) L) st.next

@[expose] def relsClosed (L : ℕ) (st : St) (rels : List (List ℕ)) : Bool :=
  allBelow (fun c => !st.live c || rels.all fun r =>
    r.foldl (fun c x => st.tab.getD (c * L + x) 0) c == c) st.next

theorem invConsistent_spec {L : ℕ} {inv : Array ℕ} {st : St}
    (h : invConsistent L inv st = true) {c x : ℕ} (hl : st.live c = true) (hx : x < L) :
    st.tab.getD (st.tab.getD (c * L + x) 0 * L + inv.getD x 0) 0 = c := by
  unfold invConsistent at h
  rw [allBelow_iff] at h
  have := h c (St.live_lt hl).2
  simp only [hl, Bool.not_true, Bool.false_or, allBelow_iff, beq_iff_eq] at this
  exact this x hx

theorem relsClosed_spec {L : ℕ} {st : St} {rels : List (List ℕ)}
    (h : relsClosed L st rels = true) {c : ℕ} (hl : st.live c = true) {r : List ℕ}
    (hr : r ∈ rels) : r.foldl (fun c x => st.tab.getD (c * L + x) 0) c = c := by
  unfold relsClosed at h
  rw [allBelow_iff] at h
  have := h c (St.live_lt hl).2
  simp only [hl, Bool.not_true, Bool.false_or, List.all_eq_true, beq_iff_eq] at this
  exact this r hr

theorem presLetter_even {m : ℕ} (rels : Set (FreeGroup (Fin m))) (i : Fin m) :
    presLetter rels (2 * i.val) = PresentedGroup.of i := by
  rw [show 2 * i.val = letterCode (i, true) by simp [letterCode], presLetter_letterCode]
  rfl

theorem presLetter_odd {m : ℕ} (rels : Set (FreeGroup (Fin m))) (i : Fin m) :
    presLetter rels (2 * i.val + 1) = (PresentedGroup.of i)⁻¹ := by
  rw [show 2 * i.val + 1 = letterCode (i, false) by simp [letterCode], presLetter_letterCode,
    show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]
  rfl

abbrev LiveNames (st : St) : Type := {c : ℕ // st.live c = true}

section Act

variable {F : Type*} [Group F] {α : Type*}

theorem act_mul (ψ : F →* (Equiv.Perm α)ᵐᵒᵖ) (g h : F) (c : α) :
    (ψ (g * h)).unop c = (ψ h).unop ((ψ g).unop c) := by
  rw [map_mul]; rfl

theorem act_one (ψ : F →* (Equiv.Perm α)ᵐᵒᵖ) (c : α) : (ψ 1).unop c = c := by
  rw [map_one]; rfl

theorem act_evalWord_step {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y) :
    ∀ w : List ℕ, (∀ y ∈ w, y < L) → ∀ c : {c : ℕ // live c},
      ((ψ (evalWord gen w)).unop c).1 = w.foldl δ c.1 := by
  intro w
  induction w with
  | nil => intro _ c; rw [evalWord_nil, act_one]; rfl
  | cons y w ih =>
    intro hw c
    have hy : y < L := hw y (by simp)
    rw [evalWord_cons, act_mul, ih (fun z hz => hw z (by simp [hz])), htab y hy c,
      List.foldl_cons]

theorem act_evalWord {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0) :
    ∀ w : List ℕ, (∀ y ∈ w, y < L) → ∀ c : LiveNames st,
      ((ψ (evalWord gen w)).unop c).1 = w.foldl (fun c x => st.tab.getD (c * L + x) 0) c.1 :=
  act_evalWord_step (live := fun c => st.live c = true)
    (δ := fun c x => st.tab.getD (c * L + x) 0) ψ htab

theorem minimalPeriod_dvd_orderOf (ψ : F →* (Equiv.Perm α)ᵐᵒᵖ) (g : F) (c : α) :
    Function.minimalPeriod (ψ g).unop c ∣ orderOf g := by
  have h1 : (ψ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h2 : (ψ g).unop ^ orderOf g = 1 := by
    have := congrArg MulOpposite.unop h1
    simpa using this
  have h3 : Function.IsPeriodicPt (ψ g).unop (orderOf g) c := by
    show ((ψ g).unop)^[orderOf g] c = c
    rw [← Equiv.Perm.coe_pow, h2]
    rfl
  exact h3.minimalPeriod_dvd

theorem iterate_act_evalWord_step {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (k : ℕ) (c : {c : ℕ // live c}) :
    (((ψ (evalWord gen w)).unop)^[k] c).1 = (fun c' => w.foldl δ c')^[k] c.1 := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      act_evalWord_step ψ htab w hw c]

theorem pow_ne_one_of_walk_ne_step {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (k : ℕ) (c : {c : ℕ // live c})
    (hne : (fun c' => w.foldl δ c')^[k] c.1 ≠ c.1) : evalWord gen w ^ k ≠ 1 := by
  intro h
  apply hne
  rw [← iterate_act_evalWord_step ψ htab hw k c]
  have h1 : ((ψ (evalWord gen w)).unop)^[k] c = c := by
    rw [← Equiv.Perm.coe_pow, ← MulOpposite.unop_pow, ← map_pow, h, map_one]
    rfl
  rw [h1]

theorem ne_one_of_walk_ne_step {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (c : {c : ℕ // live c})
    (hne : w.foldl δ c.1 ≠ c.1) : evalWord gen w ≠ 1 := by
  have := pow_ne_one_of_walk_ne_step ψ htab hw 1 c (by simpa using hne)
  simpa using this

theorem cycle_dvd_orderOf_step {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (c : {c : ℕ // live c}) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hret : (fun c' => w.foldl δ c')^[ℓ] c.1 = c.1)
    (hmin : ∀ j, 0 < j → j < ℓ → (fun c' => w.foldl δ c')^[j] c.1 ≠ c.1) :
    ℓ ∣ orderOf (evalWord gen w) := by
  set σ := (ψ (evalWord gen w)).unop with hσ
  have hper : Function.IsPeriodicPt σ ℓ c := by
    apply Subtype.ext
    show (σ^[ℓ] c).1 = c.1
    rw [hσ, iterate_act_evalWord_step ψ htab hw, hret]
  have hmp : Function.minimalPeriod σ c = ℓ := by
    apply le_antisymm (hper.minimalPeriod_le hℓ)
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hpos : 0 < Function.minimalPeriod σ c := hper.minimalPeriod_pos hℓ
    have hfix := Function.isPeriodicPt_minimalPeriod σ c
    apply hmin _ hpos hlt'
    have := congrArg Subtype.val hfix
    rw [hσ, iterate_act_evalWord_step ψ htab hw] at this
    exact this
  rw [← hmp]
  exact minimalPeriod_dvd_orderOf ψ _ c

theorem cycle_le_orderOf_step [Finite F] {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : {c : ℕ // live c}, ((ψ (gen y)).unop c).1 = δ c.1 y)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (c : {c : ℕ // live c}) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hret : (fun c' => w.foldl δ c')^[ℓ] c.1 = c.1)
    (hmin : ∀ j, 0 < j → j < ℓ → (fun c' => w.foldl δ c')^[j] c.1 ≠ c.1) :
    ℓ ≤ orderOf (evalWord gen w) :=
  Nat.le_of_dvd (orderOf_pos _) (cycle_dvd_orderOf_step ψ htab hw c hℓ hret hmin)

theorem pow_ne_one_of_walk_ne {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) (k : ℕ) {c : ℕ} (hc : st.live c = true)
    (hne : (fun c' => w.foldl (fun c x => st.tab.getD (c * L + x) 0) c')^[k] c ≠ c) :
    evalWord gen w ^ k ≠ 1 :=
  pow_ne_one_of_walk_ne_step (live := fun c => st.live c = true)
    (δ := fun c x => st.tab.getD (c * L + x) 0) ψ htab hw k ⟨c, hc⟩ hne

theorem ne_one_of_walk_ne {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) {c : ℕ} (hc : st.live c = true)
    (hne : w.foldl (fun c x => st.tab.getD (c * L + x) 0) c ≠ c) : evalWord gen w ≠ 1 :=
  ne_one_of_walk_ne_step (live := fun c => st.live c = true)
    (δ := fun c x => st.tab.getD (c * L + x) 0) ψ htab hw ⟨c, hc⟩ hne

theorem cycle_dvd_orderOf {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) {c : ℕ} (hc : st.live c = true) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hret : (fun c' => w.foldl (fun c x => st.tab.getD (c * L + x) 0) c')^[ℓ] c = c)
    (hmin : ∀ j, 0 < j → j < ℓ →
      (fun c' => w.foldl (fun c x => st.tab.getD (c * L + x) 0) c')^[j] c ≠ c) :
    ℓ ∣ orderOf (evalWord gen w) :=
  cycle_dvd_orderOf_step (live := fun c => st.live c = true)
    (δ := fun c x => st.tab.getD (c * L + x) 0) ψ htab hw ⟨c, hc⟩ hℓ hret hmin

theorem cycle_le_orderOf [Finite F] {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) {c : ℕ} (hc : st.live c = true) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hret : (fun c' => w.foldl (fun c x => st.tab.getD (c * L + x) 0) c')^[ℓ] c = c)
    (hmin : ∀ j, 0 < j → j < ℓ →
      (fun c' => w.foldl (fun c x => st.tab.getD (c * L + x) 0) c')^[j] c ≠ c) :
    ℓ ≤ orderOf (evalWord gen w) :=
  Nat.le_of_dvd (orderOf_pos _) (cycle_dvd_orderOf ψ htab hw hc hℓ hret hmin)

@[expose] def cycleLengthAux (L : ℕ) (tab : Array ℕ) (w : List ℕ) (c : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, k, d =>
    let d' := w.foldl (fun c x => tab.getD (c * L + x) 0) d
    if d' = c then k + 1 else cycleLengthAux L tab w c fuel (k + 1) d'

@[expose] def cycleLength (L : ℕ) (tab : Array ℕ) (w : List ℕ) (c fuel : ℕ) : ℕ :=
  cycleLengthAux L tab w c fuel 0 c

theorem cycleLengthAux_spec (L : ℕ) (tab : Array ℕ) (w : List ℕ) (c : ℕ) :
    ∀ (fuel k d ℓ : ℕ), cycleLengthAux L tab w c fuel k d = ℓ → 0 < ℓ →
      k < ℓ ∧ (fun d => w.foldl (fun c x => tab.getD (c * L + x) 0) d)^[ℓ - k] d = c ∧
        ∀ j, 0 < j → j < ℓ - k →
          (fun d => w.foldl (fun c x => tab.getD (c * L + x) 0) d)^[j] d ≠ c := by
  intro fuel
  induction fuel with
  | zero =>
    intro k d ℓ h hℓ
    simp [cycleLengthAux] at h
    omega
  | succ fuel ih =>
    intro k d ℓ h hℓ
    unfold cycleLengthAux at h
    dsimp only at h
    split at h
    · rename_i hd
      subst h
      refine ⟨by omega, ?_, fun j hj hj' => by omega⟩
      simpa using hd
    · rename_i hd
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) _ ℓ h hℓ
      refine ⟨by omega, ?_, ?_⟩
      · rw [show ℓ - k = (ℓ - (k + 1)) + 1 by omega, Function.iterate_succ_apply]
        exact h2
      · intro j hj hj'
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have : j = 1 := by omega
          subst this
          simpa using hd
        · rw [show j = (j - 1) + 1 by omega, Function.iterate_succ_apply]
          exact h3 (j - 1) (by omega) (by omega)

theorem cycleLength_spec (L : ℕ) (tab : Array ℕ) (w : List ℕ) (c fuel ℓ : ℕ)
    (h : cycleLength L tab w c fuel = ℓ) (hℓ : 0 < ℓ) :
    (fun d => w.foldl (fun c x => tab.getD (c * L + x) 0) d)^[ℓ] c = c ∧
      ∀ j, 0 < j → j < ℓ →
        (fun d => w.foldl (fun c x => tab.getD (c * L + x) 0) d)^[j] c ≠ c := by
  obtain ⟨-, h2, h3⟩ := cycleLengthAux_spec L tab w c fuel 0 c ℓ h hℓ
  exact ⟨by simpa using h2, fun j hj hj' => h3 j hj (by omega)⟩

theorem cycleLength_dvd_orderOf {st : St} {L : ℕ} {gen : ℕ → F}
    (ψ : F →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ)
    (htab : ∀ y < L, ∀ c : LiveNames st, ((ψ (gen y)).unop c).1 = st.tab.getD (c.1 * L + y) 0)
    {w : List ℕ} (hw : ∀ y ∈ w, y < L) {c : ℕ} (hc : st.live c = true) {fuel ℓ : ℕ}
    (h : cycleLength L st.tab w c fuel = ℓ) (hℓ : 0 < ℓ) : ℓ ∣ orderOf (evalWord gen w) :=
  cycle_dvd_orderOf ψ htab hw hc hℓ (cycleLength_spec L st.tab w c fuel ℓ h hℓ).1
    (cycleLength_spec L st.tab w c fuel ℓ h hℓ).2

end Act

private theorem invCode_eq (c : ℕ) : invCode c = if c % 2 = 0 then c + 1 else c - 1 := by
  unfold invCode
  by_cases h : c % 2 = 0
  · have : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
    rw [this]; simp [h]
  · have : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hb : Nat.beq (Nat.mod c 2) 0 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [this]; simp [h]

private theorem invCode_invCode (c : ℕ) : invCode (invCode c) = c := by
  rw [invCode_eq c]
  by_cases h : c % 2 = 0
  · rw [ite_eq_left h, invCode_eq, ite_eq_right (by omega)]; omega
  · rw [ite_eq_right h, invCode_eq, ite_eq_left (by omega)]; omega

variable {m : ℕ}

def stepPerm (live : ℕ → Prop) (δ : ℕ → ℕ → ℕ)
    (hlive : ∀ c, live c → ∀ x < 2 * m, live (δ c x))
    (hinv : ∀ c, live c → ∀ x < 2 * m, δ (δ c x) (invCode x) = c) (y : ℕ) :
    Equiv.Perm {c : ℕ // live c} :=
  if hy : y < 2 * m then
    { toFun := fun c => ⟨δ c.1 y, hlive c.1 c.2 y hy⟩
      invFun := fun c => ⟨δ c.1 (invCode y), hlive c.1 c.2 _ (invCode_lt hy)⟩
      left_inv := fun c => Subtype.ext (hinv c.1 c.2 y hy)
      right_inv := fun c => Subtype.ext (by
        have := hinv c.1 c.2 (invCode y) (invCode_lt hy)
        rwa [invCode_invCode] at this) }
  else 1

theorem stepPerm_apply {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ}
    (hlive : ∀ c, live c → ∀ x < 2 * m, live (δ c x))
    (hinv : ∀ c, live c → ∀ x < 2 * m, δ (δ c x) (invCode x) = c) {y : ℕ} (hy : y < 2 * m)
    (c : {c : ℕ // live c}) : (stepPerm live δ hlive hinv y c).1 = δ c.1 y := by
  simp only [stepPerm, hy, ↓reduceDIte]
  rfl

theorem stepPerm_inv {live : ℕ → Prop} {δ : ℕ → ℕ → ℕ}
    (hlive : ∀ c, live c → ∀ x < 2 * m, live (δ c x))
    (hinv : ∀ c, live c → ∀ x < 2 * m, δ (δ c x) (invCode x) = c) {y : ℕ} (hy : y < 2 * m) :
    (stepPerm live δ hlive hinv y)⁻¹ = stepPerm live δ hlive hinv (invCode y) := by
  ext c
  show ((stepPerm live δ hlive hinv y).symm c).1 = (stepPerm live δ hlive hinv (invCode y) c).1
  rw [stepPerm_apply hlive hinv (invCode_lt hy)]
  simp only [stepPerm, hy, ↓reduceDIte]
  rfl

theorem exists_action_step (ws : List (List (Fin m × Bool))) (live : ℕ → Prop) (δ : ℕ → ℕ → ℕ)
    (hlive : ∀ c, live c → ∀ x < 2 * m, live (δ c x))
    (hinv : ∀ c, live c → ∀ x < 2 * m, δ (δ c x) (invCode x) = c)
    (hrel : ∀ c, live c → ∀ r ∈ codes ws, r.foldl δ c = c) :
    ∃ ψ : PG m ws →* (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ, ∀ y < 2 * m, ∀ c : {c : ℕ // live c},
      ((ψ (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} y)).unop c).1 =
        δ c.1 y := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  let f : Fin m → (Equiv.Perm {c : ℕ // live c})ᵐᵒᵖ := fun i =>
    MulOpposite.op (stepPerm live δ hlive hinv (2 * i.val))
  have hg : ∀ x : Fin m × Bool,
      (cond x.2 (f x.1) (f x.1)⁻¹).unop = stepPerm live δ hlive hinv (letterCode x) := by
    intro x
    obtain ⟨i, b⟩ := x
    have hy : 2 * i.val < 2 * m := by omega
    cases b with
    | true =>
      simp only [Bool.cond_true, letterCode, f]
      rfl
    | false =>
      simp only [Bool.false_eq_true, Bool.cond_false, letterCode, f, ite_false,
        MulOpposite.unop_inv, MulOpposite.unop_op]
      rw [stepPerm_inv hlive hinv hy, invCode_eq, ite_eq_left (by omega)]
  have hwalk : ∀ w : List (Fin m × Bool), ∀ c : {c : ℕ // live c},
      (((w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod).unop c).1 =
        (w.map letterCode).foldl δ c.1 := by
    intro w
    induction w with
    | nil => intro c; rfl
    | cons x w ih =>
      intro c
      rw [List.map_cons, List.prod_cons, MulOpposite.unop_mul, Equiv.Perm.mul_apply, ih,
        List.map_cons, List.foldl_cons]
      congr 2
      rw [hg x]
      have hx : letterCode x < 2 * m := by
        obtain ⟨i, b⟩ := x
        simp only [letterCode]; split <;> omega
      rw [stepPerm_apply hlive hinv hx]
  have hrel' : ∀ r ∈ rels, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, rels] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    have hlift : FreeGroup.lift f (FreeGroup.mk w) =
        (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod := FreeGroup.lift_mk
    rw [hlift]
    apply MulOpposite.unop_injective
    ext c
    rw [hwalk w c]
    exact hrel c.1 c.2 _ (List.mem_map_of_mem hw)
  refine ⟨PresentedGroup.toGroup hrel', ?_⟩
  intro y hy c
  have hdiv : y / 2 < m := by omega
  let x : Fin m × Bool := (⟨y / 2, hdiv⟩, decide (y % 2 = 0))
  have hx : letterCode x = y := by
    unfold letterCode
    by_cases h : y % 2 = 0 <;> simp [x, h] <;> omega
  rw [← hx, presLetter_letterCode]
  show ((PresentedGroup.toGroup hrel' (PresentedGroup.mk rels (FreeGroup.mk [x]))).unop c).1 = _
  have hmk : (PresentedGroup.toGroup hrel') (PresentedGroup.mk rels (FreeGroup.mk [x])) =
      FreeGroup.lift f (FreeGroup.mk [x]) := rfl
  rw [hmk, FreeGroup.lift_mk]
  have hhx : (cond x.2 (f x.1) (f x.1)⁻¹).unop = stepPerm live δ hlive hinv y := by
    rw [hg x, hx]
  have hprod : (([x].map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod).unop =
      stepPerm live δ hlive hinv y := by
    simpa using hhx
  rw [hprod, stepPerm_apply hlive hinv hy, hx]

def presPerm (m : ℕ) (st : St) (hc : st.complete (2 * m) = true)
    (hi : invConsistent (2 * m) (invArr m) st = true) (y : ℕ) : Equiv.Perm (LiveNames st) :=
  stepPerm (fun c => st.live c = true) (fun c x => st.tab.getD (c * (2 * m) + x) 0)
    (fun _ hl _ hx => St.complete_step hc hl hx)
    (fun c hl x hx => by
      have := invConsistent_spec hi hl hx
      rwa [invArr_getD hx] at this) y

theorem presPerm_apply {st : St} (hc : st.complete (2 * m) = true)
    (hi : invConsistent (2 * m) (invArr m) st = true) {y : ℕ} (hy : y < 2 * m)
    (c : LiveNames st) : (presPerm m st hc hi y c).1 = st.tab.getD (c.1 * (2 * m) + y) 0 :=
  stepPerm_apply _ _ hy c

theorem presPerm_inv {st : St} (hc : st.complete (2 * m) = true)
    (hi : invConsistent (2 * m) (invArr m) st = true) {y : ℕ} (hy : y < 2 * m) :
    (presPerm m st hc hi y)⁻¹ = presPerm m st hc hi (invCode y) :=
  stepPerm_inv _ _ hy

theorem exists_action (ws : List (List (Fin m × Bool))) {st : St}
    (hc : st.complete (2 * m) = true) (hi : invConsistent (2 * m) (invArr m) st = true)
    (hrel : relsClosed (2 * m) st (codes ws) = true) :
    ∃ ψ : PG m ws →* (Equiv.Perm (LiveNames st))ᵐᵒᵖ, ∀ y < 2 * m,
      (ψ (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} y)).unop =
        presPerm m st hc hi y := by
  obtain ⟨ψ, hψ⟩ := exists_action_step ws (fun c => st.live c = true)
    (fun c x => st.tab.getD (c * (2 * m) + x) 0) (fun _ hl _ hx => St.complete_step hc hl hx)
    (fun c hl x hx => by
      have := invConsistent_spec hi hl hx
      rwa [invArr_getD hx] at this)
    (fun c hl r hr => relsClosed_spec hrel hl hr)
  refine ⟨ψ, fun y hy => ?_⟩
  ext c
  rw [hψ y hy c, presPerm_apply hc hi hy c]

end CFSG.CosetTable
