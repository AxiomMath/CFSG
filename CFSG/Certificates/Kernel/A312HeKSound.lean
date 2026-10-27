module

public import Certificates.Data.Kernel.A312HeK
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsExtra
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx

public section

namespace CFSG.KC.A312HeK

open CFSG.KC.E64F CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin CFSG.Quasithin.A312Words

theorem bnd_iff {m : ℕ} {w : List ℕ} : bnd m w = true ↔ ∀ l ∈ w, l < m := by
  simp [bnd, Nat.blt_eq]

theorem bit_eq (c k : ℕ) : bit c k = c.testBit k := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : c / 2 ^ k % 2 = 1
  · rw [h, Nat.beq_refl]; simp
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)

theorem xor_mod_two (a b : ℕ) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with hc | hc <;> simp_all

theorem chunkAll_sound {n m : ℕ} {f : ℕ → Bool} (hn : n ≤ 1024 * m)
    (h : ∀ c < m, chunkAll n f c = true) : ∀ p < n, f p = true := by
  intro p hp
  have hc := h (p / 1024) (by omega)
  unfold chunkAll at hc
  rw [List.all_eq_true] at hc
  have := hc p (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have hb : Nat.blt p n = true := Nat.blt_eq.mpr hp
  simpa [hb] using this

theorem invChk_sound {L : ℕ → ℕ → ℕ} {n nL m : ℕ} (hn : n ≤ 1024 * m)
    (h : ∀ l < nL, ∀ c < m, invChk L n nL l c = true) :
    ∀ l < nL, ∀ p < n, L (nL + l) (L l p) = p := fun l hl p hp =>
  Nat.eq_of_beq_eq_true (chunkAll_sound hn (h l hl) p hp)

variable {Γ : Type} [Group Γ]

@[expose] def lv (E : List Γ) (l : ℕ) : Γ :=
  if l < E.length then E.getD l 1 else (E.getD (l - E.length) 1)⁻¹

@[expose] def wv (E : List Γ) (w : List ℕ) : Γ := (w.map (lv E)).prod

theorem wv_nil (E : List Γ) : wv E [] = 1 := rfl

theorem wv_append (E : List Γ) (u v : List ℕ) : wv E (u ++ v) = wv E u * wv E v := by
  simp [wv]

theorem wv_cons (E : List Γ) (l : ℕ) (w : List ℕ) : wv E (l :: w) = lv E l * wv E w := by
  simp [wv]

theorem wv_repW (E : List Γ) (w : List ℕ) : ∀ k, wv E (repW k w) = wv E w ^ k
  | 0 => by simp [repW, wv_nil]
  | k + 1 => by
    change wv E (w ++ repW k w) = _
    rw [wv_append, wv_repW E w k, pow_succ']

theorem wv_invW (E : List Γ) : ∀ w : List ℕ, (∀ l ∈ w, l < E.length) →
    wv E (invW E.length w) = (wv E w)⁻¹
  | [], _ => by simp [invW, wv_nil]
  | l :: w, hw => by
    have e : invW E.length (l :: w) = invW E.length w ++ [E.length + l] := by
      simp [invW]
    rw [e, wv_append, wv_invW E w (fun x hx => hw x (List.mem_cons_of_mem _ hx)), wv_cons, wv_cons,
      wv_nil, mul_one, mul_inv_rev]
    have hl := hw l List.mem_cons_self
    congr 1
    simp [lv, hl]

theorem mem_repW {k : ℕ} {w : List ℕ} {l : ℕ} (h : l ∈ repW k w) : l ∈ w := by
  induction k with
  | zero => simp [repW] at h
  | succ k ih =>
    change l ∈ w ++ repW k w at h
    rcases List.mem_append.mp h with h | h
    · exact h
    · exact ih h

theorem wv_mem (E : List Γ) (H : Subgroup Γ) {w : List ℕ} (h : ∀ l ∈ w, lv E l ∈ H) :
    wv E w ∈ H :=
  H.list_prod_mem fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact h l hl

theorem lv_mem (E : List Γ) {l : ℕ} (hl : l < 2 * E.length) :
    lv E l ∈ Subgroup.closure {x | x ∈ E} := by
  have hE : ∀ i < E.length, E.getD i 1 ∈ Subgroup.closure {x | x ∈ E} := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact Subgroup.subset_closure (List.getElem_mem hi)
  unfold lv
  split_ifs with h
  · exact hE l h
  · exact inv_mem (hE _ (by omega))

theorem prod_getD_mem (K : Subgroup Γ) (Xs : List Γ) {u : List ℕ}
    (hu : ∀ a ∈ u, a < Xs.length) (hX : ∀ g ∈ Xs, g ∈ K) :
    (u.map fun a => Xs.getD a 1).prod ∈ K :=
  K.list_prod_mem fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [List.getD_eq_getElem _ _ (hu a ha)]
    exact hX _ (List.getElem_mem _)

variable {n : ℕ} [MulAction Γ (Fin n)]

structure BaseLetters (n : ℕ) [MulAction Γ (Fin n)] (B : List ℕ) (L : ℕ → ℕ → ℕ) (E : List Γ) :
    Prop where
  lt : ∀ b ∈ B, b < n
  base : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1
  eq : ∀ l < E.length, ∀ p < n, L l p = act n (E.getD l 1) p
  inv : ∀ l < E.length, ∀ p < n, L (E.length + l) (L l p) = p

theorem act_inv_act (g : Γ) {p : ℕ} (hp : p < n) : act n g⁻¹ (act n g p) = p := by
  rw [← act_mul _ _ hp, inv_mul_cancel, act_one hp]

variable {B : List ℕ} {L : ℕ → ℕ → ℕ} {E : List Γ}

theorem BaseLetters.lv_eq (h : BaseLetters n B L E) {l : ℕ} (hl : l < 2 * E.length) {p : ℕ}
    (hp : p < n) : L l p = act n (lv E l) p := by
  unfold lv
  split_ifs with h1
  · exact h.eq l h1 p hp
  · obtain ⟨i, rfl⟩ : ∃ i, l = E.length + i := ⟨l - E.length, by omega⟩
    have hi : i < E.length := by omega
    rw [Nat.add_sub_cancel_left]
    have hq := act_lt (E.getD i 1)⁻¹ hp
    have e : p = L i (act n (E.getD i 1)⁻¹ p) := by
      rw [h.eq i hi _ hq, ← act_mul _ _ hp, mul_inv_cancel, act_one hp]
    conv_lhs => rw [e]
    exact h.inv i hi _ hq

theorem BaseLetters.wordF_eq (h : BaseLetters n B L E) :
    ∀ w : List ℕ, (∀ l ∈ w, l < 2 * E.length) → ∀ p < n, wordF L w p = act n (wv E w) p
  | [], _, p, hp => by rw [wv_nil, act_one hp]; rfl
  | l :: w, hw, p, hp => by
    have ih := h.wordF_eq w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) p hp
    change L l (wordF L w p) = _
    rw [ih, h.lv_eq (hw l List.mem_cons_self) (act_lt _ hp), wv_cons, act_mul _ _ hp]

theorem BaseLetters.eq_of (h : BaseLetters n B L E) {g k : Γ}
    (e : ∀ b ∈ B, act n g b = act n k b) : g = k := by
  have := h.base (k⁻¹ * g) fun b hb => by
    rw [act_mul _ _ (h.lt b hb), e b hb, act_inv_act _ (h.lt b hb)]
  exact (inv_mul_eq_one.mp this).symm

theorem BaseLetters.eqB_sound (h : BaseLetters n B L E) {u v : List ℕ}
    (hu : ∀ l ∈ u, l < 2 * E.length) (hv : ∀ l ∈ v, l < 2 * E.length) (hc : eqB L B u v = true) :
    wv E u = wv E v := by
  unfold eqB at hc
  rw [List.all_eq_true] at hc
  refine h.eq_of fun b hb => ?_
  have := Nat.eq_of_beq_eq_true (hc b hb)
  rwa [h.wordF_eq u hu b (h.lt b hb), h.wordF_eq v hv b (h.lt b hb)] at this

theorem BaseLetters.idB_sound (h : BaseLetters n B L E) {u : List ℕ}
    (hu : ∀ l ∈ u, l < 2 * E.length) (hc : idB L B u = true) : wv E u = 1 := by
  unfold idB at hc
  rw [List.all_eq_true] at hc
  refine h.eq_of fun b hb => ?_
  have := Nat.eq_of_beq_eq_true (hc b hb)
  rw [h.wordF_eq u hu b (h.lt b hb)] at this
  rw [this, act_one (h.lt b hb)]

@[expose] noncomputable def xe (E : List Γ) (x : List ℕ × ℕ × ℕ) : Γ := wv E (qW x)

@[expose] noncomputable def olOf (E : List Γ) (xs : List (List ℕ × ℕ × ℕ)) : List Γ :=
  xs.map (xe E) ++ xs.map fun x => (xe E x)⁻¹

theorem olOf_length (E : List Γ) (xs : List (List ℕ × ℕ × ℕ)) :
    (olOf E xs).length = 2 * xs.length := by
  simp [olOf]; omega

theorem alphaW_length (nL : ℕ) (xs : List (List ℕ × ℕ × ℕ)) (t : List ℕ × ℕ × ℕ) :
    (alphaW nL xs t).length = 2 * xs.length + 1 := by
  simp [alphaW]; omega

theorem alpha_map (E : List Γ) {xs : List (List ℕ × ℕ × ℕ)} (t : List ℕ × ℕ × ℕ)
    (hxs : ∀ x ∈ xs, ∀ l ∈ x.1, l < E.length) :
    (alphaW E.length xs t).map (wv E) = olOf E xs ++ [xe E t] := by
  simp only [alphaW, olOf, List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 2
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply, qWi, qW, xe]
  rw [wv_repW, wv_repW, wv_invW E x.1 (hxs x hx), inv_pow]

theorem alpha_bnd (E : List Γ) {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ}
    (hxs : ∀ x ∈ xs, ∀ l ∈ x.1, l < E.length) (ht : ∀ l ∈ t.1, l < E.length) :
    ∀ w ∈ alphaW E.length xs t, ∀ l ∈ w, l < 2 * E.length := by
  intro w hw l hl
  simp only [alphaW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | rfl
  · have := hxs x hx l (mem_repW hl); omega
  · have h1 := mem_repW hl
    simp only [invW, List.mem_map, List.mem_reverse] at h1
    obtain ⟨i, hi, rfl⟩ := h1
    have := hxs x hx i hi; omega
  · have := ht l (mem_repW hl); omega

theorem expW_bnd {A : List (List ℕ)} {m : ℕ} (hA : ∀ w ∈ A, ∀ l ∈ w, l < m) {u : List ℕ}
    (hu : ∀ a ∈ u, a < A.length) : ∀ l ∈ expW A u, l < m := by
  intro l hl
  simp only [expW, List.mem_flatMap] at hl
  obtain ⟨a, ha, hl⟩ := hl
  rw [List.getD_eq_getElem _ _ (hu a ha)] at hl
  exact hA _ (List.getElem_mem _) l hl

theorem wv_expW (E : List Γ) (A : List (List ℕ)) :
    ∀ u : List ℕ, (∀ a ∈ u, a < A.length) →
      wv E (expW A u) = (u.map fun a => (A.map (wv E)).getD a 1).prod
  | [], _ => rfl
  | a :: u, hu => by
    have e : expW A (a :: u) = A.getD a [] ++ expW A u := by simp [expW]
    rw [e, wv_append, wv_expW E A u (fun x hx => hu x (List.mem_cons_of_mem _ hx)),
      List.map_cons, List.prod_cons]
    have ha := hu a List.mem_cons_self
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ (by simpa using ha),
      List.getElem_map]

theorem idx_sound (h : BaseLetters n B L E) {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ}
    {ws : List (List ℕ)} (hc : idxChk L B E.length xs t ws = true) :
    IdxTwoData (Subgroup.closure {x | x ∈ E}) (olOf E xs) (xe E t) ∧
      (∀ x ∈ xs, ∀ l ∈ x.1, l < E.length) ∧ (∀ l ∈ t.1, l < E.length) := by
  simp only [idxChk, Bool.and_eq_true, List.all_eq_true, bnd_iff] at hc
  obtain ⟨⟨⟨⟨⟨hx, ht⟩, ht2⟩, hwl⟩, hwb⟩, hj⟩ := hc
  have hxs : ∀ x ∈ xs, ∀ l ∈ x.1, l < E.length := fun x hx' => (hx x hx').1.1
  have hq : ∀ y : List ℕ × ℕ × ℕ, (∀ l ∈ y.1, l < E.length) → ∀ k, ∀ l ∈ repW k (qW y),
      l < 2 * E.length := fun y hy k l hl => by
    have := hy l (mem_repW (mem_repW hl)); omega
  have hY : ∀ y : List ℕ × ℕ × ℕ, (∀ l ∈ y.1, l < E.length) →
      xe E y ∈ Subgroup.closure {x | x ∈ E} := fun y hy =>
    wv_mem E _ fun l hl => lv_mem E (by have := hy l (mem_repW hl); omega)
  have hA := alpha_map E t hxs
  have hAb := alpha_bnd E hxs ht
  refine ⟨⟨?_, ?_, ?_, hY t ht, ?_, ?_⟩, hxs, ht⟩
  · intro g hg
    simp only [olOf, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨x, hx', rfl⟩ | ⟨x, hx', rfl⟩
    · exact hY x (hxs x hx')
    · exact inv_mem (hY x (hxs x hx'))
  · intro g hg
    simp only [olOf, List.mem_append, List.mem_map] at hg
    have hodd : ∀ x ∈ xs, x.2.2 % 2 = 1 ∧ xe E x ^ x.2.2 = 1 := fun x hx' => by
      refine ⟨Nat.eq_of_beq_eq_true (hx x hx').1.2, ?_⟩
      have := h.idB_sound (hq x (hxs x hx') _) (hx x hx').2
      rwa [wv_repW] at this
    rcases hg with ⟨x, hx', rfl⟩ | ⟨x, hx', rfl⟩
    · exact ⟨_, hodd x hx'⟩
    · exact ⟨x.2.2, (hodd x hx').1, by rw [inv_pow, (hodd x hx').2, inv_one]⟩
  · intro g hg
    simp only [olOf, List.mem_append, List.mem_map] at hg ⊢
    rcases hg with ⟨x, hx', rfl⟩ | ⟨x, hx', rfl⟩
    · exact Or.inr ⟨x, hx', rfl⟩
    · exact Or.inl ⟨x, hx', (inv_inv _).symm⟩
  · have := h.idB_sound (hq t ht 2) ht2
    rwa [wv_repW, pow_two] at this
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hjl, rfl⟩ := List.getElem_of_mem hg
    have hjr := hj j (List.mem_range.mpr hjl)
    have hwj : ∀ a ∈ ws.getD j [], a < (alphaW E.length xs t).length := by
      rw [alphaW_length]
      rw [List.getD_eq_getElem _ _ (by rw [Nat.eq_of_beq_eq_true hwl]; exact hjl)]
      exact hwb _ (List.getElem_mem _)
    have e := h.eqB_sound (expW_bnd hAb hwj) (fun l hl => by
      simp only [List.mem_singleton] at hl; omega) hjr
    rw [wv_cons, wv_nil, mul_one, wv_expW E _ _ hwj, hA] at e
    have e2 : lv E j = E[j] := by simp [lv, hjl, List.getD_eq_getElem _ _ hjl]
    change E[j] ∈ Subgroup.closure {x | x ∈ olOf E xs ++ [xe E t]}
    rw [← e2, ← e]
    refine prod_getD_mem _ _ (fun a ha => ?_) fun g hg => Subgroup.subset_closure hg
    have := hwj a ha
    rw [alphaW_length] at this
    simp [olOf_length]; omega

@[expose] def sp : List Γ → ℕ → Γ
  | [], _ => 1
  | g :: gs, e => (if e % 2 = 1 then g else 1) * sp gs (e / 2)

theorem wv_subW (E : List Γ) : ∀ (V : List (List ℕ)) (e : ℕ), wv E (subW V e) = sp (V.map (wv E)) e
  | [], _ => rfl
  | v :: V, e => by
    change wv E ((bif Nat.beq (e % 2) 1 then v else []) ++ subW V (e / 2)) = _
    rw [wv_append, wv_subW E V (e / 2)]
    simp only [List.map_cons, sp]
    congr 1
    by_cases he : e % 2 = 1
    · rw [he, Nat.beq_refl]; simp
    · rw [if_neg he]
      have : Nat.beq (e % 2) 1 = false := Bool.eq_false_iff.mpr fun h => he (Nat.eq_of_beq_eq_true h)
      rw [this]; rfl

theorem subW_bnd {V : List (List ℕ)} {m : ℕ} (hV : ∀ v ∈ V, ∀ l ∈ v, l < m) :
    ∀ e, ∀ l ∈ subW V e, l < m := by
  induction V with
  | nil => intro e l hl; simp [subW] at hl
  | cons v V ih =>
    intro e l hl
    change l ∈ (bif Nat.beq (e % 2) 1 then v else []) ++ subW V (e / 2) at hl
    rcases List.mem_append.mp hl with hl | hl
    · cases hb : Nat.beq (e % 2) 1
      · rw [hb] at hl; simp at hl
      · rw [hb] at hl; exact hV v List.mem_cons_self l hl
    · exact ih (fun w hw => hV w (List.mem_cons_of_mem _ hw)) _ l hl

theorem sp_zero : ∀ gs : List Γ, sp gs 0 = 1
  | [] => rfl
  | g :: gs => by simp [sp, sp_zero gs]

theorem sp_mem (K : Subgroup Γ) : ∀ (gs : List Γ), (∀ g ∈ gs, g ∈ K) → ∀ e, sp gs e ∈ K
  | [], _, _ => one_mem K
  | g :: gs, hg, e => by
    refine mul_mem ?_ (sp_mem K gs (fun x hx => hg x (List.mem_cons_of_mem _ hx)) _)
    split_ifs
    · exact hg g List.mem_cons_self
    · exact one_mem K

theorem sp_commute {h : Γ} : ∀ (gs : List Γ), (∀ g ∈ gs, Commute h g) → ∀ e, Commute h (sp gs e)
  | [], _, _ => Commute.one_right h
  | g :: gs, hg, e => by
    refine Commute.mul_right ?_ (sp_commute gs (fun x hx => hg x (List.mem_cons_of_mem _ hx)) _)
    split_ifs
    · exact hg g List.mem_cons_self
    · exact Commute.one_right h

theorem sp_cons_two (g : Γ) (gs : List Γ) (e : ℕ) (b : Bool) :
    sp (g :: gs) (2 * e + b.toNat) = (if b then g else 1) * sp gs e := by
  cases b <;> simp [sp, Nat.mul_add_div, Nat.mul_add_mod]

theorem sp_mul_left (z : Γ) : ∀ (gs : List Γ), (∀ g ∈ gs, Commute g z) →
    (∀ g ∈ gs, ∃ k : ℕ, g * g = z ^ k) →
    (∀ a ∈ gs, ∀ b ∈ gs, ∃ k : ℕ, a * b = z ^ k * (b * a)) →
    ∀ h ∈ gs, ∀ e < 2 ^ gs.length, ∃ e' < 2 ^ gs.length, ∃ k : ℕ, h * sp gs e = z ^ k * sp gs e'
  | [], _, _, _, h, hh, _, _ => absurd hh List.not_mem_nil
  | g :: gs, hzc, hsq, hcomm, h, hh, e, he => by
    have hzc' : ∀ x ∈ gs, Commute x z := fun x hx => hzc x (List.mem_cons_of_mem _ hx)
    have hlen : (g :: gs).length = gs.length + 1 := rfl
    rw [hlen, pow_succ] at he ⊢
    have he2 : e / 2 < 2 ^ gs.length := by omega
    have hsp : sp (g :: gs) e = (if e % 2 = 1 then g else 1) * sp gs (e / 2) := rfl
    rcases List.mem_cons.mp hh with rfl | hh'
    · by_cases hb : e % 2 = 1
      · obtain ⟨k, hk⟩ := hsq h List.mem_cons_self
        refine ⟨2 * (e / 2) + (false).toNat, by simp; omega, k, ?_⟩
        rw [sp_cons_two, hsp, if_pos hb, ← mul_assoc, hk]
        simp
      · refine ⟨2 * (e / 2) + (true).toNat, by simp; omega, 0, ?_⟩
        rw [sp_cons_two, hsp, if_neg hb]
        simp
    · obtain ⟨e', he', k', hk'⟩ := sp_mul_left z gs hzc'
        (fun x hx => hsq x (List.mem_cons_of_mem _ hx))
        (fun a ha b hb => hcomm a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        h hh' (e / 2) he2
      have hcg : ∃ k : ℕ, h * (if e % 2 = 1 then g else 1) =
          z ^ k * ((if e % 2 = 1 then g else 1) * h) := by
        split_ifs
        · exact hcomm h hh g List.mem_cons_self
        · exact ⟨0, by simp⟩
      obtain ⟨k, hk⟩ := hcg
      refine ⟨2 * e' + (decide (e % 2 = 1)).toNat, ?_, k + k', ?_⟩
      · cases decide (e % 2 = 1) <;> simp <;> omega
      · rw [sp_cons_two, hsp, ← mul_assoc, hk, mul_assoc, mul_assoc, hk', pow_add]
        have hgz : Commute (if e % 2 = 1 then g else 1) (z ^ k') := by
          split_ifs
          · exact (hzc g List.mem_cons_self).pow_right k'
          · exact Commute.one_left _
        rw [← mul_assoc _ (z ^ k'), hgz.eq]
        by_cases hb : e % 2 = 1 <;> simp [hb, mul_assoc]

theorem sp_cover (z : Γ) (gs : List Γ) (hzz : z * z = 1) (hzc : ∀ g ∈ gs, Commute g z)
    (hsq : ∀ g ∈ gs, ∃ k : ℕ, g * g = z ^ k)
    (hcomm : ∀ a ∈ gs, ∀ b ∈ gs, ∃ k : ℕ, a * b = z ^ k * (b * a)) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gs ∨ g = z}, ∃ e < 2 ^ gs.length, ∃ k : ℕ,
      x = z ^ k * sp gs e := by
  have hzl : ∀ j y, (∃ e < 2 ^ gs.length, ∃ k : ℕ, y = z ^ k * sp gs e) →
      ∃ e < 2 ^ gs.length, ∃ k : ℕ, z ^ j * y = z ^ k * sp gs e := by
    rintro j y ⟨e, he, k, rfl⟩
    exact ⟨e, he, j + k, by rw [← mul_assoc, ← pow_add]⟩
  have hgl : ∀ x ∈ gs, ∀ y, (∃ e < 2 ^ gs.length, ∃ k : ℕ, y = z ^ k * sp gs e) →
      ∃ e < 2 ^ gs.length, ∃ k : ℕ, x * y = z ^ k * sp gs e := by
    rintro x hx y ⟨e, he, k, rfl⟩
    obtain ⟨e', he', k', hk'⟩ := sp_mul_left z gs hzc hsq hcomm x hx e he
    refine ⟨e', he', k + k', ?_⟩
    rw [← mul_assoc, ((hzc x hx).pow_right k).eq, mul_assoc, hk', ← mul_assoc, pow_add]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by positivity, 0, by rw [sp_zero]; simp⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | rfl
    · exact hgl x hx y ih
    · simpa using hzl 1 y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | rfl
    · obtain ⟨k, hk⟩ := hsq x hx
      have hzk : (z ^ k)⁻¹ = z ^ k := by
        rw [← inv_pow, hzi]
      have hxi : x⁻¹ = z ^ k * x := by
        rw [← hzk, ← hk]
        group
      rw [hxi, mul_assoc]
      exact hzl k _ (hgl x hx y ih)
    · rw [hzi]
      simpa using hzl 1 y ih

theorem sp_xor : ∀ (gs : List Γ), (∀ g ∈ gs, g * g = 1) → (∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a) →
    ∀ e e', sp gs e * sp gs e' = sp gs (e ^^^ e')
  | [], _, _, _, _ => by simp [sp]
  | g :: gs, hsq, hc, e, e' => by
    have ih := sp_xor gs (fun x hx => hsq x (List.mem_cons_of_mem _ hx))
      (fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) (e / 2)
      (e' / 2)
    have hgc : Commute g (sp gs (e / 2)) :=
      sp_commute gs (fun x hx => hc g List.mem_cons_self x (List.mem_cons_of_mem _ hx)) _
    have hA' : Commute (if e' % 2 = 1 then g else 1) (sp gs (e / 2)) := by
      split_ifs
      · exact hgc
      · exact Commute.one_left _
    have hg := hsq g List.mem_cons_self
    simp only [sp]
    rw [Nat.xor_div_two, ← ih, xor_mod_two]
    calc (if e % 2 = 1 then g else 1) * sp gs (e / 2) * ((if e' % 2 = 1 then g else 1) * sp gs (e' / 2))
        = (if e % 2 = 1 then g else 1) * (if e' % 2 = 1 then g else 1) *
            (sp gs (e / 2) * sp gs (e' / 2)) := by
          rw [mul_assoc, ← mul_assoc (sp gs _), hA'.symm.eq]
          simp only [mul_assoc]
      _ = _ := by
          congr 1
          rcases Nat.mod_two_eq_zero_or_one e with h1 | h1 <;>
            rcases Nat.mod_two_eq_zero_or_one e' with h2 | h2 <;> simp [h1, h2, hg]

theorem card_closure_sp (gs : List Γ) (hsq : ∀ g ∈ gs, g * g = 1)
    (hc : ∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a)
    (hne : ∀ e, 0 < e → e < 2 ^ gs.length → sp gs e ≠ 1) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = 2 ^ gs.length := by
  have hcov := sp_cover 1 gs (by simp) (fun g _ => Commute.one_right g)
    (fun g hg => ⟨0, by simp [hsq g hg]⟩) (fun a ha b hb => ⟨0, by simp [hc a ha b hb]⟩)
  have hset : {g | g ∈ gs ∨ g = (1 : Γ)} = {g | g ∈ gs} ∪ {1} := by
    ext
    simp [or_comm]
  have hcl : Subgroup.closure {g | g ∈ gs ∨ g = (1 : Γ)} = Subgroup.closure {g | g ∈ gs} := by
    rw [hset, Subgroup.closure_union, Subgroup.closure_singleton_one, sup_bot_eq]
  let f : Fin (2 ^ gs.length) → Subgroup.closure {g | g ∈ gs} := fun e =>
    ⟨sp gs e, sp_mem _ gs (fun g hg => Subgroup.subset_closure hg) e⟩
  have hf : Function.Bijective f := by
    refine ⟨fun e e' hee => ?_, fun x => ?_⟩
    · have hee' : sp gs e'.1 = sp gs e.1 := (congrArg Subtype.val hee).symm
      have h1 : sp gs (e.1 ^^^ e'.1) = 1 := by
        rw [← sp_xor gs hsq hc, hee', sp_xor gs hsq hc, Nat.xor_self, sp_zero]
      by_contra hne'
      have hx0 : e.1 ^^^ e'.1 ≠ 0 := by
        intro h0
        apply hne'
        apply Fin.ext
        have : e'.1 = e.1 ^^^ (e.1 ^^^ e'.1) := by
          rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [this, h0, Nat.xor_zero]
      exact hne _ (Nat.pos_of_ne_zero hx0) (Nat.xor_lt_two_pow e.2 e'.2) h1
    · obtain ⟨e, he, k, hk⟩ := hcov x.1 (by rw [hcl]; exact x.2)
      exact ⟨⟨e, he⟩, Subtype.ext (by simp [f, hk])⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem conj_closure {g : Γ} {S : Set Γ} (hS : ∀ v ∈ S, g⁻¹ * v * g ∈ Subgroup.closure S) :
    ∀ v ∈ Subgroup.closure S, g⁻¹ * v * g ∈ Subgroup.closure S := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem getD_bnd {A : List (List ℕ)} {m : ℕ} (hA : ∀ w ∈ A, ∀ l ∈ w, l < m) (a : ℕ) :
    ∀ l ∈ A.getD a [], l < m := by
  intro l hl
  by_cases ha : a < A.length
  · rw [List.getD_eq_getElem _ _ ha] at hl
    exact hA _ (List.getElem_mem _) l hl
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    simp at hl

theorem BaseLetters.normA_sound (h : BaseLetters n B L E) {A V : List (List ℕ)} {ex : List ℕ}
    {a : ℕ} (hA : ∀ w ∈ A, ∀ l ∈ w, l < 2 * E.length) (hV : ∀ w ∈ V, ∀ l ∈ w, l < 2 * E.length)
    (hc : normA L B A V ex a = true) :
    ∀ v ∈ V.map (wv E), ∃ e, v * wv E (A.getD a []) = wv E (A.getD a []) * sp (V.map (wv E)) e := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hi' : i < V.length := by simpa using hi
  unfold normA at hc
  rw [List.all_eq_true] at hc
  have hci := hc i (List.mem_range.mpr hi')
  dsimp only at hci
  simp only [Bool.and_eq_true] at hci
  have hVi : ∀ l ∈ V.getD i [], l < 2 * E.length := getD_bnd hV i
  have e := h.eqB_sound (u := V.getD i [] ++ A.getD a [])
    (v := A.getD a [] ++ subW V (ex.getD (V.length * a + i) 0))
    (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hVi l hl
      · exact getD_bnd hA a l hl)
    (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact getD_bnd hA a l hl
      · exact subW_bnd hV _ l hl) hci.2
  refine ⟨ex.getD (V.length * a + i) 0, ?_⟩
  rw [wv_append, wv_append, wv_subW, List.getD_eq_getElem _ _ hi'] at e
  simpa using e

theorem BaseLetters.witChk_sound (h : BaseLetters n B L E) {V : List (List ℕ)} {wit : List ℕ}
    (hV : ∀ w ∈ V, ∀ l ∈ w, l < 2 * E.length) (hc : witChk L B V wit = true) :
    ∀ e, 0 < e → e < 2 ^ (V.map (wv E)).length → sp (V.map (wv E)) e ≠ 1 := by
  intro e he0 he1 hsp
  rw [List.length_map] at he1
  unfold witChk at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hi := hall (e - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlt, hmv⟩ := hi
  rw [Nat.sub_add_cancel he0] at hmv
  have hq : B.getD (wit.getD (e - 1) 0) 0 ∈ B := by
    rw [List.getD_eq_getElem _ _ (Nat.blt_eq.mp hlt)]
    exact List.getElem_mem _
  have := h.wordF_eq (subW V e) (subW_bnd hV e) _ (h.lt _ hq)
  rw [wv_subW, hsp, act_one (h.lt _ hq)] at this
  rw [this, Nat.beq_refl] at hmv
  exact absurd hmv (by decide)

theorem hat_sound (h : BaseLetters n B L E) {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ}
    {ws : List (List ℕ)} {pts w1 w2 : List ℕ} {vws : List (List ℕ)} {wit ex : List ℕ}
    (hc : hatChk L n B E.length xs t ws pts w1 w2 vws wit ex = true) :
    IdxTwoData (Subgroup.closure {x | x ∈ E}) (olOf E xs) (xe E t) ∧
    ∃ pf : Fin 6 → Fin n, Function.Injective pf ∧
      (∀ g ∈ olOf E xs ++ [xe E t], ∀ i, ∃ k, g • pf i = pf k) ∧
      ∃ y1 y2 : Γ, y1 ∈ Subgroup.closure {x | x ∈ E} ∧ y2 ∈ Subgroup.closure {x | x ∈ E} ∧
      (∀ i : Fin 6, y1 • pf i = pf (i + 1)) ∧ (∀ i : Fin 6, y2 • pf i = pf (Equiv.swap 0 1 i)) ∧
      ∃ vl : List Γ, (∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ olOf E xs}) ∧
        (∀ g ∈ olOf E xs ++ [xe E t], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
          g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl}) ∧
        (∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) ∧ (∀ a ∈ vl, a * a = 1) ∧
        (∀ a ∈ vl, ∀ i, a • pf i = pf i) ∧ Nat.card (Subgroup.closure {v | v ∈ vl}) = 64 := by
  classical
  unfold hatChk at hc
  rw [List.all_eq_true] at hc
  have hpart : ∀ k < 2 * xs.length + 3,
      hatPart L n B E.length xs t ws pts w1 w2 vws wit ex k = true :=
    fun k hk => hc k (List.mem_range.mpr hk)
  have h0 := hpart 0 (by omega)
  simp only [hatPart, Nat.beq_refl, cond_true, Bool.and_eq_true, List.all_eq_true, bnd_iff] at h0
  obtain ⟨⟨⟨⟨⟨⟨hidx, hsix⟩, hv6⟩, hvb⟩, hvfix⟩, hci⟩, -⟩ := h0
  obtain ⟨hid, hxs, ht⟩ := idx_sound h hidx
  have hAb := alpha_bnd E hxs ht
  have hAm := alpha_map E t hxs
  have hAlen := alphaW_length E.length xs t
  have hglY : ∀ g ∈ olOf E xs ++ [xe E t], g ∈ Subgroup.closure {x | x ∈ E} := fun g hg => by
    rcases List.mem_append.mp hg with hg | hg
    · exact hid.mem g hg
    · rw [List.mem_singleton.mp hg]
      exact hid.tmem
  have hexpY : ∀ u, (∀ a ∈ u, a < (alphaW E.length xs t).length) →
      wv E (expW (alphaW E.length xs t) u) ∈ Subgroup.closure {x | x ∈ E} := fun u hu => by
    rw [wv_expW E _ u hu, hAm]
    refine prod_getD_mem _ _ (fun a ha => ?_) hglY
    have := hu a ha
    rw [hAlen] at this
    simp [olOf_length]
    omega
  unfold sixChk at hsix
  simp only [Bool.and_eq_true, List.all_eq_true, bnd_iff, decide_eq_true_eq,
    List.mem_range] at hsix
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen6, hnd⟩, hlt⟩, hinv⟩, hw1⟩, hw2⟩, h1⟩, h2⟩ := hsix
  have hlen6' : pts.length = 6 := Nat.eq_of_beq_eq_true hlen6
  have hget : ∀ i : Fin 6, pts.getD i.1 0 ∈ pts := fun i => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen6']; exact i.2)]
    exact List.getElem_mem _
  have hptn : ∀ i : Fin 6, pts.getD i.1 0 < n := fun i => Nat.blt_eq.mp (hlt _ (hget i))
  let pf : Fin 6 → Fin n := fun i => ⟨pts.getD i.1 0, hptn i⟩
  have hpf : Function.Injective pf := by
    intro i k hik
    have e : pts.getD i.1 0 = pts.getD k.1 0 := congrArg Fin.val hik
    rw [List.getD_eq_getElem _ _ (by rw [hlen6']; exact i.2),
      List.getD_eq_getElem _ _ (by rw [hlen6']; exact k.2)] at e
    exact Fin.ext ((hnd.getElem_inj_iff).mp e)
  have hact : ∀ (g : Γ) (i : Fin 6), act n g (pts.getD i.1 0) = (g • pf i).val :=
    fun g i => act_eq g (pf i)
  have hperm : ∀ g ∈ olOf E xs ++ [xe E t], ∀ i, ∃ k, g • pf i = pf k := by
    intro g hg i
    rw [← hAm] at hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    have hm : wordF L w (pts.getD i.1 0) ∈ pts := by simpa using hinv w hw _ (hget i)
    rw [h.wordF_eq w (hAb w hw) _ (hptn i), hact] at hm
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hm
    have hk6 : k < 6 := by rw [← hlen6']; exact hk
    refine ⟨⟨k, hk6⟩, Fin.ext ?_⟩
    change (wv E w • pf i).val = pts.getD k 0
    rw [List.getD_eq_getElem _ _ hk, hkv]
  have hy1 := hexpY w1 hw1
  have hy2 := hexpY w2 hw2
  have hb1 := expW_bnd hAb hw1
  have hb2 := expW_bnd hAb hw2
  have hc1 : ∀ i : Fin 6, wv E (expW (alphaW E.length xs t) w1) • pf i = pf (i + 1) := by
    intro i
    have e := Nat.eq_of_beq_eq_true (h1 i.1 i.2)
    unfold pt at e
    rw [h.wordF_eq _ hb1 _ (hptn i), hact] at e
    apply Fin.ext
    rw [e]
    change pts.getD ((i.1 + 1) % 6) 0 = pts.getD (i + 1).1 0
    rw [Fin.val_add]
    rfl
  have hc2 : ∀ i : Fin 6, wv E (expW (alphaW E.length xs t) w2) • pf i =
      pf (Equiv.swap 0 1 i) := by
    intro i
    have e := Nat.eq_of_beq_eq_true (h2 i.1 i.2)
    unfold pt at e
    rw [h.wordF_eq _ hb2 _ (hptn i), hact] at e
    apply Fin.ext
    rw [e]
    have hs : ∀ i : Fin 6, (bif Nat.beq i.1 0 then 1 else bif Nat.beq i.1 1 then 0 else i.1) =
        (Equiv.swap (0 : Fin 6) 1 i).1 := by decide
    change pts.getD _ 0 = pts.getD (Equiv.swap (0 : Fin 6) 1 i).1 0
    rw [hs i]
  have hVb : ∀ w ∈ vws.map (expW (alphaW E.length xs t)), ∀ l ∈ w, l < 2 * E.length := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact expW_bnd hAb fun a ha => by have := hvb u hu a ha; omega
  set vl : List Γ := (vws.map (expW (alphaW E.length xs t))).map (wv E) with hvl
  have hvl6 : vl.length = 6 := by
    rw [hvl, List.length_map, List.length_map]
    exact Nat.eq_of_beq_eq_true hv6
  have hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ olOf E xs} := by
    intro v hv
    rw [hvl, List.map_map] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have hu' : ∀ a ∈ u, a < 2 * xs.length := hvb u hu
    rw [Function.comp_apply, wv_expW E _ u (fun a ha => by have := hu' a ha; omega), hAm]
    have e : (u.map fun a => (olOf E xs ++ [xe E t]).getD a 1) =
        u.map fun a => (olOf E xs).getD a 1 := by
      apply List.map_congr_left
      intro a ha
      rw [List.getD_append _ _ _ _ (by rw [olOf_length]; exact hu' a ha)]
    rw [e]
    exact prod_getD_mem _ _ (fun a ha => by rw [olOf_length]; exact hu' a ha)
      fun g hg => Subgroup.subset_closure hg
  unfold commInv at hci
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hci
  obtain ⟨hsqc, hcc⟩ := hci
  have hvsq : ∀ a ∈ vl, a * a = 1 := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    have := h.idB_sound (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl <;> exact hVb w hw l hl) (hsqc w hw)
    rwa [wv_append] at this
  have hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a := by
    have key : ∀ i (hi : i < vl.length) k (hk : k < i), vl[i] * vl[k] = vl[k] * vl[i] := by
      intro i hi k hk
      have hi' : i < (vws.map (expW (alphaW E.length xs t))).length := by simpa [hvl] using hi
      have hk' : k < (vws.map (expW (alphaW E.length xs t))).length := by omega
      have e := h.eqB_sound (fun l hl => by
          rcases List.mem_append.mp hl with hl | hl <;> exact getD_bnd hVb _ l hl)
        (fun l hl => by
          rcases List.mem_append.mp hl with hl | hl <;> exact getD_bnd hVb _ l hl)
        (hcc i hi' k hk)
      rw [wv_append, wv_append, List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hk'] at e
      simpa [hvl] using e
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    rcases lt_trichotomy k i with hki | rfl | hik
    · exact key i hi k hki
    · rfl
    · exact (key k hk i hik).symm
  have hvfx : ∀ a ∈ vl, ∀ i, a • pf i = pf i := by
    intro a ha i
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    have e := Nat.eq_of_beq_eq_true (hvfix w hw _ (hget i))
    rw [h.wordF_eq w (hVb w hw) _ (hptn i), hact] at e
    exact Fin.ext e
  have hnorm : ∀ a < (alphaW E.length xs t).length,
      normA L B (alphaW E.length xs t) (vws.map (expW (alphaW E.length xs t))) ex a = true := by
    intro a ha
    have hk := hpart (a + 1) (by omega)
    have e1 : Nat.beq (a + 1) 0 = false := rfl
    have e2 : Nat.blt (a + 1) ((alphaW E.length xs t).length + 1) = true :=
      Nat.blt_eq.mpr (by omega)
    simp only [hatPart, e1, e2, cond_false, cond_true, Nat.add_sub_cancel] at hk
    exact hk
  have hVnorm : ∀ g ∈ olOf E xs ++ [xe E t], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl} := by
    intro g hg
    rw [← hAm] at hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hw
    refine conj_closure fun v hv => ?_
    obtain ⟨e, he⟩ := h.normA_sound hAb hVb (hnorm a ha) v hv
    rw [List.getD_eq_getElem _ _ ha] at he
    have e2 : (wv E (alphaW E.length xs t)[a])⁻¹ * v * wv E (alphaW E.length xs t)[a] =
        sp vl e := by
      rw [mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact sp_mem _ vl (fun g hg => Subgroup.subset_closure hg) e
  have hwit : witChk L B (vws.map (expW (alphaW E.length xs t))) wit = true := by
    have hk := hpart (2 * xs.length + 2) (by omega)
    have e1 : Nat.beq (2 * xs.length + 2) 0 = false := rfl
    have e2 : Nat.blt (2 * xs.length + 2) ((alphaW E.length xs t).length + 1) = false :=
      Bool.eq_false_iff.mpr fun hb => by
        have := Nat.blt_eq.mp hb
        omega
    simp only [hatPart, e1, e2, cond_false] at hk
    exact hk
  have hcard := card_closure_sp vl hvsq hvc (h.witChk_sound hVb hwit)
  rw [hvl6] at hcard
  exact ⟨hid, pf, hpf, hperm, _, _, hy1, hy2, hc1, hc2, vl, hvol, hVnorm, hvc, hvsq, hvfx, hcard⟩

theorem repW_nil : ∀ k, repW k ([] : List ℕ) = []
  | 0 => rfl
  | k + 1 => by
    change [] ++ repW k [] = []
    rw [repW_nil k]
    rfl

theorem cond_beq_one {α : Type} (e : ℕ) (x y : α) :
    (bif Nat.beq (e % 2) 1 then x else y) = if e % 2 = 1 then x else y := by
  by_cases he : e % 2 = 1
  · rw [he, Nat.beq_refl]
    rfl
  · rw [if_neg he]
    have : Nat.beq (e % 2) 1 = false := Bool.eq_false_iff.mpr fun h => he (Nat.eq_of_beq_eq_true h)
    rw [this]
    rfl

theorem pow_toNat_xor (z : Γ) (hzz : z * z = 1) (a b : Bool) :
    z ^ a.toNat * z ^ b.toNat = z ^ (a ^^ b).toNat := by
  cases a <;> cases b <;> simp [hzz]

theorem pow_mod_two (z : Γ) (hzz : z * z = 1) (j : ℕ) : z ^ j = z ^ (j % 2) := by
  conv_lhs => rw [← Nat.div_add_mod j 2]
  rw [pow_add, pow_mul, pow_two, hzz, one_pow, one_mul]

theorem rowSum_cons (C : List ℕ) (i : ℕ) (idx : List ℕ) (e : ℕ) :
    rowSum C (i :: idx) e = (if e % 2 = 1 then C.getD i 0 else 0) ^^^ rowSum C idx (e / 2) := by
  rw [← cond_beq_one]
  rfl

theorem rowSum_xor (C : List ℕ) : ∀ (idx : List ℕ) (e f : ℕ),
    rowSum C idx (e ^^^ f) = rowSum C idx e ^^^ rowSum C idx f
  | [], _, _ => by
    change (0 : ℕ) = 0 ^^^ 0
    rw [Nat.xor_self]
  | i :: idx, e, f => by
    rw [rowSum_cons, rowSum_cons, rowSum_cons, Nat.xor_div_two, rowSum_xor C idx, xor_mod_two]
    apply Nat.eq_of_testBit_eq
    intro j
    rcases Nat.mod_two_eq_zero_or_one e with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one f with h2 | h2 <;>
      simp [h1, h2, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_left_comm]

theorem mem_of_testBit_maskOf : ∀ (idx : List ℕ) {k : ℕ}, (maskOf idx).testBit k = true → k ∈ idx
  | [], k, h => by simp [maskOf] at h
  | i :: idx, k, h => by
    have h' : (2 ^ i ||| maskOf idx).testBit k = true := h
    rw [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h'
    rcases h' with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_testBit_maskOf idx h')

theorem gram_sound {C idx : List ℕ} (hg : gramOK C idx = true) {e : ℕ} (he0 : 0 < e)
    (he : e < 2 ^ idx.length) : ∃ k ∈ idx, bit (rowSum C idx e) k = true := by
  unfold gramOK at hg
  rw [List.all_eq_true] at hg
  have hi := hg (e - 1) (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel he0] at hi
  have hne : (rowSum C idx e &&& maskOf idx) ≠ 0 := by
    intro h0
    have : Nat.land (rowSum C idx e) (maskOf idx) = 0 := h0
    rw [this, Nat.beq_refl] at hi
    exact absurd hi (by decide)
  obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hne
  rw [Nat.testBit_land, Bool.and_eq_true] at hk
  exact ⟨k, mem_of_testBit_maskOf idx hk.2, by rw [bit_eq]; exact hk.1⟩

theorem sp_char (C : List ℕ) (wl : List Γ) (z : Γ) (hzz : z * z = 1)
    (hzc : ∀ g ∈ wl, Commute g z) {k : ℕ} :
    ∀ idx : List ℕ, (∀ i ∈ idx, i < wl.length) →
      (∀ i ∈ idx, wl.getD i 1 * wl.getD k 1 =
        z ^ (bit (C.getD i 0) k).toNat * (wl.getD k 1 * wl.getD i 1)) →
      ∀ e, sp (idx.map fun i => wl.getD i 1) e * wl.getD k 1 =
        z ^ (bit (rowSum C idx e) k).toNat * (wl.getD k 1 * sp (idx.map fun i => wl.getD i 1) e)
  | [], _, _, e => by
    have : bit 0 k = false := by rw [bit_eq]; exact Nat.zero_testBit k
    simp [sp, rowSum, this]
  | i :: idx, hlt, hR, e => by
    have ih := sp_char C wl z hzz hzc idx (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => hR x (List.mem_cons_of_mem _ hx)) (e / 2)
    have hgw : wl.getD i 1 ∈ wl := by
      rw [List.getD_eq_getElem _ _ (hlt i List.mem_cons_self)]
      exact List.getElem_mem _
    set g := wl.getD i 1
    set q := wl.getD k 1
    set s := sp (idx.map fun i => wl.getD i 1) (e / 2)
    set gb : Γ := if e % 2 = 1 then g else 1 with hgb
    set cb : Bool := if e % 2 = 1 then bit (C.getD i 0) k else false with hcb
    have hsp : sp ((i :: idx).map fun i => wl.getD i 1) e = gb * s := rfl
    have hgbz : ∀ m : ℕ, gb * z ^ m = z ^ m * gb := fun m => by
      rw [hgb]
      split_ifs
      · exact ((hzc g hgw).pow_right m).eq
      · simp
    have hgbq : gb * q = z ^ cb.toNat * (q * gb) := by
      rw [hgb, hcb]
      split_ifs
      · exact hR i List.mem_cons_self
      · simp
    have hbit : bit (rowSum C (i :: idx) e) k = (cb ^^ bit (rowSum C idx (e / 2)) k) := by
      rw [rowSum_cons, bit_eq, Nat.testBit_xor, bit_eq (rowSum C idx (e / 2)) k, hcb]
      split_ifs
      · rw [bit_eq]
      · rw [Nat.zero_testBit]
    rw [hsp, hbit, ← pow_toNat_xor z hzz, mul_assoc, ih, ← mul_assoc, hgbz, mul_assoc,
      ← mul_assoc gb, hgbq]
    rw [((Commute.refl z).pow_pow _ _).eq]
    simp only [mul_assoc]

theorem ext_sound [Finite Γ] (h : BaseLetters n B L E) {xs : List (List ℕ × ℕ × ℕ)}
    {t : List ℕ × ℕ × ℕ} {ws : List (List ℕ)} {W : List (List ℕ)} {zw : List ℕ}
    {sq C idx ex : List ℕ} (hc : extChk L B E.length xs t ws W zw sq C idx ex = true)
    (ht : t.1 = []) (hidx6 : idx.length = 6) :
    ∃ (ol : List Γ) (Wg : Subgroup Γ), IdxTwoData (Subgroup.closure {x | x ∈ E}) ol 1 ∧
      Wg ≤ Subgroup.closure {x | x ∈ E} ∧ (∀ g ∈ ol, ∀ v ∈ Wg, g⁻¹ * v * g ∈ Wg) ∧
      Nat.card Wg = 2 ^ 7 ∧ IsExtraspecial2 3 Wg := by
  classical
  unfold extChk at hc
  rw [List.all_eq_true] at hc
  have hpart : ∀ k < 2 * xs.length + 2,
      extPart L B E.length xs t ws W zw sq C idx ex k = true :=
    fun k hk => hc k (List.mem_range.mpr hk)
  have h0 := hpart 0 (by omega)
  simp only [extPart, Nat.beq_refl, cond_true, Bool.and_eq_true] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hidc, hWb⟩, hzb⟩, hzW⟩, hz1⟩, hzz⟩, hzc⟩, hrel⟩, hib⟩, hiz⟩, hgram⟩, -⟩ := h0
  obtain ⟨hid, hxs, htb⟩ := idx_sound h hidc
  have ht1 : xe E t = 1 := by
    unfold xe qW
    rw [ht, repW_nil, wv_nil]
  rw [ht1] at hid
  have hAb := alpha_bnd E hxs htb
  have hAm := alpha_map E t hxs
  rw [ht1] at hAm
  have hAlen := alphaW_length E.length xs t
  rw [List.all_eq_true] at hWb hzc
  have hWb' : ∀ w ∈ W, ∀ l ∈ w, l < E.length := fun w hw => bnd_iff.mp (hWb w hw)
  have hWb2 : ∀ w ∈ W, ∀ l ∈ w, l < 2 * E.length := fun w hw l hl => by
    have := hWb' w hw l hl
    omega
  have hzb' : ∀ l ∈ zw, l < 2 * E.length := fun l hl => by
    have := bnd_iff.mp hzb l hl
    omega
  set wl : List Γ := W.map (wv E) with hwl
  set z : Γ := wv E zw with hzdef
  have hwlen : wl.length = W.length := by rw [hwl, List.length_map]
  have hwget : ∀ i < W.length, wl.getD i 1 = wv E (W.getD i []) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hwlen]; exact hi), List.getD_eq_getElem _ _ hi]
    simp [hwl]
  have hwmem : ∀ i < W.length, wl.getD i 1 ∈ wl := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hwlen]; exact hi)]
    exact List.getElem_mem _
  have hWgb : ∀ i, ∀ l ∈ W.getD i [], l < 2 * E.length := getD_bnd hWb2
  have hzW' : zw ∈ W := by simpa using hzW
  have hzwl : z ∈ wl := List.mem_map.mpr ⟨zw, hzW', rfl⟩
  have hzz' : z * z = 1 := by
    have := h.idB_sound (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl <;> exact hzb' l hl) hzz
    rwa [wv_append] at this
  have hz1' : z ≠ 1 := by
    intro e
    have : idB L B zw = true := by
      unfold idB
      rw [List.all_eq_true]
      intro b hb
      rw [h.wordF_eq zw hzb' b (h.lt b hb), ← hzdef, e, act_one (h.lt b hb), Nat.beq_refl]
    rw [this] at hz1
    exact absurd hz1 (by decide)
  have hzc' : ∀ g ∈ wl, Commute g z := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    have := h.eqB_sound (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hWb2 w hw l hl
      · exact hzb' l hl) (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hzb' l hl
      · exact hWb2 w hw l hl) (hzc w hw)
    rwa [wv_append, wv_append] at this
  unfold relChk at hrel
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hrel
  obtain ⟨⟨-, -⟩, hrow⟩ := hrel
  have hdiag : ∀ i < W.length, bit (C.getD i 0) i = false := fun i hi => by
    have := (hrow i hi).1.1.2
    simpa using this
  have hsqi : ∀ i < W.length, ∃ m : ℕ, wl.getD i 1 * wl.getD i 1 = z ^ m := by
    intro i hi
    have hs := (hrow i hi).1.2
    rw [hwget i hi]
    have hb : ∀ l ∈ W.getD i [] ++ W.getD i [], l < 2 * E.length := fun l hl => by
      rcases List.mem_append.mp hl with hl | hl <;> exact hWgb i l hl
    cases hq : Nat.beq (sq.getD i 0) 0
    · rw [hq] at hs
      refine ⟨1, ?_⟩
      have := h.eqB_sound hb hzb' hs
      rw [wv_append] at this
      rw [pow_one]
      exact this
    · rw [hq] at hs
      refine ⟨0, ?_⟩
      have := h.idB_sound hb hs
      rw [wv_append] at this
      rw [pow_zero]
      exact this
  have hlow : ∀ i < W.length, ∀ k < i, bit (C.getD i 0) k = bit (C.getD k 0) i ∧
      wl.getD i 1 * wl.getD k 1 =
        z ^ (bit (C.getD i 0) k).toNat * (wl.getD k 1 * wl.getD i 1) := by
    intro i hi k hk
    obtain ⟨hsym, hr⟩ := (hrow i hi).2 k hk
    have hbeq : ∀ x y : Bool, Bool.beq x y = true → x = y := by decide
    refine ⟨hbeq _ _ hsym, ?_⟩
    rw [hwget i hi, hwget k (by omega)]
    have hb : ∀ u v : List ℕ, (∀ l ∈ u, l < 2 * E.length) → (∀ l ∈ v, l < 2 * E.length) →
        ∀ l ∈ u ++ v, l < 2 * E.length := fun u v hu hv l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hu l hl
      · exact hv l hl
    cases hbit : bit (C.getD i 0) k
    · rw [hbit] at hr
      have := h.eqB_sound (hb _ _ (hWgb i) (hWgb k)) (hb _ _ (hWgb k) (hWgb i)) hr
      rw [wv_append, wv_append] at this
      simpa using this
    · rw [hbit] at hr
      have := h.eqB_sound (hb _ _ (hWgb i) (hWgb k))
        (hb _ _ (hb _ _ hzb' (hWgb k)) (hWgb i)) hr
      simp only [wv_append] at this
      simpa [mul_assoc] using this
  have hR : ∀ i < W.length, ∀ k < W.length, wl.getD i 1 * wl.getD k 1 =
      z ^ (bit (C.getD i 0) k).toNat * (wl.getD k 1 * wl.getD i 1) := by
    intro i hi k hk
    rcases lt_trichotomy k i with hki | rfl | hik
    · exact (hlow i hi k hki).2
    · rw [hdiag k hk]
      simp
    · obtain ⟨hs, hr⟩ := hlow k hk i hik
      rw [hs] at hr
      rw [hr, ← mul_assoc, ← pow_add]
      cases bit (C.getD i 0) k <;> simp [hzz', pow_two]
  have hidxlt : ∀ i ∈ idx, i < W.length := fun i hi => bnd_iff.mp hib i hi
  set gs : List Γ := idx.map fun i => wl.getD i 1 with hgs
  have hgsl : gs.length = 6 := by rw [hgs, List.length_map, hidx6]
  have hgsw : ∀ g ∈ gs, g ∈ wl := fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact hwmem i (hidxlt i hi)
  set Wg : Subgroup Γ := Subgroup.closure {x | x ∈ wl} with hWg
  have hle : Wg ≤ Subgroup.closure {g | g ∈ gs ∨ g = z} := by
    rw [hWg, Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < W.length := by rw [← hwlen]; exact hi
    have hz := hiz
    rw [List.all_eq_true] at hz
    have hzi := hz i (List.mem_range.mpr hi')
    simp only [Bool.or_eq_true, beq_iff_eq] at hzi
    apply Subgroup.subset_closure
    rcases hzi with hzi | hzi
    · left
      refine List.mem_map.mpr ⟨i, by simpa using hzi, ?_⟩
      rw [List.getD_eq_getElem _ _ hi]
    · right
      rw [← List.getD_eq_getElem _ 1 hi, hwget i hi', hzi]
  have hcov := sp_cover z gs hzz' (fun g hg => hzc' g (hgsw g hg))
    (fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      exact hsqi i (hidxlt i hi))
    (fun a ha b hb => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, hR i (hidxlt i hi) k (hidxlt k hk)⟩)
  rw [hgsl] at hcov
  have hchar : ∀ k < W.length, ∀ e j, z ^ j * sp gs e * wl.getD k 1 =
      z ^ (bit (rowSum C idx e) k).toNat * (wl.getD k 1 * (z ^ j * sp gs e)) := by
    intro k hk e j
    have hs := sp_char C wl z hzz' hzc' idx (fun i hi => by rw [hwlen]; exact hidxlt i hi)
      (fun i hi => hR i (hidxlt i hi) k hk) e
    rw [← hgs] at hs
    have hqz : Commute (wl.getD k 1) (z ^ j) := (hzc' _ (hwmem k hk)).pow_right j
    rw [mul_assoc, hs, ← mul_assoc, ((Commute.refl z).pow_pow _ _).eq, mul_assoc, ← mul_assoc _ _ (sp gs e),
      ← hqz.eq]
    simp only [mul_assoc]
  have hpow : ∀ a b : Bool, z ^ a.toNat = z ^ b.toNat → a = b := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one] at hab
      exact absurd hab.symm hz1'
    · simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one] at hab
      exact absurd hab hz1'
    · rfl
  have hwk : ∀ k ∈ idx, wl.getD k 1 ∈ Wg := fun k hk =>
    Subgroup.subset_closure (hwmem k (hidxlt k hk))
  have hzWg : z ∈ Wg := Subgroup.subset_closure hzwl
  have hspW : ∀ e j, z ^ j * sp gs e ∈ Wg := fun e j =>
    mul_mem (pow_mem hzWg j)
      (sp_mem _ gs (fun g hg => Subgroup.subset_closure (hgsw g hg)) e)
  have hcen : ∀ c ∈ Wg, (∀ q ∈ Wg, c * q = q * c) → c = 1 ∨ c = z := by
    intro c hcW hcc
    obtain ⟨e, he, j, rfl⟩ := hcov c (hle hcW)
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · rw [sp_zero, mul_one, pow_mod_two z hzz' j]
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp [hj]
    · obtain ⟨k, hk, hbit⟩ := gram_sound hgram he0 (by rw [hidx6]; exact he)
      have e1 := hchar k (hidxlt k hk) e j
      rw [hbit, hcc _ (hwk k hk), Bool.toNat_true, pow_one] at e1
      exact absurd (mul_right_cancel (e1.symm.trans (one_mul _).symm)) hz1'
  let f : Fin (2 ^ idx.length) × Fin 2 → Wg := fun p => ⟨z ^ p.2.1 * sp gs p.1.1, hspW _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' hpp => ?_, fun x => ?_⟩
    · have he : z ^ p.2.1 * sp gs p.1.1 = z ^ p'.2.1 * sp gs p'.1.1 := congrArg Subtype.val hpp
      have hchi : ∀ k ∈ idx, bit (rowSum C idx p.1.1) k = bit (rowSum C idx p'.1.1) k := by
        intro k hk
        have e1 := hchar k (hidxlt k hk) p.1.1 p.2.1
        have e2 := hchar k (hidxlt k hk) p'.1.1 p'.2.1
        rw [he, e2] at e1
        exact (hpow _ _ (mul_right_cancel e1)).symm
      have hee : p.1 = p'.1 := by
        by_contra hne
        have hx0 : p.1.1 ^^^ p'.1.1 ≠ 0 := by
          intro h0
          apply hne
          apply Fin.ext
          have : p'.1.1 = p.1.1 ^^^ (p.1.1 ^^^ p'.1.1) := by
            rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
          rw [this, h0, Nat.xor_zero]
        obtain ⟨k, hk, hbit⟩ := gram_sound hgram (Nat.pos_of_ne_zero hx0)
          (Nat.xor_lt_two_pow p.1.2 p'.1.2)
        rw [rowSum_xor, bit_eq, Nat.testBit_xor, ← bit_eq, ← bit_eq, hchi k hk] at hbit
        simp at hbit
      have hjj : z ^ p.2.1 = z ^ p'.2.1 := by
        rw [hee] at he
        exact mul_right_cancel he
      have hj : p.2 = p'.2 := by
        by_contra hne
        have hv : p.2.1 ≠ p'.2.1 := fun e => hne (Fin.ext e)
        have h2 := p.2.2
        have h2' := p'.2.2
        rcases (by omega : (p.2.1 = 0 ∧ p'.2.1 = 1) ∨ (p.2.1 = 1 ∧ p'.2.1 = 0)) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hjj <;> simp at hjj
        · exact hz1' hjj.symm
        · exact hz1' hjj
      exact Prod.ext hee hj
    · obtain ⟨e, he, j, hej⟩ := hcov x.1 (hle x.2)
      refine ⟨(⟨e, by rw [hidx6]; exact he⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
      change z ^ (j % 2) * sp gs e = x.1
      rw [hej, ← pow_mod_two z hzz' j]
  have hcard : Nat.card Wg = 2 ^ 7 := by
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, hidx6]
    norm_num
  have hsqw : ∀ a ∈ wl, a * a = 1 ∨ a * a = z := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hi' : i < W.length := by rw [← hwlen]; exact hi
    obtain ⟨m, hm⟩ := hsqi i hi'
    rw [List.getD_eq_getElem _ _ hi] at hm
    rw [hm, pow_mod_two z hzz' m]
    rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2 <;> simp [hm2]
  have hcommw : ∀ a ∈ wl, ∀ b ∈ wl, a * b = b * a ∨ a * b = z * (b * a) := by
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have e := hR i (by rw [← hwlen]; exact hi) k (by rw [← hwlen]; exact hk)
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hk] at e
    rw [e]
    cases bit (C.getD i 0) k <;> simp
  have hext : IsExtraspecial2 3 Wg :=
    isExtraspecial2_of_gens wl z (Subgroup.subset_closure hzwl) hz1' hzz'
      (fun a ha => (hzc' a ha).eq) hsqw hcommw hcen hcard
  have hWY : Wg ≤ Subgroup.closure {x | x ∈ E} := by
    rw [hWg, Subgroup.closure_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    exact wv_mem E _ fun l hl => lv_mem E (hWb2 w hw l hl)
  have hnorm : ∀ g ∈ olOf E xs, ∀ v ∈ Wg, g⁻¹ * v * g ∈ Wg := by
    intro g hg
    have hg' : g ∈ (alphaW E.length xs t).map (wv E) := by
      rw [hAm]
      exact List.mem_append_left _ hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg'
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hw
    have hk := hpart (a + 1) (by omega)
    have e1 : Nat.beq (a + 1) 0 = false := rfl
    simp only [extPart, e1, cond_false, Nat.add_sub_cancel] at hk
    refine conj_closure fun v hv => ?_
    obtain ⟨e, he⟩ := h.normA_sound hAb hWb2 hk v hv
    rw [List.getD_eq_getElem _ _ ha] at he
    have e2 : (wv E (alphaW E.length xs t)[a])⁻¹ * v * wv E (alphaW E.length xs t)[a] =
        sp wl e := by
      rw [mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact sp_mem _ wl (fun g hg => Subgroup.subset_closure hg) e
  exact ⟨olOf E xs, Wg, hid, hWY, hnorm, hcard, hext⟩

end CFSG.KC.A312HeK

end
