
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowPBase

@[expose] public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ eq_xorBits xorBits_two_pow_of_lt)

theorem card_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = Nat.card {x : Fin n // p x = true} := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter p), List.toFinset_filter,
    List.toFinset_range, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ⟨fun x => ⟨⟨x.1, List.mem_range.1 ?_⟩, ?_⟩,
    fun y => ⟨y.1.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 y.1.2, y.2⟩⟩,
    fun x => rfl, fun y => rfl⟩
  · exact Finset.mem_range.1 (Finset.mem_filter.1 x.2).1 |> List.mem_range.2
  · exact (Finset.mem_filter.1 x.2).2

def eAct (u : Bool) (σ : Equiv.Perm (Fin 64)) (x : ℕ) : ℕ :=
  evalE (bOf u (tupleOf σ)) x

theorem eAct_zero (u : Bool) (σ : Equiv.Perm (Fin 64)) : eAct u σ 0 = 0 := by
  have h := evalE_xor (bOf u (tupleOf σ)) 0 0
  rw [Nat.xor_self] at h
  have h2 : eAct u σ 0 ^^^ eAct u σ 0 = 0 := Nat.xor_self _
  rwa [eAct, ← h] at h2

theorem eAct_lt (u : Bool) (σ : Equiv.Perm (Fin 64)) (x : ℕ) : eAct u σ x < 512 :=
  evalE_lt (bOf_lt u _) x

theorem eAct_xor (u : Bool) (σ : Equiv.Perm (Fin 64)) (x y : ℕ) :
    eAct u σ (x ^^^ y) = eAct u σ x ^^^ eAct u σ y :=
  evalE_xor _ x y

theorem eq_of_eq_on_q {u : Bool} {f g : ℕ → ℕ}
    (hf : ∀ x y, x < 512 → y < 512 → f (x ^^^ y) = f x ^^^ f y)
    (hg : ∀ x y, x < 512 → y < 512 → g (x ^^^ y) = g x ^^^ g y)
    (hfg : ∀ v, v < 64 → f (qOf u v) = g (qOf u v)) {x : ℕ} (hx : x < 512) : f x = g x := by
  have hb : ∀ k, k < 9 → f (2 ^ k) = g (2 ^ k) := by
    intro k hk
    obtain ⟨ha, hb, hc, he⟩ := spanW_spec u k hk
    rw [← he, hf _ _ (Nat.xor_lt_two_pow (n := 9) (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _),
      hf _ _ (qOf_lt u _) (qOf_lt u _),
      hg _ _ (Nat.xor_lt_two_pow (n := 9) (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _),
      hg _ _ (qOf_lt u _) (qOf_lt u _), hfg _ ha, hfg _ hb, hfg _ hc]
  rw [eq_xorBits (n := 9) hf hx, eq_xorBits (n := 9) hg hx]
  exact xorBits_congr_bits fun k hk _ => hb k hk

section EAct

theorem q_eAct {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) (v : Fin 64) :
    qOf u (σ v) = eAct u σ (qOf u v) := by
  have h := validT_of_mem hσ
  simp only [validT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have := h.2 v v.2
  rwa [evalV_tupleOf hσ.1 v.2, fn_val] at this

theorem eAct_unique {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u)
    {τ : Equiv.Perm (Fin 512)} (hτ : ∀ x y, τ (fx9 x y) = fx9 (τ x) (τ y))
    (hq : ∀ v, qF u (σ v) = τ (qF u v)) (x : Fin 512) : (τ x).val = eAct u σ x := by
  rw [← fn9_val]
  refine eq_of_eq_on_q (u := u) (fun a b ha hb => fn9_xor hτ ha hb)
    (fun a b _ _ => eAct_xor u σ a b) (fun v hv => ?_) x.2
  rw [fn9, dite_eq_left (qOf_lt u v)]
  have h := congrArg Fin.val (hq ⟨v, hv⟩)
  simp only [qF] at h
  rw [← h, q_eAct hσ]

theorem eAct_mul {u : Bool} {σ σ' : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) (hσ' : σ' ∈ Gq u)
    {x : ℕ} (hx : x < 512) : eAct u (σ * σ') x = eAct u σ (eAct u σ' x) := by
  refine eq_of_eq_on_q (u := u) (f := eAct u (σ * σ')) (g := fun y => eAct u σ (eAct u σ' y))
    (fun a b _ _ => eAct_xor u _ a b) (fun a b _ _ => by rw [eAct_xor, eAct_xor])
    (fun v hv => ?_) hx
  have e1 := q_eAct (mul_mem hσ hσ') ⟨v, hv⟩
  have e2 := q_eAct hσ' ⟨v, hv⟩
  have e3 := q_eAct hσ (σ' ⟨v, hv⟩)
  simp only at e1 e2
  rw [← e1, ← e2, ← e3]
  rfl

theorem eAct_one (u : Bool) {x : ℕ} (hx : x < 512) : eAct u 1 x = x := by
  have h := eAct_unique (u := u) (σ := 1) (one_mem _) (τ := 1) (fun _ _ => rfl) (fun _ => rfl)
    ⟨x, hx⟩
  exact h.symm

end EAct

theorem mem_insCode {a t : List ℕ} : ∀ {l : List (List ℕ)}, t ∈ insCode a l → t = a ∨ t ∈ l
  | [], h => Or.inl (List.mem_singleton.1 h)
  | b :: l, h => by
    unfold insCode at h
    split at h
    · exact (List.mem_cons.1 h).imp id id
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact (mem_insCode h).imp id (List.mem_cons_of_mem _)

theorem mem_foldr_insCode {t : List ℕ} : ∀ {l : List (List ℕ)}, t ∈ l.foldr insCode [] → t ∈ l
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rw [List.foldr_cons] at h
    rcases mem_insCode h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_foldr_insCode h)

theorem mem_adjoin {x t : List ℕ} {L : List (List ℕ)} (h : t ∈ adjoin x L) :
    t ∈ L ∨ ∃ a ∈ L, t = compT x a := by
  rcases List.mem_append.1 (mem_foldr_insCode h) with h | h
  · exact Or.inl h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    exact Or.inr ⟨a, ha, rfl⟩

theorem mem_extenders {P L : List (List ℕ)} {x : List ℕ} :
    x ∈ extenders P L ↔ x ∈ P ∧ isInvT x = true ∧ x ∉ L ∧ ∀ a ∈ L, compT x a = compT a x := by
  simp [extenders, List.mem_filter, List.all_eq_true, and_assoc]

theorem eq_one_of_tupleOf_eq_idT {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u)
    (h : tupleOf σ = idT) : σ = 1 :=
  tupleOf_injective hσ.1 (one_mem (Gq u)).1 (h.trans tupleOf_one.symm)

section EA

theorem eaCheck_spec (u : Bool) : [idT] ∈ eaList u ∧ ∀ L ∈ eaList u, (∀ a ∈ L, a ∈ pList u) ∧
    (L.map codeT).Nodup ∧ idT ∈ L ∧
      ∀ x ∈ extenders (pList u) L, adjoin x L ∈ eaList u ∧ L.length < (adjoin x L).length := by
  have h := (sylowChecks u).2.1
  simp only [eaCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.1, fun L hL => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.2 L hL
  exact ⟨h1, h2, h3, fun x hx => h4 x hx⟩

theorem exists_ea_mem {u : Bool} {A : Subgroup (Equiv.Perm (Fin 64))} (hA : A ≤ Psub u)
    (hcomm : ∀ σ ∈ A, ∀ τ ∈ A, σ * τ = τ * σ) (hsq : ∀ σ ∈ A, σ * σ = 1) :
    ∃ L ∈ eaList u, (∀ t ∈ L, ∃ σ ∈ A, tupleOf σ = t) ∧ ∀ σ ∈ A, tupleOf σ ∈ L := by
  classical
  obtain ⟨hid, hall⟩ := eaCheck_spec u
  let good : List (List ℕ) → Prop := fun L => ∀ t ∈ L, ∃ σ ∈ A, tupleOf σ = t
  have hgid : good [idT] := fun t ht => ⟨1, one_mem _, by
    rw [List.mem_singleton.1 ht, tupleOf_one]⟩
  let s := (eaList u).toFinset.filter good
  have hs : s.Nonempty := ⟨[idT], Finset.mem_filter.2 ⟨List.mem_toFinset.2 hid, hgid⟩⟩
  obtain ⟨L, hLs, hmax⟩ := s.exists_max_image List.length hs
  obtain ⟨hLe, hLg⟩ := Finset.mem_filter.1 hLs
  have hLe' := List.mem_toFinset.1 hLe
  refine ⟨L, hLe', hLg, fun σ hσ => ?_⟩
  by_contra hnot
  obtain ⟨-, -, hLid, hext⟩ := hall L hLe'
  have hσG : σ ∈ Gq u := (hA hσ).1
  have hx : tupleOf σ ∈ extenders (pList u) L := by
    refine mem_extenders.2 ⟨(hA hσ).2, ?_, hnot, fun a ha => ?_⟩
    · have hne : tupleOf σ ≠ idT := fun h => hnot (h ▸ hLid)
      simp only [isInvT, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      refine ⟨?_, hne⟩
      rw [← tupleOf_mul hσG.1, hsq σ hσ, tupleOf_one]
    · obtain ⟨τ, hτ, rfl⟩ := hLg a ha
      rw [← tupleOf_mul hσG.1, ← tupleOf_mul (hA hτ).1.1, hcomm σ hσ τ hτ]
  obtain ⟨hmem, hlen⟩ := hext _ hx
  have hgood : good (adjoin (tupleOf σ) L) := by
    intro t ht
    rcases mem_adjoin ht with ht | ⟨a, ha, rfl⟩
    · exact hLg t ht
    · obtain ⟨τ, hτ, rfl⟩ := hLg a ha
      exact ⟨σ * τ, mul_mem hσ hτ, tupleOf_mul hσG.1⟩
  have := hmax _ (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hmem, hgood⟩)
  omega

theorem boundCheck_spec (u : Bool) {L : List (List ℕ)} (hL : L ∈ eaList u) (hne : L ≠ [idT]) :
    L.length *
      ((List.range 512).filter fun e => (L.map (bOf u)).all fun B => evalE B e == e).length *
      ((List.range 64).filter fun v => qOf u v == 0 && L.all fun a => evalV a v == v).length <
      2 ^ (if u then 9 else 12) := by
  have h := (sylowChecks u).2.2
  simp only [boundCheck, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h L hL with h | h
  · exact absurd h hne
  · exact h

end EA

section Bound

theorem offender_bound_P {u : Bool} {A : Subgroup (Equiv.Perm (Fin 64))} (hA : A ≤ Psub u)
    (hcomm : ∀ σ ∈ A, ∀ τ ∈ A, σ * τ = τ * σ) (hsq : ∀ σ ∈ A, σ * σ = 1) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card {e : Fin 512 // ∀ σ ∈ A, eAct u σ e = e} *
      Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ A, σ v = v} < 2 ^ (if u then 9 else 12) := by
  obtain ⟨L, hLe, hLg, hLA⟩ := exists_ea_mem hA hcomm hsq
  have hnd : L.Nodup := List.Nodup.of_map codeT ((eaCheck_spec u).2 L hLe).2.1
  have hcard : Nat.card A = L.length := by
    have hbij : Function.Bijective (fun σ : A => (⟨tupleOf σ, hLA σ σ.2⟩ : {t // t ∈ L})) := by
      refine ⟨fun σ σ' h => Subtype.ext (tupleOf_injective (hA σ.2).1.1 (hA σ'.2).1.1
        (congrArg Subtype.val h)), fun t => ?_⟩
      obtain ⟨σ, hσ, he⟩ := hLg t.1 t.2
      exact ⟨⟨σ, hσ⟩, Subtype.ext he⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), ← List.toFinset_card_of_nodup hnd,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun l => List.mem_toFinset.symm)
  have hE : ((List.range 512).filter fun e => (L.map (bOf u)).all fun B => evalE B e == e).length =
      Nat.card {e : Fin 512 // ∀ σ ∈ A, eAct u σ e = e} := by
    rw [card_filter_range]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    constructor
    · intro h σ hσ
      exact h _ (hLA σ hσ)
    · intro h t ht
      obtain ⟨σ, hσ, rfl⟩ := hLg t ht
      exact h σ hσ
  have hV : ((List.range 64).filter fun v => qOf u v == 0 && L.all fun a => evalV a v == v).length =
      Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ A, σ v = v} := by
    rw [card_filter_range]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine and_congr_right fun _ => ⟨fun h σ hσ => ?_, fun h t ht => ?_⟩
    · have := h _ (hLA σ hσ)
      rw [evalV_tupleOf (hA hσ).1.1 v.2, fn_val] at this
      exact Fin.ext this
    · obtain ⟨σ, hσ, rfl⟩ := hLg t ht
      rw [evalV_tupleOf (hA hσ).1.1 v.2, fn_val, h σ hσ]
  have hLne : L ≠ [idT] := by
    intro hL
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have h1 := hLA σ hσ
    rw [hL, List.mem_singleton] at h1
    exact eq_one_of_tupleOf_eq_idT (hA hσ).1 h1
  have := boundCheck_spec u hLe hLne
  rwa [hE, hV, ← hcard] at this

theorem eAct_inv_mul {u : Bool} {g : Equiv.Perm (Fin 64)} (hg : g ∈ Gq u) {x : ℕ} (hx : x < 512) :
    eAct u g⁻¹ (eAct u g x) = x := by
  rw [← eAct_mul (inv_mem hg) hg hx, inv_mul_cancel, eAct_one u hx]

theorem eAct_mul_inv {u : Bool} {g : Equiv.Perm (Fin 64)} (hg : g ∈ Gq u) {x : ℕ} (hx : x < 512) :
    eAct u g (eAct u g⁻¹ x) = x := by
  rw [← eAct_mul hg (inv_mem hg) hx, mul_inv_cancel, eAct_one u hx]

theorem eAct_conj {u : Bool} {g σ : Equiv.Perm (Fin 64)} (hg : g ∈ Gq u) (hσ : σ ∈ Gq u)
    {x : ℕ} (hx : x < 512) : eAct u (g * σ * g⁻¹) (eAct u g x) = eAct u g (eAct u σ x) := by
  rw [eAct_mul (mul_mem hg hσ) (inv_mem hg) (eAct_lt _ _ _), eAct_inv_mul hg hx,
    eAct_mul hg hσ hx]

end Bound

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
