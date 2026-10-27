module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.List.GetD

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.FinCode

open Equiv Subgroup

variable {n : ℕ}

section Digits

@[expose] def dig (c i : ℕ) : ℕ := c / 16 ^ i % 16

@[expose] def num : List ℕ → ℕ
  | [] => 0
  | d :: L => d + 16 * num L

theorem dig_num : ∀ (L : List ℕ), (∀ d ∈ L, d < 16) → ∀ i, dig (num L) i = L.getD i 0
  | [], _, i => by simp [dig, num]
  | d :: L, h, 0 => by
    have hd := h d List.mem_cons_self
    simp only [dig, num, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | d :: L, h, i + 1 => by
    have hd := h d List.mem_cons_self
    have ih := dig_num L (fun x hx => h x (List.mem_cons_of_mem d hx)) i
    simp only [dig, num, List.getD_cons_succ] at ih ⊢
    rw [pow_succ', ← Nat.div_div_eq_div_mul, show (d + 16 * num L) / 16 = num L by omega]
    exact ih

@[expose] def enc (σ : Perm (Fin n)) : ℕ := num (List.ofFn fun i => (σ i : ℕ))

theorem digits_lt (hn : n ≤ 16) (σ : Perm (Fin n)) :
    ∀ d ∈ List.ofFn fun i => (σ i : ℕ), d < 16 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  have := (σ i).2
  omega

theorem dig_enc (hn : n ≤ 16) (σ : Perm (Fin n)) (i : Fin n) : dig (enc σ) i = σ i := by
  rw [enc, dig_num _ (digits_lt hn σ), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.2]

theorem enc_injective (hn : n ≤ 16) : Function.Injective (enc (n := n)) := fun σ τ h =>
  Equiv.ext fun i => Fin.ext (by rw [← dig_enc hn σ i, ← dig_enc hn τ i, h])

@[expose] def cmul : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => dig a (b % 16) + 16 * cmul k a (b / 16)

theorem cmul_num (a : ℕ) : ∀ L : List ℕ, (∀ d ∈ L, d < 16) →
    cmul L.length a (num L) = num (L.map (dig a))
  | [], _ => rfl
  | d :: L, h => by
    have hd := h d List.mem_cons_self
    simp only [List.length_cons, cmul, num, List.map_cons]
    rw [show (d + 16 * num L) % 16 = d by omega, show (d + 16 * num L) / 16 = num L by omega,
      cmul_num a L (fun x hx => h x (List.mem_cons_of_mem d hx))]

theorem enc_mul (hn : n ≤ 16) (σ τ : Perm (Fin n)) :
    enc (σ * τ) = cmul n (enc σ) (enc τ) := by
  have h := cmul_num (enc σ) (List.ofFn fun i => (τ i : ℕ)) (digits_lt hn τ)
  rw [List.length_ofFn] at h
  rw [show enc τ = num (List.ofFn fun i => (τ i : ℕ)) from rfl, h, List.map_ofFn]
  show num (List.ofFn fun i => ((σ * τ) i : ℕ)) = _
  congr 1
  congr 1
  funext i
  simp [dig_enc hn σ (τ i)]

theorem mul_eq_iff (hn : n ≤ 16) {σ τ ρ : Perm (Fin n)} :
    σ * τ = ρ ↔ cmul n (enc σ) (enc τ) = enc ρ := by
  rw [← enc_mul hn]
  exact (enc_injective hn).eq_iff.symm

theorem commute_iff (hn : n ≤ 16) {σ τ : Perm (Fin n)} :
    σ * τ = τ * σ ↔ cmul n (enc σ) (enc τ) = cmul n (enc τ) (enc σ) := by
  rw [← enc_mul hn, ← enc_mul hn]
  exact (enc_injective hn).eq_iff.symm

@[expose] def suppN (k c : ℕ) : ℕ := ((Finset.range k).filter fun i => dig c i ≠ i).card

theorem card_support_eq (hn : n ≤ 16) (σ : Perm (Fin n)) : σ.support.card = suppN n (enc σ) := by
  rw [suppN, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Fin.valEmbedding_apply, Perm.mem_support, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2, ?_⟩
    rw [dig_enc hn σ j]
    exact fun h => hj (Fin.ext h)
  · rintro ⟨hi, h⟩
    refine ⟨⟨i, hi⟩, fun h' => h ?_, rfl⟩
    rw [dig_enc hn σ ⟨i, hi⟩, h']

end Digits

section Closure

@[expose] def wordPerm (gens : List (Perm (Fin n))) (w : List ℕ) : Perm (Fin n) :=
  (w.map fun i => gens.getD i 1).prod

@[expose] def wordCode (n e : ℕ) (gc w : List ℕ) : ℕ :=
  w.foldr (fun i acc => cmul n (gc.getD i e) acc) e

theorem enc_wordPerm (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc : List ℕ} {e : ℕ}
    (hgc : gens.map enc = gc) (he : enc (1 : Perm (Fin n)) = e) (w : List ℕ) :
    enc (wordPerm gens w) = wordCode n e gc w := by
  induction w with
  | nil => simpa [wordPerm, wordCode] using he
  | cons i w ih =>
    have h : wordPerm gens (i :: w) = gens.getD i 1 * wordPerm gens w := by
      simp [wordPerm]
    rw [h, enc_mul hn, ih]
    simp only [wordCode, List.foldr_cons]
    congr 1
    rw [← hgc, ← he, List.getD_map]

theorem wordPerm_mem (gens : List (Perm (Fin n))) (w : List ℕ) :
    wordPerm gens w ∈ closure {x | x ∈ gens} := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gens[i]? with
  | none => exact one_mem _
  | some g => exact subset_closure (List.mem_of_getElem? h)

@[expose] def closedB (n : ℕ) (codes gc : List ℕ) : Bool :=
  codes.all fun c => gc.all fun g => codes.contains (cmul n c g)

theorem enc_mem_of_mem_closure (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc codes : List ℕ}
    (hgc : gens.map enc = gc) (hinv : ∀ g ∈ gens, g * g = 1)
    (hone : enc (1 : Perm (Fin n)) ∈ codes) (hcl : closedB n codes gc = true)
    {σ : Perm (Fin n)} (hσ : σ ∈ closure {x | x ∈ gens}) : enc σ ∈ codes := by
  simp only [closedB, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hcl
  have key : ∀ x, enc x ∈ codes → ∀ y ∈ gens, enc (x * y) ∈ codes := by
    intro x hx y hy
    rw [enc_mul hn]
    exact hcl _ hx _ (hgc ▸ List.mem_map_of_mem hy)
  induction hσ using Subgroup.closure_induction_right with
  | one => exact hone
  | mul_right x _ y hy ih => exact key x ih y hy
  | mul_inv_cancel x _ y hy ih =>
    rw [inv_eq_of_mul_eq_one_right (hinv y hy)]
    exact key x ih y hy

theorem exists_of_mem_codes (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc codes : List ℕ}
    {e : ℕ} {words : List (List ℕ)} (hgc : gens.map enc = gc) (he : enc (1 : Perm (Fin n)) = e)
    (hw : words.map (wordCode n e gc) = codes) {c : ℕ} (hc : c ∈ codes) :
    ∃ σ ∈ closure {x | x ∈ gens}, enc σ = c := by
  rw [← hw] at hc
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨wordPerm gens w, wordPerm_mem gens w, enc_wordPerm hn hgc he w⟩

theorem mem_closure_iff (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc codes : List ℕ} {e : ℕ}
    {words : List (List ℕ)} (hgc : gens.map enc = gc) (he : enc (1 : Perm (Fin n)) = e)
    (hinv : ∀ g ∈ gens, g * g = 1) (hcl : closedB n codes gc = true)
    (hw : words.map (wordCode n e gc) = codes) (hone : e ∈ codes) (σ : Perm (Fin n)) :
    σ ∈ closure {x | x ∈ gens} ↔ enc σ ∈ codes := by
  refine ⟨enc_mem_of_mem_closure hn hgc hinv (he ▸ hone) hcl, fun h => ?_⟩
  obtain ⟨τ, hτ, hτσ⟩ := exists_of_mem_codes hn hgc he hw h
  rwa [← enc_injective hn hτσ]

theorem card_eq_length (hn : n ≤ 16) {H : Subgroup (Perm (Fin n))} {codes : List ℕ}
    (hH : ∀ σ, σ ∈ H ↔ enc σ ∈ codes) (hsurj : ∀ c ∈ codes, ∃ σ : Perm (Fin n), enc σ = c)
    (hnd : codes.Nodup) : Nat.card H = codes.length := by
  let f : H → {c // c ∈ codes.toFinset} := fun σ =>
    ⟨enc (σ : Perm (Fin n)), List.mem_toFinset.2 ((hH (σ : Perm (Fin n))).1 σ.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun σ τ h => Subtype.ext (enc_injective hn (congrArg Subtype.val h)), fun c => ?_⟩
    obtain ⟨σ, hσ⟩ := hsurj c (List.mem_toFinset.1 c.2)
    exact ⟨⟨σ, (hH σ).2 (hσ ▸ List.mem_toFinset.1 c.2)⟩, Subtype.ext hσ⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem card_closure (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc codes : List ℕ} {e : ℕ}
    {words : List (List ℕ)} (hgc : gens.map enc = gc) (he : enc (1 : Perm (Fin n)) = e)
    (hinv : ∀ g ∈ gens, g * g = 1) (hcl : closedB n codes gc = true)
    (hw : words.map (wordCode n e gc) = codes) (hone : e ∈ codes) (hnd : codes.Nodup) :
    Nat.card (closure {x | x ∈ gens}) = codes.length :=
  card_eq_length hn (mem_closure_iff hn hgc he hinv hcl hw hone) (fun c hc => by
    obtain ⟨σ, -, h⟩ := exists_of_mem_codes hn hgc he hw hc
    exact ⟨σ, h⟩) hnd

theorem sq_eq_one_of_codes (hn : n ≤ 16) {gens : List (Perm (Fin n))} {gc : List ℕ} {e : ℕ}
    (hgc : gens.map enc = gc) (he : enc (1 : Perm (Fin n)) = e)
    (h : (gc.all fun g => cmul n g g == e) = true) : ∀ g ∈ gens, g * g = 1 := by
  intro g hg
  rw [mul_eq_iff hn, he]
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h _ (hgc ▸ List.mem_map_of_mem hg)

@[expose] def invB (n e w : ℕ) (codes I : List ℕ) : Bool :=
  codes.all fun c => !(cmul n c c == e) || c == e || c == w || I.contains c

theorem mem_of_invB {e w : ℕ} {codes I : List ℕ} (h : invB n e w codes I = true) :
    ∀ c ∈ codes, cmul n c c = e → c ≠ e → c ≠ w → c ∈ I := by
  intro c hc h1 h2 h3
  simp only [invB, List.all_eq_true] at h
  have := h c hc
  simp only [h1, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    h2, h3, false_or, List.contains_eq_mem, decide_eq_true_eq] at this
  exact this

@[expose] def nodupB : List ℕ → Bool
  | [] => true
  | a :: L => !(L.contains a) && nodupB L

theorem nodup_of_nodupB : ∀ {L : List ℕ}, nodupB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_nodupB h.2⟩

end Closure

section Center

@[expose] def centerB (n e w : ℕ) (codes gc : List ℕ) : Bool :=
  codes.all fun c => !(gc.all fun g => cmul n c g == cmul n g c) || c == e || c == w

theorem center_of_check (hn : n ≤ 16) {R : Subgroup (Perm (Fin n))} {gens : List (Perm (Fin n))}
    {gc codes : List ℕ} {e w : ℕ} {w0 : Perm (Fin n)} (hgc : gens.map enc = gc)
    (he : enc (1 : Perm (Fin n)) = e) (hw : enc w0 = w) (hR : ∀ σ, σ ∈ R ↔ enc σ ∈ codes)
    (hgR : ∀ g ∈ gens, g ∈ R) (hcheck : centerB n e w codes gc = true) :
    ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r = 1 ∨ r = w0 := by
  intro r hr hcomm
  simp only [centerB, List.all_eq_true] at hcheck
  have h := hcheck _ ((hR r).1 hr)
  have hall : (gc.all fun g => cmul n (enc r) g == cmul n g (enc r)) = true := by
    rw [List.all_eq_true, ← hgc]
    intro c hc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
    rw [beq_iff_eq, ← commute_iff hn]
    exact hcomm g (hgR g hg)
  rw [hall] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl (enc_injective hn (h.trans he.symm))
  · exact Or.inr (enc_injective hn (h.trans hw.symm))

end Center

section Trichotomy

@[expose] def octet (n e w a b : ℕ) : List ℕ :=
  [e, w, a, cmul n w a, b, cmul n w b, cmul n a b, cmul n w (cmul n a b)]

@[expose] def triB (n w : ℕ) (Wa Wb : List ℕ) (cc : List ℕ → Bool) (O : List ℕ) : Bool :=
  Wa.any (fun t => !(O.contains t) && O.all fun x => cmul n t x == cmul n x t) ||
    Wb.any (fun g => (O.all fun x => O.contains (cmul n (cmul n g x) g)) &&
      !(cmul n g w == cmul n w g)) ||
    cc O

@[expose] def fxB (n e w : ℕ) (I Wa Wb : List ℕ) (cc : List ℕ → Bool) : Bool :=
  I.all fun a => I.all fun b =>
    !(cmul n a b == cmul n b a) || b == a || b == cmul n w a ||
      (nodupB (octet n e w a b) && triB n w Wa Wb cc (octet n e w a b))

private theorem comm_of_sq {G : Type*} [Group G] {X : Subgroup G} (hsq : ∀ x ∈ X, x * x = 1)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x :=
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hx hy))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by
      rw [inv_eq_of_mul_eq_one_right (hsq _ hx), inv_eq_of_mul_eq_one_right (hsq _ hy)]

private theorem ncard_eq {G : Type*} [Group G] {X : Subgroup G} (h : Nat.card X = 8) :
    (X : Set G).ncard = 8 := by
  rw [← Nat.card_coe_set_eq]
  exact h

theorem fx_of_check (hn : n ≤ 16) {R Nbar : Subgroup (Perm (Fin n))} {w0 : Perm (Fin n)}
    {codes I WaC WbC : List ℕ} {e w : ℕ} {Wa Wb : List (Perm (Fin n))}
    {cc : Subgroup (Perm (Fin n)) → Prop} {ccB : List ℕ → Bool}
    (he : enc (1 : Perm (Fin n)) = e) (hw : enc w0 = w) (hR : ∀ σ, σ ∈ R ↔ enc σ ∈ codes)
    (hI : ∀ c ∈ codes, cmul n c c = e → c ≠ e → c ≠ w → c ∈ I)
    (hWa : Wa.map enc = WaC) (hWaN : ∀ t ∈ Wa, t ∈ Nbar ∧ t * t = 1)
    (hWb : Wb.map enc = WbC) (hWbN : ∀ g ∈ Wb, g ∈ Nbar ∧ g * g = 1)
    (hcc : ∀ X : Subgroup (Perm (Fin n)), ∀ O : List ℕ, (∀ x, x ∈ X ↔ enc x ∈ O) →
      ccB O = true → cc X)
    (hcheck : fxB n e w I WaC WbC ccB = true) :
    ∀ X : Subgroup (Perm (Fin n)), X ≤ R → w0 ∈ X → Nat.card X = 8 → (∀ x ∈ X, x * x = 1) →
      (∃ t ∈ Nbar, t * t = 1 ∧ t ∉ X ∧ ∀ x ∈ X, t * x = x * t) ∨
      (∃ g ∈ Nbar, (∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧ g * w0 ≠ w0 * g) ∨ cc X := by
  intro X hXR hwX hcard hsq
  have hinj := enc_injective hn
  have hfin := ncard_eq hcard
  obtain ⟨a, haX, ha1, haw⟩ : ∃ a ∈ X, a ≠ 1 ∧ a ≠ w0 := by
    by_contra h
    push Not at h
    have hsub : (X : Set (Perm (Fin n))) ⊆ (({1, w0} : Finset (Perm (Fin n))) : Set _) := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · simp [h x hx h1]
    have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [hfin, Set.ncard_coe_finset] at h2
    have := Finset.card_le_two (a := (1 : Perm (Fin n))) (b := w0)
    omega
  obtain ⟨b, hbX, hb1, hbw, hba, hbwa⟩ : ∃ b ∈ X, b ≠ 1 ∧ b ≠ w0 ∧ b ≠ a ∧ b ≠ w0 * a := by
    by_contra h
    push Not at h
    have hsub : (X : Set (Perm (Fin n))) ⊆
        (({1, w0, a, w0 * a} : Finset (Perm (Fin n))) : Set _) := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      by_cases h2 : x = w0
      · simp [h2]
      by_cases h3 : x = a
      · simp [h3]
      · simp [h x hx h1 h2 h3]
    have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [hfin, Set.ncard_coe_finset] at h2
    have := Finset.card_le_four (a := (1 : Perm (Fin n))) (b := w0) (c := a) (d := w0 * a)
    omega
  have hmemI : ∀ x ∈ X, x ≠ 1 → x ≠ w0 → enc x ∈ I := by
    intro x hx hx1 hxw
    refine hI _ ((hR x).1 (hXR hx)) ?_ (fun h => hx1 (hinj (h.trans he.symm)))
      (fun h => hxw (hinj (h.trans hw.symm)))
    rw [← enc_mul hn, hsq x hx, he]
  simp only [fxB, List.all_eq_true] at hcheck
  have hab := hcheck _ (hmemI a haX ha1 haw) _ (hmemI b hbX hb1 hbw)
  have hc1 : (cmul n (enc a) (enc b) == cmul n (enc b) (enc a)) = true := by
    rw [beq_iff_eq, ← commute_iff hn]
    exact comm_of_sq hsq haX hbX
  have hc2 : (enc b == enc a) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hba (hinj h)
  have hc3 : (enc b == cmul n w (enc a)) = false := by
    rw [beq_eq_false_iff_ne, ← hw, ← enc_mul hn]
    exact fun h => hbwa (hinj h)
  rw [hc1, hc2, hc3] at hab
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hab
  obtain ⟨hnd, htri⟩ := hab
  set S : List (Perm (Fin n)) := [1, w0, a, w0 * a, b, w0 * b, a * b, w0 * (a * b)] with hSdef
  have hS : S.map enc = octet n e w (enc a) (enc b) := by
    simp [hSdef, octet, enc_mul hn, he, hw]
  have hSnd : S.Nodup := List.Nodup.of_map enc (hS ▸ nodup_of_nodupB hnd)
  have hSX : ∀ s ∈ S, s ∈ X := by
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false]
    rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hwX
    · exact haX
    · exact mul_mem hwX haX
    · exact hbX
    · exact mul_mem hwX hbX
    · exact mul_mem haX hbX
    · exact mul_mem hwX (mul_mem haX hbX)
  have hXS : ∀ x ∈ X, x ∈ S := by
    have hsub : ((S.toFinset : Finset (Perm (Fin n))) : Set (Perm (Fin n))) ⊆ X :=
      fun s hs => hSX s (List.mem_toFinset.1 hs)
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [hfin, Set.ncard_coe_finset, List.toFinset_card_of_nodup hSnd]; rfl)
      (Set.toFinite _)
    intro x hx
    have hx' : x ∈ ((S.toFinset : Finset (Perm (Fin n))) : Set (Perm (Fin n))) := by
      rw [heq]
      exact hx
    exact List.mem_toFinset.1 hx'
  have hmemO : ∀ x, x ∈ X ↔ enc x ∈ octet n e w (enc a) (enc b) := by
    intro x
    rw [← hS, List.mem_map]
    constructor
    · intro hx
      exact ⟨x, hXS x hx, rfl⟩
    · rintro ⟨s, hs, hse⟩
      rw [← hinj hse]
      exact hSX s hs
  simp only [triB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not, List.all_eq_true, beq_iff_eq,
    beq_eq_false_iff_ne, decide_eq_true_eq] at htri
  rcases htri with (⟨t', ht', hnot, hall⟩ | ⟨g', hg', hall, hne⟩) | hccO
  · left
    rw [← hWa] at ht'
    obtain ⟨t, htWa, rfl⟩ := List.mem_map.1 ht'
    obtain ⟨htN, htt⟩ := hWaN t htWa
    refine ⟨t, htN, htt, fun htX => hnot ((hmemO t).1 htX), fun x hx => ?_⟩
    rw [commute_iff hn]
    exact hall (enc x) ((hmemO x).1 hx)
  · right
    left
    rw [← hWb] at hg'
    obtain ⟨g, hgWb, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨hgN, hgg⟩ := hWbN g hgWb
    refine ⟨g, hgN, fun x hx => ?_, fun h => ?_⟩
    · rw [inv_eq_of_mul_eq_one_right hgg, hmemO, enc_mul hn, enc_mul hn]
      exact hall (enc x) ((hmemO x).1 hx)
    · rw [← hw] at hne
      exact hne ((commute_iff hn).1 h)
  · right
    right
    exact hcc X _ hmemO hccO

end Trichotomy

end CFSG.OddStandard.AltStdSmall4.Fus.FinCode
