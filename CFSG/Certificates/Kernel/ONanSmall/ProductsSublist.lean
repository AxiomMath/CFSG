module

public import CFSG.Certificates.Kernel.ONanSmall.PickRunSound
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod

public section

namespace CFSG.KC.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M]

theorem eq_filter_append_of_pairwise {α : Type*} (R : α → α → Prop) (p : α → Bool)
    (hR : ∀ a b, p a = false → p b = true → ¬ R a b) :
    ∀ l : List α, l.Pairwise R → l = l.filter p ++ l.filter (fun a => !p a)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha]), List.cons_append,
        ← eq_filter_append_of_pairwise R p hR l h.2]
    · have hall : ∀ b ∈ a :: l, p b = false := by
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · simpa using ha
        · by_contra hb'
          exact hR a b (by simpa using ha) (by simpa using hb') (h.1 b hb)
      rw [List.filter_eq_nil_iff.2 (fun b hb => by simp [hall b hb]), List.nil_append,
        List.filter_eq_self.2 (fun b hb => by simp [hall b hb])]

theorem genP_cons_zero (t : M) (T : List M) (Ts : List (List M)) (d : List ℕ) :
    genP ((t :: T) :: Ts) (0 :: d) = (genP Ts d).map (t * ·) := by
  rw [genP, List.getElem?_cons_zero]
  cases genP Ts d <;> rfl

theorem genP_cons_succ (t : M) (T : List M) (Ts : List (List M)) (i : ℕ) (d : List ℕ) :
    genP ((t :: T) :: Ts) ((i + 1) :: d) = genP (T :: Ts) (i :: d) := by
  rw [genP, genP, List.getElem?_cons_succ]

theorem productsOf_cons_cons (t : M) (T : List M) (Ts : List (List M)) :
    productsOf ((t :: T) :: Ts) = (productsOf Ts).map (t * ·) ++ productsOf (T :: Ts) := by
  simp only [productsOf, List.flatMap_cons]

@[expose] def wordShift : List ℕ → List ℕ
  | (i + 1) :: d => i :: d
  | w => w

@[expose] def wordUnshift : List ℕ → List ℕ
  | i :: d => (i + 1) :: d
  | [] => []

theorem sublist_productsOf_level (Ts : List (List M))
    (ih : ∀ ws : List (List ℕ), ws.Pairwise (List.Lex (· < ·)) →
      (∀ w ∈ ws, (genP Ts w).isSome) → (ws.filterMap (genP Ts)).Sublist (productsOf Ts)) :
    ∀ (T : List M) (ws : List (List ℕ)), ws.Pairwise (List.Lex (· < ·)) →
      (∀ w ∈ ws, (genP (T :: Ts) w).isSome) →
      (ws.filterMap (genP (T :: Ts))).Sublist (productsOf (T :: Ts))
  | [], ws, _, hv => by
    have hws : ws = [] := List.eq_nil_iff_forall_not_mem.2 fun w hw => by
      have h := hv w hw
      match w with
      | [] => simp [genP] at h
      | _ :: _ => simp [genP] at h
    subst hws
    exact List.nil_sublist _
  | t :: T, ws, hs, hv => by
    let p : List ℕ → Bool := fun w => w.head?.getD 0 == 0
    have hR : ∀ a b, p a = false → p b = true → ¬ List.Lex (· < ·) a b := by
      intro a b ha hb hab
      match a, b, ha, hb, hab with
      | 0 :: _, _, ha, _, _ => simp [p] at ha
      | (i + 1) :: _, [], _, _, hab => cases hab
      | (i + 1) :: _, 0 :: _, _, _, hab =>
        cases hab with
        | rel h => omega
      | (i + 1) :: _, (j + 1) :: _, _, hb, _ => simp [p] at hb
    rw [eq_filter_append_of_pairwise _ p hR ws hs, List.filterMap_append, productsOf_cons_cons]
    refine List.Sublist.append ?_ ?_
    ·
      have hform : ∀ w ∈ ws.filter p, w = 0 :: w.tail := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
        match w, hw2, hv w hw1 with
        | [], _, h => simp [genP] at h
        | a :: d, hw2, _ => simp only [p, List.head?_cons, Option.getD_some, beq_iff_eq] at hw2; simp [hw2]
      have e : ws.filter p = ((ws.filter p).map List.tail).map (0 :: ·) := by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id (ws.filter p)]
        exact List.map_congr_left fun w hw => hform w hw
      have hf : genP ((t :: T) :: Ts) ∘ (0 :: ·) = fun d => (genP Ts d).map (t * ·) :=
        funext fun d => genP_cons_zero t T Ts d
      have hpw : (((ws.filter p).map List.tail).map (0 :: ·)).Pairwise (List.Lex (· < ·)) := by
        rw [← e]
        exact hs.filter p
      rw [e, List.filterMap_map, hf, ← List.map_filterMap]
      refine (ih _ ?_ ?_).map _
      · rw [List.pairwise_map] at hpw
        refine hpw.imp fun h => ?_
        cases h with
        | cons h => exact h
        | rel h => omega
      · intro d hd
        have h0 : 0 :: d ∈ ws.filter p := by
          rw [e]
          exact List.mem_map.2 ⟨d, hd, rfl⟩
        have h := hv _ (List.mem_filter.1 h0).1
        rw [genP_cons_zero, Option.isSome_map] at h
        exact h
    ·
      have hform : ∀ w ∈ ws.filter (fun a => !p a), wordUnshift (wordShift w) = w := by
        intro w hw
        obtain ⟨_, hw2⟩ := List.mem_filter.1 hw
        match w, hw2 with
        | [], hw2 => simp [p] at hw2
        | 0 :: _, hw2 => simp [p] at hw2
        | (i + 1) :: d, _ => rfl
      have e : ws.filter (fun a => !p a) =
          ((ws.filter (fun a => !p a)).map wordShift).map wordUnshift := by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id (ws.filter (fun a => !p a))]
        exact List.map_congr_left fun w hw => (hform w hw).symm
      have hf : genP ((t :: T) :: Ts) ∘ wordUnshift = genP (T :: Ts) := by
        funext w
        match w with
        | [] => simp [wordUnshift, genP]
        | i :: d => exact genP_cons_succ t T Ts i d
      rw [e, List.filterMap_map, hf]
      refine sublist_productsOf_level Ts ih T _ ?_ ?_
      · rw [List.pairwise_map]
        refine (hs.filter _).imp_of_mem fun {a b} ha hb h => ?_
        obtain ⟨_, ha2⟩ := List.mem_filter.1 ha
        obtain ⟨_, hb2⟩ := List.mem_filter.1 hb
        match a, b, ha2, hb2, h with
        | [], _, ha2, _, _ => simp [p] at ha2
        | 0 :: _, _, ha2, _, _ => simp [p] at ha2
        | _ :: _, [], _, hb2, _ => simp [p] at hb2
        | _ :: _, 0 :: _, _, hb2, _ => simp [p] at hb2
        | (i + 1) :: _, (j + 1) :: _, _, _, h =>
          cases h with
          | cons h => exact List.Lex.cons h
          | rel h => exact List.Lex.rel (by omega)
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
        have h := hv u (List.mem_filter.1 hu).1
        rw [← hform u hu, ← Function.comp_apply (f := genP ((t :: T) :: Ts)), hf] at h
        exact h

theorem sublist_productsOf : ∀ (Ts : List (List M)) (ws : List (List ℕ)),
    ws.Pairwise (List.Lex (· < ·)) → (∀ w ∈ ws, (genP Ts w).isSome) →
    (ws.filterMap (genP Ts)).Sublist (productsOf Ts)
  | [], ws, hs, hv => by
    have hw : ∀ w ∈ ws, w = [] := fun w hw => by
      have h := hv w hw
      match w with
      | [] => rfl
      | _ :: _ => simp [genP] at h
    match ws, hs with
    | [], _ => exact List.nil_sublist _
    | [a], _ =>
      rw [hw a (by simp)]
      simp [genP, productsOf]
    | a :: b :: _, hs =>
      exfalso
      have h := List.rel_of_pairwise_cons hs (List.mem_cons_self ..)
      rw [hw a (by simp), hw b (by simp)] at h
      cases h
  | T :: Ts, ws, hs, hv => sublist_productsOf_level Ts (sublist_productsOf Ts) T ws hs hv

section Count

variable [DecidableEq M]

theorem length_mul_centB_le (L Cl : List M) (r : M) (hL : L.Nodup) (hCl : Cl.Nodup)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hconj : ∀ c ∈ Cl, ∃ g ∈ L, g * c * g⁻¹ = r) :
    Cl.length * (centB L r).length ≤ L.length := by
  choose! f hfL hfc using hconj
  have hcN : (centB L r).Nodup := hL.filter _
  rw [← List.toFinset_card_of_nodup hCl, ← List.toFinset_card_of_nodup hcN,
    ← List.toFinset_card_of_nodup hL, ← Finset.card_product]
  have key : ∀ c ∈ Cl, ∀ x ∈ centB L r, (x * f c)⁻¹ * r * (x * f c) = c := by
    intro c hc x hx
    have hx' : x * r = r * x := of_decide_eq_true (List.mem_filter.1 hx).2
    have hxr : x⁻¹ * r * x = r := by rw [mul_assoc, ← hx', inv_mul_cancel_left]
    calc (x * f c)⁻¹ * r * (x * f c) = (f c)⁻¹ * (x⁻¹ * r * x) * f c := by
          simp only [mul_inv_rev, mul_assoc]
      _ = (f c)⁻¹ * (f c * c * (f c)⁻¹) * f c := by rw [hxr, hfc c hc]
      _ = c := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine Finset.card_le_card_of_injOn (fun p => p.2 * f p.1) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, List.mem_toFinset, List.mem_toFinset] at hp
    rw [Finset.mem_coe, List.mem_toFinset]
    exact hmul _ (List.mem_filter.1 hp.2).1 _ (hfL _ hp.1)
  · intro p hp q hq h
    rw [Finset.mem_coe, Finset.mem_product, List.mem_toFinset, List.mem_toFinset] at hp hq
    have h'' : p.2 * f p.1 = q.2 * f q.1 := h
    have h1 : p.1 = q.1 := by
      rw [← key p.1 hp.1 p.2 hp.2, ← key q.1 hq.1 q.2 hq.2, h'']
    rw [h1] at h''
    exact Prod.ext h1 (mul_right_cancel h'')

theorem centB_eq_of_length (L Cl Cr : List M) (r : M) (hL : L.Nodup) (hCl : Cl.Nodup)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hconj : ∀ c ∈ Cl, ∃ g ∈ L, g * c * g⁻¹ = r)
    (hsub : Cr.Sublist L) (hcomm : ∀ x ∈ Cr, x * r = r * x)
    (hcard : L.length ≤ Cl.length * Cr.length) (hpos : 0 < Cl.length) : centB L r = Cr := by
  have hs : Cr.Sublist (centB L r) := by
    have h := hsub.filter (fun c => decide (c * r = r * c))
    rwa [List.filter_eq_self.2 (fun x hx => decide_eq_true (hcomm x hx))] at h
  refine (hs.eq_of_length_le ?_).symm
  exact Nat.le_of_mul_le_mul_left
    ((length_mul_centB_le L Cl r hL hCl hmul hconj).trans hcard) hpos

end Count

end CFSG.KC.ONanSmall
