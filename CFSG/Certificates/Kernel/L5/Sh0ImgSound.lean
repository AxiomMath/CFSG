module

public import Certificates.Data.Kernel.L5.Sh0Img

public section

namespace CFSG.Certificates.Kernel.L5S

theorem sh0I_all_congr {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem sh0I_any_congr {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem pk7_cons (v : Nat) (l : List Nat) : pk7 (v :: l) = v + 128 * pk7 l := rfl

theorem pk7_read {l : List Nat} (h : ∀ v ∈ l, v < 128) (g : Nat) :
    (pk7 l >>> (7 * g)) % 128 = l.getD g 0 := by
  induction l generalizing g with
  | nil =>
    have e : pk7 [] = 0 := rfl
    rw [e, Nat.zero_shiftRight, List.getD_nil]
  | cons v l ih =>
    have hv : v < 128 := h v List.mem_cons_self
    have ih' := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [pk7_cons]
    cases g with
    | zero =>
      rw [Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
      omega
    | succ g =>
      have e : 7 * (g + 1) = 7 + 7 * g := by omega
      have e2 : (v + 128 * pk7 l) >>> 7 = pk7 l := by
        rw [Nat.shiftRight_eq_div_pow]
        omega
      rw [e, Nat.shiftRight_add, e2, ih', List.getD_cons_succ]

theorem shr64 (s L : Nat) : (s % 18446744073709551616 + 18446744073709551616 * L) >>> 64 = L := by
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem rdI_eq (P g : Nat) : rdI P g = (P >>> (64 + 7 * g)) % 128 :=
  Nat.and_two_pow_sub_one_eq_mod _ 7

theorem sel3_eq (x0 x1 x2 k : Nat) : sel3 x0 x1 x2 k = [x0, x1, x2].getD k 0 := by
  rcases k with _ | _ | _ | k <;> rfl

theorem evX_eq (t : Nat → Nat) (x0 x1 x2 : Nat) (w : List Nat) (a : Nat) :
    evX t x0 x1 x2 w a = evFromT t [x0, x1, x2] a w := by
  induction w generalizing a with
  | nil => rfl
  | cons k w ih =>
    have e : evX t x0 x1 x2 (k :: w) a = evX t x0 x1 x2 w (t (a * 128 + sel3 x0 x1 x2 k)) := rfl
    have e2 : evFromT t [x0, x1, x2] a (k :: w) =
        evFromT t [x0, x1, x2] (t (a * 128 + [x0, x1, x2].getD k 0)) w := rfl
    rw [e, e2, ih, sel3_eq]

theorem imgP_eq (t : Nat → Nat) (x0 x1 x2 : Nat) (WL : List (List Nat)) :
    imgP t x0 x1 x2 WL = pk7 [x0, x1, x2] * 2654435761 % 18446744073709551616 +
      18446744073709551616 * pk7 (WL.map fun w => evFromT t [x0, x1, x2] 0 w) := by
  have e : ∀ L : List (List Nat), @List.rec (List Nat) (fun _ => Nat) 0
      (fun w _ acc => Nat.add (evX t x0 x1 x2 w 0) (Nat.mul 128 acc)) L =
      pk7 (L.map fun w => evFromT t [x0, x1, x2] 0 w) := by
    intro L
    induction L with
    | nil => rfl
    | cons w L ih =>
      rw [List.map_cons, pk7_cons, ← ih, ← evX_eq]
      rfl
  unfold imgP
  rw [e]
  rfl

theorem getD3_lt {a b c : Nat} (ha : a < 128) (hb : b < 128) (hc : c < 128) (k : Nat) :
    [a, b, c].getD k 0 < 128 := by
  rcases k with _ | _ | _ | k <;> simp [ha, hb, hc]

theorem evFromT_snoc (t : Nat → Nat) (x w : List Nat) (a k : Nat) :
    evFromT t x a (w ++ [k]) = t (evFromT t x a w * 128 + x.getD k 0) := by
  unfold evFromT
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem relsUT_all (t : Nat → Nat) (gs : List Nat) (W : Nat → List Nat) (x : List Nat) :
    (relsUT t gs W).all (fun r => decide (evFromT t x 0 r.1 = evFromT t x 0 r.2)) =
      (List.range 128).all fun g => (List.range 3).all fun k =>
        decide (evFromT t x 0 (W g ++ [k]) = evFromT t x 0 (W (t (g * 128 + gs.getD k 0)))) := by
  unfold relsUT
  rw [List.all_flatMap]
  refine congrArg (List.all (List.range 128)) (funext fun g => ?_)
  rw [List.all_filterMap]
  refine congrArg (List.all (List.range 3)) (funext fun k => ?_)
  by_cases h : (W g ++ [k] == W (t (g * 128 + gs.getD k 0))) = true
  · rw [if_pos h, beq_iff_eq.mp h]
    simp
  · rw [if_neg h]

section

variable {t : Nat → Nat} (hb : ∀ n, t n < 128)
include hb

theorem evFromT_lt (x : List Nat) (w : List Nat) {a : Nat} (ha : a < 128) :
    evFromT t x a w < 128 := by
  induction w generalizing a with
  | nil => exact ha
  | cons k w ih =>
    have e : evFromT t x a (k :: w) = evFromT t x (t (a * 128 + x.getD k 0)) w := rfl
    rw [e]
    exact ih (hb _)

theorem rdI_imgP (x0 x1 x2 : Nat) {WL : List (List Nat)} {g : Nat} (hg : g < WL.length) :
    rdI (imgP t x0 x1 x2 WL) g = evFromT t [x0, x1, x2] 0 (WL.getD g []) := by
  rw [rdI_eq, imgP_eq, Nat.shiftRight_add, shr64, pk7_read]
  · simp [List.getD_eq_getElem?_getD, hg]
  · intro v hv
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv
    exact evFromT_lt hb _ _ (by omega)

variable {WL : List (List Nat)} (hW : WL.length = 128)
include hW

theorem relI_imgP (gs : List Nat) (x0 x1 x2 : Nat) :
    relI t gs [x0, x1, x2] (imgP t x0 x1 x2 WL) =
      (relsUT t gs fun i => WL.getD i []).all
        (fun r => decide (evFromT t [x0, x1, x2] 0 r.1 = evFromT t [x0, x1, x2] 0 r.2)) := by
  rw [relsUT_all]
  unfold relI
  refine sh0I_all_congr fun g hg => sh0I_all_congr fun k _ => ?_
  have hg' : g < WL.length := by rw [hW]; exact List.mem_range.1 hg
  have hp : t (g * 128 + gs.getD k 0) < WL.length := by rw [hW]; exact hb _
  rw [rdI_imgP hb x0 x1 x2 hg', rdI_imgP hb x0 x1 x2 hp, evFromT_snoc, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_eq]

theorem triI_imgP (iv : Nat → Nat) (gs ridx : List Nat) (xs : List (List Nat)) (ss : List Nat)
    {x0 x1 x2 : Nat} (hx : ∀ k, [x0, x1, x2].getD k 0 < 128) (hr : ∀ r ∈ ridx, r < 128) :
    triI t iv gs ridx xs ss [x0, x1, x2] (imgP t x0 x1 x2 WL) =
      (!((relsUT t gs fun i => WL.getD i []).all
          fun r => decide (evFromT t [x0, x1, x2] 0 r.1 = evFromT t [x0, x1, x2] 0 r.2)) ||
        !(ridx.any fun r => !decide (evFromT t [x0, x1, x2] 0 (WL.getD r []) ∈ ridx)) ||
        (List.range 128).all fun u => !(autPairOKT t iv gs (fun i => WL.getD i []) [x0, x1, x2] u) ||
          twistOKT t iv (fun i => WL.getD i []) xs ss [x0, x1, x2] u) := by
  have hR : ∀ g, g < 128 → rdI (imgP t x0 x1 x2 WL) g = evFromT t [x0, x1, x2] 0 (WL.getD g []) :=
    fun g hg => rdI_imgP hb x0 x1 x2 (by rw [hW]; exact hg)
  unfold triI
  rw [relI_imgP hb hW]
  have hRi : (ridx.any fun r => !decide (rdI (imgP t x0 x1 x2 WL) r ∈ ridx)) =
      ridx.any fun r => !decide (evFromT t [x0, x1, x2] 0 (WL.getD r []) ∈ ridx) :=
    sh0I_any_congr fun r hr' => by rw [hR r (hr r hr')]
  have hU : ((List.range 128).all fun u => !(autI t iv gs [x0, x1, x2] (imgP t x0 x1 x2 WL) u) ||
      twI t iv xs ss [x0, x1, x2] (imgP t x0 x1 x2 WL) u) =
      (List.range 128).all fun u => !(autPairOKT t iv gs (fun i => WL.getD i []) [x0, x1, x2] u) ||
        twistOKT t iv (fun i => WL.getD i []) xs ss [x0, x1, x2] u := by
    refine sh0I_all_congr fun u hu => ?_
    have hk : ∀ k, rdI (imgP t x0 x1 x2 WL) ([x0, x1, x2].getD k 0) =
        evFromT t [x0, x1, x2] 0 (WL.getD ([x0, x1, x2].getD k 0) []) :=
      fun k => hR _ (hx k)
    have hA : autI t iv gs [x0, x1, x2] (imgP t x0 x1 x2 WL) u =
        autPairOKT t iv gs (fun i => WL.getD i []) [x0, x1, x2] u := by
      unfold autI autPairOKT
      simp only [hk, hR u (List.mem_range.1 hu)]
    have hT : twI t iv xs ss [x0, x1, x2] (imgP t x0 x1 x2 WL) u =
        twistOKT t iv (fun i => WL.getD i []) xs ss [x0, x1, x2] u := by
      unfold twI twistOKT
      refine sh0I_any_congr fun m _ => sh0I_any_congr fun h0 hh => ?_
      rw [hR h0 (List.mem_range.1 hh)]
    rw [hA, hT]
  rw [hRi, hU]

theorem classifyRowT_eq_I (iv : Nat → Nat) (gs : List Nat) (r0 : List Nat × List Nat)
    (ridx invl : List Nat) (z : Nat) (xs : List (List Nat)) (ss : List Nat) {x0 : Nat}
    (hx0 : x0 < 128) (hl : ∀ y ∈ invl, y < 128) (hr : ∀ r ∈ ridx, r < 128) :
    classifyRowT t iv gs (fun i => WL.getD i []) (r0 :: relsUT t gs fun i => WL.getD i []) ridx invl
      z xs ss x0 = classifyRowI t iv gs WL r0 ridx invl z xs ss x0 := by
  unfold classifyRowT classifyRowI
  refine sh0I_all_congr fun x1 h1 => sh0I_all_congr fun x2 h2 => ?_
  have hb1 : ∀ a b : Nat, Nat.beq a b = decide (a = b) := fun a b => by
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
  rw [triI_imgP hb hW iv gs ridx xs ss (getD3_lt hx0 (hl x1 h1) (hl x2 h2)) hr, List.all_cons,
    Bool.not_and, hb1, hb1, evX_eq, evX_eq, evX_eq]
  simp only [Bool.or_assoc]

end

end CFSG.Certificates.Kernel.L5S

end
