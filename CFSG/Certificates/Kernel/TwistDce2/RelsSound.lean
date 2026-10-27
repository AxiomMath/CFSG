module

public import Certificates.Data.Kernel.TwistDce2.Rels
public import CFSG.Certificates.Kernel.TwistDce.Words
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Bound.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Certificates.TwDce2.Rels

open CFSG.KC.TwDce2 CFSG.KC.TwDce CFSG.Certificates.TwDce.Words CFSG.KC.YModel

private theorem fld15' (x j : ℕ) : fld x (4 * j) 15 = x / 16 ^ j % 16 := by
  unfold fld
  show (x >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

private theorem lst_eq' (w : ℕ) :
    lst w = (List.range (wLen w)).map (fun i => wStr w / 16 ^ i % 16) := by
  unfold lst
  exact List.map_congr_left fun i _ => fld15' (wStr w) i

private theorem digs_succ' (s n : ℕ) : (List.range (n + 1)).map (fun i => s / 16 ^ i % 16) =
    s % 16 :: (List.range n).map (fun i => (s / 16) / 16 ^ i % 16) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    show s / 16 ^ (i + 1) % 16 = _
    rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

private theorem land15' (s : ℕ) : Nat.land s 15 = s % 16 := by
  show s &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem shr4' (s : ℕ) : Nat.shiftRight s 4 = s / 16 := by
  rw [show Nat.shiftRight s 4 = s >>> 4 from rfl, Nat.shiftRight_eq_div_pow]

private theorem evP_loop' (F : ℕ → ℕ) : ∀ (n s x : ℕ),
    (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ x => x)
      (fun _ ih s x => sN (fieldAt 11 (F (Nat.land s 15)) x) (fun y =>
        sN (Nat.shiftRight s 4) (fun s' => ih s' y))) n) s x =
    ((List.range n).map (fun i => s / 16 ^ i % 16)).foldl
      (fun p c => fieldAt 11 (F c) p) x := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    intro s x
    rw [digs_succ', List.foldl_cons]
    simp only [Nat.rec_add_one, sN_eq] at ih ⊢
    rw [ih, land15', shr4']

theorem evP_eq (F : ℕ → ℕ) (w x : ℕ) :
    CFSG.KC.TwDce2.evP F w x = (lst w).foldl (fun p c => fieldAt 11 (F c) p) x := by
  rw [lst_eq']
  exact evP_loop' F (wLen w) (wStr w) x

private theorem wMk_zero : wMk 0 0 = 0 := by
  unfold wMk
  show (0 : ℕ) ||| (0 <<< 32) = 0
  simp

theorem codesW_spec : ∀ w : List ℕ, (∀ c ∈ w, c < 16) → w.length < 2 ^ 32 →
    wLen (codesW w) = w.length ∧ wOK (codesW w) = true ∧ lst (codesW w) = w
  | [], _, _ => by
    have h0 : codesW [] = 0 := wMk_zero
    rw [h0, ← length_lst, lst_zero]
    exact ⟨rfl, wOK_zero, rfl⟩
  | c :: w, hc, hl => by
    have hl' : w.length < 2 ^ 32 := by simp only [List.length_cons] at hl; omega
    obtain ⟨i1, i2, i3⟩ := codesW_spec w (fun d hd => hc d (List.mem_cons_of_mem _ hd)) hl'
    obtain ⟨o1, o2, o3⟩ := wOne_spec (hc c List.mem_cons_self)
    have e : codesW (c :: w) = wCat (wOne c) (codesW w) := sN_eq _ _
    obtain ⟨c1, c2, c3⟩ := wCat_spec o2 i2 (by rw [o1, i1]; simp only [List.length_cons] at hl; omega)
    rw [e]
    refine ⟨by rw [c1, o1, i1, List.length_cons]; omega, c2, by rw [c3, o3, i3]; rfl⟩

private theorem natRec_and {P : ℕ → Bool} : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc (P c)) n) = true →
    ∀ c < n, P c = true := by
  intro n
  induction n with
  | zero => intro _ c hc; exact absurd hc (Nat.not_lt_zero _)
  | succ n ih =>
    intro h c hc
    change andB _ (P n) = true at h
    rw [andB_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact ih h.1 c hc
    · exact h.2

theorem fixAll_sound {F : ℕ → ℕ} {NP v : ℕ} (h : fixAll F NP v = true) :
    ∀ x < NP, CFSG.KC.TwDce2.evP F v x = x := fun x hx =>
  Nat.eq_of_beq_eq_true (natRec_and (P := fun x => Nat.beq (CFSG.KC.TwDce2.evP F v x) x) NP h x hx)

theorem codesOK_sound : ∀ {w : List ℕ}, codesOK w = true → ∀ c ∈ w, c < 12
  | [], _ => fun _ hc => absurd hc List.not_mem_nil
  | c :: w, h => by
    change andB (Nat.blt c 12) (codesOK w) = true at h
    rw [andB_iff, Nat.blt_eq] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact codesOK_sound h.2 d hd

theorem relsOK_sound {F : ℕ → ℕ} {NP : ℕ} : ∀ {ws : List (List ℕ)}, relsOK F NP ws = true →
    (∀ w ∈ ws, w.length < 2 ^ 32) →
    ∀ w ∈ ws, (∀ c ∈ w, c < 12) ∧ ∀ p < NP, w.foldl (fun q c => fieldAt 11 (F c) q) p = p
  | [], _, _ => fun _ hw => absurd hw List.not_mem_nil
  | w :: ws, h, hl => by
    change andB (andB (codesOK w) (CFSG.KC.TwDce.sB (codesW w) (fun v => fixAll F NP v)))
      (relsOK F NP ws) = true at h
    rw [andB_iff, andB_iff, sB_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · have hc := codesOK_sound h1
      obtain ⟨-, -, hlst⟩ := codesW_spec v (fun c hc' => by have := hc c hc'; omega)
        (hl v List.mem_cons_self)
      refine ⟨hc, fun p hp => ?_⟩
      have := fixAll_sound h2 p hp
      rwa [evP_eq, hlst] at this
    · exact relsOK_sound h3 (fun u hu => hl u (List.mem_cons_of_mem _ hu)) v hv

theorem fixesPt_sound {F : ℕ → ℕ} {INVM : ℕ} {RW : ℕ → ℕ} {p : ℕ} : ∀ {L : List ℕ},
    fixesPt F INVM RW L p = true → ∀ c ∈ L, CFSG.KC.TwDce2.evP F (gWord INVM RW c) p = p
  | [], _ => fun _ hc => absurd hc List.not_mem_nil
  | c :: L, h => by
    change andB (Nat.beq (CFSG.KC.TwDce2.evP F (gWord INVM RW c) p) p)
      (fixesPt F INVM RW L p) = true at h
    rw [andB_iff] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Nat.eq_of_beq_eq_true h.1
    · exact fixesPt_sound h.2 d hd

theorem invCodesOK_sound {INVM m : ℕ} (h : invCodesOK INVM m = true) :
    ∀ i < m, ivL INVM (2 * i) = 2 * i + 1 := by
  intro i hi
  have := natRec_and (P := fun j => Nat.beq (ivL INVM (Nat.mul 2 (Nat.add 0 j)))
    (Nat.add (Nat.mul 2 (Nat.add 0 j)) 1)) m h i hi
  have e : Nat.add 0 i = i := Nat.zero_add i
  rw [e] at this
  exact Nat.eq_of_beq_eq_true this

theorem lettersOK_sound {F : ℕ → ℕ} {INVM NP : ℕ} (h : lettersOK F INVM NP = true) :
    ∀ c < 12, ivL INVM c < 12 ∧ ∀ x < NP, fieldAt 11 (F c) x < NP ∧
      fieldAt 11 (F (ivL INVM c)) (fieldAt 11 (F c) x) = x := by
  intro c hc
  have h1 := natRec_and (P := fun c => andB (Nat.blt (ivL INVM c) 12)
    (Nat.rec (motive := fun _ => Bool) true
      (fun x acc2 => andB acc2 (CFSG.KC.TwDce.sB (ptL F c x) (fun y =>
        andB (Nat.blt y NP) (Nat.beq (ptL F (ivL INVM c) y) x)))) NP)) 12 h c hc
  rw [andB_iff, Nat.blt_eq] at h1
  refine ⟨h1.1, fun x hx => ?_⟩
  have h2 := natRec_and (P := fun x => CFSG.KC.TwDce.sB (ptL F c x) (fun y =>
    andB (Nat.blt y NP) (Nat.beq (ptL F (ivL INVM c) y) x))) NP h1.2 x hx
  rw [sB_eq, andB_iff, Nat.blt_eq] at h2
  exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩

variable {F : ℕ → ℕ} {INVM NP : ℕ}

@[expose] noncomputable def tablePerm (hL : lettersOK F INVM NP = true) (c : ℕ) (hc : c < 12) :
    Equiv.Perm (Fin NP) where
  toFun p := ⟨fieldAt 11 (F c) p, ((lettersOK_sound hL c hc).2 p p.2).1⟩
  invFun p := ⟨fieldAt 11 (F (ivL INVM c)) p,
    ((lettersOK_sound hL _ (lettersOK_sound hL c hc).1).2 p p.2).1⟩
  left_inv p := Fin.ext ((lettersOK_sound hL c hc).2 p p.2).2
  right_inv q := by
    have hinj : Function.Injective (fun p : Fin NP =>
        (⟨fieldAt 11 (F c) p, ((lettersOK_sound hL c hc).2 p p.2).1⟩ : Fin NP)) := by
      intro p p' e
      have e' := congrArg (fun r : Fin NP => fieldAt 11 (F (ivL INVM c)) r.val) e
      simp only at e'
      rw [((lettersOK_sound hL c hc).2 p p.2).2, ((lettersOK_sound hL c hc).2 p' p'.2).2] at e'
      exact Fin.ext e'
    obtain ⟨p, rfl⟩ := Finite.injective_iff_surjective.1 hinj q
    exact Fin.ext (congrArg (fieldAt 11 (F c)) ((lettersOK_sound hL c hc).2 p p.2).2)

@[expose] noncomputable def tableGen (hL : lettersOK F INVM NP = true) (j : ℕ) :
    (Equiv.Perm (Fin NP))ᵐᵒᵖ :=
  if h : 2 * j < 12 then MulOpposite.op (tablePerm hL (2 * j) h) else 1

@[expose] noncomputable def tableHom (hL : lettersOK F INVM NP = true) (m : ℕ) :
    FreeGroup (Fin m) →* (Equiv.Perm (Fin NP))ᵐᵒᵖ :=
  FreeGroup.lift fun j => tableGen hL j.val

@[expose] def letterCode {m : ℕ} (l : Fin m × Bool) : ℕ :=
  bif l.2 then 2 * l.1.val else 2 * l.1.val + 1

theorem tableGen_apply (hL : lettersOK F INVM NP = true) {j : ℕ} (hj : j < 6) (p : Fin NP) :
    ((tableGen hL j).unop p).val = fieldAt 11 (F (2 * j)) p.val := by
  rw [tableGen, dif_pos (by omega)]
  rfl

theorem tableGen_inv_apply (hL : lettersOK F INVM NP = true) (hI : invCodesOK INVM 6 = true)
    {j : ℕ} (hj : j < 6) (p : Fin NP) :
    ((tableGen hL j)⁻¹.unop p).val = fieldAt 11 (F (2 * j + 1)) p.val := by
  rw [tableGen, dif_pos (by omega), MulOpposite.unop_inv, MulOpposite.unop_op,
    Equiv.Perm.inv_def, ← invCodesOK_sound hI j hj]
  rfl

theorem tableHom_mk_apply (hL : lettersOK F INVM NP = true) (hI : invCodesOK INVM 6 = true)
    {m : ℕ} : ∀ (u : List (Fin m × Bool)), (∀ l ∈ u, l.1.val < 6) → ∀ p : Fin NP,
    ((tableHom hL m (FreeGroup.mk u)).unop p).val =
      (u.map letterCode).foldl (fun q c => fieldAt 11 (F c) q) p.val
  | [], _, p => rfl
  | l :: u, hu, p => by
    rw [← List.singleton_append, ← FreeGroup.mul_mk, map_mul, MulOpposite.unop_mul,
      Equiv.Perm.mul_apply, tableHom_mk_apply hL hI u (fun l' hl' => hu l' (by simp [hl'])),
      List.singleton_append, List.map_cons, List.foldl_cons]
    congr 1
    have hl := hu l List.mem_cons_self
    rw [tableHom, FreeGroup.lift_mk]
    rcases l with ⟨j, _ | _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, cond_false]
      rw [tableGen_inv_apply hL hI hl]
      rfl
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, cond_true]
      rw [tableGen_apply hL hl]
      rfl

theorem tableHom_mk_eq_one (hL : lettersOK F INVM NP = true) (hI : invCodesOK INVM 6 = true)
    {m : ℕ} {u : List (Fin m × Bool)} (hu : ∀ l ∈ u, l.1.val < 6)
    (hfix : ∀ p < NP, (u.map letterCode).foldl (fun q c => fieldAt 11 (F c) q) p = p) :
    tableHom hL m (FreeGroup.mk u) = 1 := by
  apply MulOpposite.unop_injective
  ext p
  rw [tableHom_mk_apply hL hI u hu, hfix p p.2]
  rfl

end CFSG.Certificates.TwDce2.Rels

end
