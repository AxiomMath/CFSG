module

public import CFSG.Certificates.Kernel.SporLatDc2Act
public import Certificates.Data.Kernel.SporLatDc2Check

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (labF sortedLt sumN pairF)
open MulAction

theorem isS_iff (C : Dc2Ctx) {w : List ℕ} : isS C w = true ↔ ∀ l ∈ w, l < C.ns := by
  simp [isS]

theorem isF_iff (C : Dc2Ctx) {w : List ℕ} : isF C w = true ↔ ∀ l ∈ w, l < C.nf := by
  simp [isF]

theorem isW_iff (C : Dc2Ctx) {w : List ℕ} : isW C w = true ↔ ∀ l ∈ w, l < C.nl := by
  simp [isW]

structure Dc2SoundCtx (Γ : Type) [Group Γ] [Finite Γ] (n : ℕ) [MulAction Γ (Fin n)] where
  C : Dc2Ctx
  hn : C.n = n
  D : Dc2Data
  els : List Γ
  hel : els.length = C.nl
  hL : ∀ l < C.nl, Good n (tab n (els.getD l 1)).toArray (C.L l)
  hk : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k
  hN : Nat.card Γ = C.N1 * C.N2 * 2 ^ C.k
  hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1
  h : dc2Check C D = true

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem parts : globOK P.C P.D = true ∧
    (∀ i < P.D.bo.length, borbOK P.C P.D (P.D.bo.getD i default) = true) ∧
    (∀ c < P.D.R1.length, rec1OK P.C P.D (P.D.R1.getD c default) = true) ∧
    fRestOK P.C P.D = true ∧ (∀ l < P.C.nf, fRowOK P.C P.D l = true) ∧
    (∀ c < P.D.R1.length, rec2OK P.C P.D c = true) ∧
    (∀ b < P.D.roots.length, rootsOK P.C P.D b = true) ∧ rootIdxOK P.C P.D = true := by
  have h := P.h
  simp only [dc2Check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem glob : (∀ p ∈ P.C.Λ, p < n) ∧ P.C.Λ.Pairwise (· < ·) ∧
    (∀ p ∈ P.C.Δ, p < n * n) ∧ P.C.Δ.Pairwise (· < ·) ∧ P.C.ns ≤ P.C.nf ∧ P.C.nf ≤ P.C.nl ∧
    (∀ l < P.C.nf, labF (P.C.L l) P.C.Λ = P.C.Λ) ∧
    (∀ l < P.C.ns, labF (pairF n (P.C.L l)) P.C.Δ = P.C.Δ) ∧ (∀ p ∈ P.D.sep, p < n) ∧
    sortedLt (P.D.R1.map Rec1.key) = true ∧ sumN (P.D.R1.map Rec1.m) = P.C.N1 := by
  have h := P.parts.1
  simp only [globOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, decide_eq_true_eq,
    Nat.ble_eq, List.mem_range, beq_iff_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have hn := P.hn
  refine ⟨fun p hp => ?_, h2, fun p hp => ?_, h4, h5, h6, h7, fun l hl => ?_, fun p hp => ?_, h10,
    h11⟩
  · have e := h1 p hp; rw [hn] at e; exact e
  · have e := h3 p hp; rw [hn] at e; exact e
  · have e := h8 l hl; rw [hn] at e; exact e
  · have e := h9 p hp; rw [hn] at e; exact e

theorem ns_le : P.C.ns ≤ P.C.nf := P.glob.2.2.2.2.1

theorem nf_le : P.C.nf ≤ P.C.nl := P.glob.2.2.2.2.2.1

theorem sep_lt : ∀ p ∈ P.D.sep, p < n := P.glob.2.2.2.2.2.2.2.2.1

@[expose] def elt (w : List ℕ) : Γ := evalElt P.els.toArray w

theorem getD_els (l : ℕ) : P.els.toArray.getD l 1 = P.els.getD l 1 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem elt_nil : P.elt [] = 1 := evalElt_nil _

theorem elt_cons (l : ℕ) (w : List ℕ) : P.elt (l :: w) = P.els.getD l 1 * P.elt w := by
  rw [elt, evalElt_cons, getD_els]
  rfl

theorem elt_append (u v : List ℕ) : P.elt (u ++ v) = P.elt u * P.elt v := by
  simp [elt, evalElt, List.map_append, List.prod_append]

theorem act_letter {l p : ℕ} (hl : l < P.C.nl) (hp : p < n) :
    act n (P.els.getD l 1) p = P.C.L l p := by
  rw [← ((P.hL l hl).2 p hp).1]
  simp [act]

theorem letter_lt {l p : ℕ} (hl : l < P.C.nl) (hp : p < n) : P.C.L l p < n :=
  ((P.hL l hl).2 p hp).2

theorem act_wordF (w : List ℕ) (hw : ∀ l ∈ w, l < P.C.nl) : ∀ p < n,
    act n (P.elt w) p = wordF P.C.L w p ∧ wordF P.C.L w p < n := by
  induction w with
  | nil => intro p hp; exact ⟨by rw [elt_nil]; exact act_one hp, hp⟩
  | cons l w ih =>
    intro p hp
    obtain ⟨e, hlt⟩ := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) p hp
    have hl := hw l List.mem_cons_self
    rw [elt_cons, act_mul _ _ hp, e, P.act_letter hl hlt]
    exact ⟨rfl, P.letter_lt hl hlt⟩

theorem good_elt {w : List ℕ} (hw : ∀ l ∈ w, l < P.C.nl) :
    Good n (tab n (P.elt w)).toArray (wordF P.C.L w) := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  obtain ⟨e, hlt⟩ := P.act_wordF w hw p hp
  refine ⟨?_, hlt⟩
  rw [← e]
  simp [act, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem smul_lw {w : List ℕ} (hw : ∀ l ∈ w, l < P.C.nl) (x : PtL n) :
    (P.elt w • x).val = lw P.C w x.val :=
  smul_val_eq (P.good_elt hw) x

theorem smul_fAct {l : ℕ} (hl : l < P.C.nf) (x : PrL n) :
    (P.els.getD l 1 • x).val = fAct P.C l x.val := by
  rw [prSmul_val_eq (P.hL l (lt_of_lt_of_le hl P.nf_le)) x, fAct, P.hn]
  unfold labF
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have h2 : Nat.blt p (Nat.mul n n) = true := by rw [Nat.blt_eq]; exact x.valid.2 p hp
  simp only [clampF, h2, cond_true]

@[expose] def S : Subgroup Γ := Subgroup.closure {x | x ∈ P.els.take P.C.ns}

@[expose] def H : Subgroup Γ := Subgroup.closure {x | x ∈ P.els.take P.C.nf}

theorem getD_mem_take {m l : ℕ} (hl : l < m) :
    P.els.getD l 1 ∈ Subgroup.closure {x | x ∈ P.els.take m} := by
  by_cases hle : l < P.els.length
  · apply Subgroup.subset_closure
    show P.els.getD l 1 ∈ P.els.take m
    rw [List.getD_eq_getElem _ _ hle]
    exact List.mem_iff_getElem.2 ⟨l, by simp; omega, by simp⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Subgroup.one_mem _

theorem elt_mem {K : Subgroup Γ} {w : List ℕ} (h : ∀ l ∈ w, P.els.getD l 1 ∈ K) :
    P.elt w ∈ K := by
  induction w with
  | nil => rw [elt_nil]; exact K.one_mem
  | cons l w ih =>
    rw [elt_cons]
    exact K.mul_mem (h l List.mem_cons_self) (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem elt_mem_S {w : List ℕ} (hw : ∀ l ∈ w, l < P.C.ns) : P.elt w ∈ P.S :=
  P.elt_mem fun l hl => P.getD_mem_take (hw l hl)

theorem elt_mem_H {w : List ℕ} (hw : ∀ l ∈ w, l < P.C.nf) : P.elt w ∈ P.H :=
  P.elt_mem fun l hl => P.getD_mem_take (hw l hl)

theorem mem_take_letter {m : ℕ} {x : Γ} (hx : x ∈ P.els.take m) :
    ∃ l < m, l < P.C.nl ∧ P.els.getD l 1 = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  simp only [List.length_take, lt_min_iff] at hi
  refine ⟨i, hi.1, P.hel ▸ hi.2, ?_⟩
  rw [List.getD_eq_getElem _ _ hi.2]
  simp

theorem S_le_H : P.S ≤ P.H := by
  rw [S, Subgroup.closure_le]
  intro x hx
  obtain ⟨l, hl, -, rfl⟩ := P.mem_take_letter hx
  exact P.getD_mem_take (lt_of_lt_of_le hl P.ns_le)

theorem smul_mem_take {α : Type*} [MulAction Γ α] {m : ℕ} {F : Set α}
    (hF : ∀ l < m, l < P.C.nl → ∀ y ∈ F, P.els.getD l 1 • y ∈ F) {k : Γ}
    (hk : k ∈ Subgroup.closure {x | x ∈ P.els.take m}) : ∀ y ∈ F, k • y ∈ F :=
  smul_mem_of_closure (fun e he => by
    obtain ⟨l, hl, hl', rfl⟩ := P.mem_take_letter he
    exact hF l hl hl') hk

theorem eq_of_sep {u v : List ℕ} (hu : ∀ l ∈ u, l < P.C.nl) (hv : ∀ l ∈ v, l < P.C.nl)
    (h : ∀ p ∈ P.D.sep, wordF P.C.L u p = wordF P.C.L v p) : P.elt u = P.elt v := by
  have hs := P.sep_lt
  exact eq_of_act_eq_base hs P.hsep fun b hb => by
    rw [(P.act_wordF u hu b (hs b hb)).1, (P.act_wordF v hv b (hs b hb)).1]
    exact h b hb

@[expose] def Λl : PtL n :=
  ⟨P.C.Λ, P.glob.2.1.imp le_of_lt, P.glob.1⟩

@[expose] def Δl : PrL n :=
  ⟨P.C.Δ, P.glob.2.2.2.1.imp le_of_lt, P.glob.2.2.1⟩

theorem Λ_nodup : P.C.Λ.Nodup := P.glob.2.1.imp ne_of_lt

theorem H_le_stab : P.H ≤ stabilizer Γ P.Λl := by
  rw [H, Subgroup.closure_le]
  intro x hx
  obtain ⟨l, hl, hl', rfl⟩ := P.mem_take_letter hx
  rw [SetLike.mem_coe, mem_stabilizer_iff]
  apply PtL.ext
  rw [smul_val_eq (P.hL l hl') P.Λl]
  exact P.glob.2.2.2.2.2.2.1 l hl

theorem S_le_stabΔ : P.S ≤ stabilizer Γ P.Δl := by
  rw [S, Subgroup.closure_le]
  intro x hx
  obtain ⟨l, hl, hl', rfl⟩ := P.mem_take_letter hx
  rw [SetLike.mem_coe, mem_stabilizer_iff]
  apply PrL.ext
  rw [prSmul_val_eq (P.hL l hl') P.Δl]
  exact P.glob.2.2.2.2.2.2.2.1 l hl

end Dc2SoundCtx

end CFSG.KC.SLD2

end
