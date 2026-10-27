module

public import Certificates.Data.Kernel.SporLatDcS
public import CFSG.Certificates.Kernel.E64FSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

theorem dcCheck_eq_dcCheckS (C : DcCtx) (D : DcData) : dcCheck C D = dcCheckS C D (2 ^ C.k) := rfl

structure DcSoundCtx (Γ : Type) [Group Γ] [Finite Γ] (n : ℕ) [MulAction Γ (Fin n)] where
  C : DcCtx
  D : DcData
  hn : C.n = n
  a : Γ
  b : Γ
  gen : Subgroup.closure ({a, b} : Set Γ) = ⊤
  sl : List Γ
  hsl : sl.length = C.ns
  hL : ∀ l < 2 + C.ns, Good n (tab n ((a :: b :: sl).getD l 1)).toArray (C.L l)
  hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng}
  s : ℕ
  hk : Nat.card (Subgroup.closure {x | x ∈ sl.take C.ng}) = s
  hN : Nat.card Γ = C.N * s
  hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1
  hΔ : PtValid n C.Δ
  h : dcCheckS C D s = true

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

@[expose] def els : Array Γ := (P.a :: P.b :: P.sl).toArray

@[expose] def S : Subgroup Γ := Subgroup.closure {x | x ∈ P.sl.take P.C.ng}

theorem hlaw : LabLawful Γ n ptLab (PtValid n) := ptLab_lawful

private theorem els_size : P.els.size = 2 + P.C.ns := by
  simp [els, P.hsl]
  omega

theorem els_getD (l : ℕ) : P.els.getD l 1 = (P.a :: P.b :: P.sl).getD l 1 := by
  simp [els, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem els_getD_sl {l : ℕ} (hl : 2 ≤ l) : P.els.getD l 1 = P.sl.getD (l - 2) 1 := by
  rcases Nat.exists_eq_add_of_le hl with ⟨k, rfl⟩
  have h2 : 2 + k - 2 = k := by omega
  rw [h2, P.els_getD, List.getD_eq_getElem?_getD, Nat.add_comm 2 k]
  rfl

private theorem good {l : ℕ} (hl : l < 2 + P.C.ns) :
    Good n (tab n (P.els.getD l 1)).toArray (P.C.L l) := by
  rw [P.els_getD]
  exact P.hL l hl

theorem act_letter {l p : ℕ} (hl : l < 2 + P.C.ns) (hp : p < n) :
    act n (P.els.getD l 1) p = P.C.L l p := by
  rw [← ((P.good hl).2 p hp).1]
  simp [act]

theorem letter_lt {l p : ℕ} (hl : l < 2 + P.C.ns) (hp : p < n) : P.C.L l p < n :=
  ((P.good hl).2 p hp).2

theorem act_wordF : ∀ (w : List ℕ), (∀ l ∈ w, l < 2 + P.C.ns) → ∀ p < n,
    act n (evalElt P.els w) p = wordF P.C.L w p ∧ wordF P.C.L w p < n := by
  intro w
  induction w with
  | nil =>
    intro _ p hp
    exact ⟨act_one hp, hp⟩
  | cons l w ih =>
    intro hw p hp
    have hl : l < 2 + P.C.ns := hw l List.mem_cons_self
    have hw' : ∀ l' ∈ w, l' < 2 + P.C.ns := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    obtain ⟨e, hlt⟩ := ih hw' p hp
    rw [evalElt_cons, act_mul _ _ hp, e, P.act_letter hl hlt]
    exact ⟨rfl, P.letter_lt hl hlt⟩

theorem act_wordF_eq {w : List ℕ} (hw : ∀ l ∈ w, l < 2 + P.C.ns) {p : ℕ} (hp : p < n) :
    act n (evalElt P.els w) p = wordF P.C.L w p :=
  (P.act_wordF w hw p hp).1

private theorem wordF_lt {w : List ℕ} (hw : ∀ l ∈ w, l < 2 + P.C.ns) {p : ℕ} (hp : p < n) :
    wordF P.C.L w p < n :=
  (P.act_wordF w hw p hp).2

theorem labF_eq_lab {w : List ℕ} (hw : ∀ l ∈ w, l < 2 + P.C.ns) :
    labF (wordF P.C.L w) P.C.Δ = lab n ptLab P.C.Δ (evalElt P.els w) := by
  have h1 : lab n ptLab P.C.Δ (evalElt P.els w)
      = sortN (P.C.Δ.map fun p => act n (evalElt P.els w) p) := ptAct_tab _ _
  rw [labF, h1, sortN_eq]
  congr 1
  exact List.map_congr_left fun p hp => (P.act_wordF_eq hw (P.hΔ.2 p hp)).symm

private theorem els_getD_lt_two {l : ℕ} (hl : l < 2) : P.els.getD l 1 = #[P.a, P.b].getD l 1 := by
  interval_cases l <;> simp [els]

theorem evalElt_eq_wordElt {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    evalElt P.els w = wordElt P.a P.b w := by
  unfold wordElt
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalElt_cons, evalElt_cons, P.els_getD_lt_two (hw l List.mem_cons_self),
      ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))]

private theorem labF_wordElt (w : List ℕ) (hw : ∀ l ∈ w, l < 2) :
    labF (wordF P.C.L w) P.C.Δ = lab n ptLab P.C.Δ (wordElt P.a P.b w) := by
  rw [P.labF_eq_lab (fun l hl => by have := hw l hl; omega), P.evalElt_eq_wordElt hw]

theorem evalElt_mem_S {w : List ℕ} (hw : ∀ l ∈ w, 2 ≤ l ∧ l < 2 + P.C.ns) :
    evalElt P.els w ∈ P.S := by
  induction w with
  | nil => rw [evalElt_nil]; exact P.S.one_mem
  | cons l w ih =>
    rw [evalElt_cons]
    refine P.S.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨h2, hlt⟩ := hw l List.mem_cons_self
    rw [P.els_getD_sl h2]
    apply P.hS
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [P.hsl]; omega)]
    exact List.mem_iff_getElem.mpr ⟨l - 2, by rw [P.hsl]; omega, rfl⟩

end DcSoundCtx

end CFSG.KC.SLDc

end
