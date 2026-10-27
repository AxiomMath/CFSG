module

public import Certificates.Data.Kernel.Ivk8Cent
public import CFSG.Certificates.Kernel.Spor.RecGroup
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.Ivk8Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KS.RecGroup

@[expose] def PR (n w x : Nat) (σ : Equiv.Perm (Fin n)) : Prop :=
  canonK n w (mask w) (n * w) x = true ∧ Rep n (tabT (unpack n w x)) σ

variable {n w : Nat}

theorem PR.pc {p q : Nat} {σ τ : Equiv.Perm (Fin n)} (hp : PR n w p σ) (hq : PR n w q τ) :
    PR n w (pc n w p q) (σ * τ) :=
  ⟨CFSG.KC.BfsPin.canonK_pcomp hp.1 hq.1, rep_pcomp hp.1 hq.1 hp.2 hq.2⟩

theorem PR.one (hsz : szOK n w = true) : PR n w (pidn n w) 1 := by
  refine ⟨(CFSG.KC.BfsPin.PP.id hsz).1, ?_⟩
  have h32 : n < 2 ^ 32 := (CFSG.KC.BfsPin.PP.id hsz).lt32
  rw [← CFSG.KC.BfsPin.idA_eq hsz, ← idT_tabT]
  exact Rep.idT h32

theorem PR.beq {x y : Nat} {σ τ : Equiv.Perm (Fin n)} (hx : PR n w x σ) (hy : PR n w y τ) :
    Nat.beq x y = true ↔ σ = τ := by
  constructor
  · intro h
    have e := Nat.eq_of_beq_eq_true h
    subst e
    exact perm_eq_of_rep hx.2 hy.2
  · intro h
    subst h
    rw [eq_of_rep_eq hx.1 hy.1 hx.2 hy.2]
    exact Nat.beq_refl _

theorem bIf_ne {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem bIf_or {a b : Bool} (h : bIf(a, true, b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem bAnd_and {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact (Bool.false_ne_true h).elim
  · exact ⟨rfl, h⟩

theorem evW_rep (hsz : szOK n w = true) {L : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hL : ∀ l, PR n w (L l) (g l)) (ws : List Nat) : PR n w (evW n w L ws) (ws.map g).prod := by
  induction ws with
  | nil => exact PR.one hsz
  | cons l ws ih =>
    change PR n w (strictN (evW n w L ws) (fun r => pc n w (L l) r)) _
    rw [PF.strictN_eqP, List.map_cons, List.prod_cons]
    exact (hL l).pc ih

theorem cube_rep {u : Nat} {σ : Equiv.Perm (Fin n)} (hu : PR n w u σ) :
    PR n w (cube n w u) (σ ^ 3) := by
  unfold cube
  rw [PF.strictN_eqP, pow_three]
  exact hu.pc (hu.pc hu)

theorem movesP_sound (hsz : szOK n w = true) {u : Nat} {σ : Equiv.Perm (Fin n)}
    (hu : PR n w u σ) (h : movesP n w u = true) : σ ^ 27 ≠ 1 := by
  unfold movesP at h
  rw [PF.strictB_eqP, PF.strictB_eqP] at h
  have h3 := cube_rep (cube_rep (cube_rep hu))
  rw [← pow_mul, ← pow_mul] at h3
  intro e
  rw [e] at h3
  have := (h3.beq (PR.one hsz)).2 rfl
  rw [bIf_ne h] at this
  exact absurd this (by decide)

theorem wit1P_sound (hsz : szOK n w = true) {x : Nat} {ξ : Equiv.Perm (Fin n)}
    (hx : PR n w x ξ) {hs : List Nat} {hsP : List (Equiv.Perm (Fin n))}
    (hh : List.Forall₂ (PR n w) hs hsP) (h : wit1P n w x hs = true) :
    ∃ a ∈ hsP, (ξ * (a * ξ * a)) ^ 27 ≠ 1 := by
  induction hh with
  | nil => exact (Bool.false_ne_true h).elim
  | @cons a α hs hsP ha _ ih =>
    rcases bIf_or h with h1 | h1
    · exact ⟨α, List.mem_cons_self .., movesP_sound hsz (hx.pc ((ha.pc hx).pc ha)) h1⟩
    · obtain ⟨b, hb, hne⟩ := ih h1
      exact ⟨b, List.mem_cons_of_mem _ hb, hne⟩

theorem wit2In_sound (hsz : szOK n w = true) {x y : Nat} {ξ η : Equiv.Perm (Fin n)}
    (hx : PR n w x ξ) (hy : PR n w y η) {hs : List Nat} {hsP : List (Equiv.Perm (Fin n))}
    (hh : List.Forall₂ (PR n w) hs hsP) (h : wit2In n w x y hs = true) :
    ∃ b ∈ hsP, (η * (b * ξ * b)) ^ 27 ≠ 1 := by
  induction hh with
  | nil => exact (Bool.false_ne_true h).elim
  | @cons b β hs hsP hb _ ih =>
    rcases bIf_or h with h1 | h1
    · exact ⟨β, List.mem_cons_self .., movesP_sound hsz (hy.pc ((hb.pc hx).pc hb)) h1⟩
    · obtain ⟨c, hc, hne⟩ := ih h1
      exact ⟨c, List.mem_cons_of_mem _ hc, hne⟩

theorem wit2Q_sound (hsz : szOK n w = true) {x : Nat} {ξ : Equiv.Perm (Fin n)}
    (hx : PR n w x ξ) {hs : List Nat} {hsP : List (Equiv.Perm (Fin n))}
    (hh : List.Forall₂ (PR n w) hs hsP) {as : List Nat} {asP : List (Equiv.Perm (Fin n))}
    (ha : List.Forall₂ (PR n w) as asP) (h : wit2Q n w x as hs = true) :
    ∃ a ∈ asP, ∃ b ∈ hsP, (ξ * (a * ξ * a) * (b * ξ * b)) ^ 27 ≠ 1 := by
  induction ha with
  | nil => exact (Bool.false_ne_true h).elim
  | @cons a α as asP ha' _ ih =>
    rcases bIf_or h with h1 | h1
    · rw [PF.strictB_eqP] at h1
      obtain ⟨b, hb, hne⟩ := wit2In_sound hsz hx (hx.pc ((ha'.pc hx).pc ha')) hh h1
      exact ⟨α, List.mem_cons_self .., b, hb, hne⟩
    · obtain ⟨c, hc, b, hb, hne⟩ := ih h1
      exact ⟨c, List.mem_cons_of_mem _ hc, b, hb, hne⟩

theorem chkKP_at (hsz : szOK n w = true) {c ci cnt : Nat} {T : Nat → Nat}
    {γ τ : Equiv.Perm (Fin n)} (hc : PR n w c γ) (hci : PR n w ci γ⁻¹) {hs : List Nat}
    {hsP : List (Equiv.Perm (Fin n))} (hh : List.Forall₂ (PR n w) hs hsP)
    (h : chkKP n w c ci cnt T hs = true) {i : Nat} (hi : i < cnt) (hT : PR n w (T i) τ) :
    (∃ a ∈ hsP, (γ * τ * γ⁻¹ * (a * (γ * τ * γ⁻¹) * a)) ^ 27 ≠ 1) ∨
      ∃ a ∈ hsP, ∃ b ∈ hsP, (γ * τ * γ⁻¹ * (a * (γ * τ * γ⁻¹) * a) *
        (b * (γ * τ * γ⁻¹) * b)) ^ 27 ≠ 1 := by
  have hi' := allN_spec h i hi
  rw [PF.strictB_eqP] at hi'
  have hx : PR n w (pc n w c (pc n w (T i) ci)) (γ * τ * γ⁻¹) := by
    rw [mul_assoc]
    exact hc.pc (hT.pc hci)
  rcases bIf_or hi' with h1 | h1
  · exact Or.inl (wit1P_sound hsz hx hh h1)
  · exact Or.inr (wit2Q_sound hsz hx hh hh h1)

theorem withH_eq (L : Nat → Nat) (wA wB wC : List Nat) (k : Nat → Nat → Nat → List Nat → Bool) :
    withH n w L wA wB wC k = k (evW n w L wC) (pc n w (evW n w L wA) (evW n w L wB))
      (pc n w (pc n w (evW n w L wA) (evW n w L wB)) (evW n w L wC))
      [evW n w L wA, evW n w L wB, pc n w (evW n w L wA) (evW n w L wB), evW n w L wC,
        pc n w (evW n w L wA) (evW n w L wC), pc n w (evW n w L wB) (evW n w L wC),
        pc n w (pc n w (evW n w L wA) (evW n w L wB)) (evW n w L wC)] := by
  unfold withH
  simp only [PF.strictB_eqP]

theorem hOK_sound (hsz : szOK n w = true) {L : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hL : ∀ l, PR n w (L l) (g l)) {wA wB wC : List Nat} (h : hOK n w L wA wB wC = true) :
    (wA.map g).prod * (wA.map g).prod = 1 ∧ (wB.map g).prod * (wB.map g).prod = 1 ∧
    (wC.map g).prod * (wC.map g).prod = 1 ∧
    (wA.map g).prod * (wB.map g).prod = (wB.map g).prod * (wA.map g).prod ∧
    (wA.map g).prod * (wC.map g).prod = (wC.map g).prod * (wA.map g).prod ∧
    (wB.map g).prod * (wC.map g).prod = (wC.map g).prod * (wB.map g).prod ∧
    (wC.map g).prod ≠ 1 ∧ (wA.map g).prod * (wB.map g).prod ≠ 1 ∧
    (wC.map g).prod ≠ (wA.map g).prod * (wB.map g).prod := by
  have hA := evW_rep hsz hL wA
  have hB := evW_rep hsz hL wB
  have hC := evW_rep hsz hL wC
  have he := PR.one (n := n) (w := w) hsz
  unfold hOK at h
  simp only [PF.strictB_eqP] at h
  obtain ⟨h1, h⟩ := bAnd_and h
  obtain ⟨h2, h⟩ := bAnd_and h
  obtain ⟨h3, h⟩ := bAnd_and h
  obtain ⟨h4, h⟩ := bAnd_and h
  obtain ⟨h5, h⟩ := bAnd_and h
  obtain ⟨h6, h⟩ := bAnd_and h
  obtain ⟨h7, h⟩ := bAnd_and h
  obtain ⟨h8, h9⟩ := bAnd_and h
  have ne : ∀ {x y : Nat} {σ τ : Equiv.Perm (Fin n)}, PR n w x σ → PR n w y τ →
      neP x y = true → σ ≠ τ := by
    intro x y σ τ hx hy hn e
    have := (hx.beq hy).2 e
    rw [bIf_ne hn] at this
    exact absurd this (by decide)
  exact ⟨((hA.pc hA).beq he).1 h1, ((hB.pc hB).beq he).1 h2, ((hC.pc hC).beq he).1 h3,
    ((hA.pc hB).beq (hB.pc hA)).1 h4, ((hA.pc hC).beq (hC.pc hA)).1 h5,
    ((hB.pc hC).beq (hC.pc hB)).1 h6, ne hC he h7, ne (hA.pc hB) he h8, ne hC (hA.pc hB) h9⟩

theorem conjOK_sound (hsz : szOK n w = true) {c ci t e : Nat} {γ γ' τ ε : Equiv.Perm (Fin n)}
    (hc : PR n w c γ) (hci : PR n w ci γ') (ht : PR n w t τ) (he : PR n w e ε)
    (h : conjOK n w c ci t e = true) : γ' = γ⁻¹ ∧ γ * τ * γ⁻¹ = ε := by
  obtain ⟨h1, h2⟩ := bAnd_and h
  have e1 : γ * γ' = 1 := ((hc.pc hci).beq (PR.one hsz)).1 h1
  have e2 : γ' = γ⁻¹ := eq_inv_of_mul_eq_one_right e1
  refine ⟨e2, ?_⟩
  have e3 := ((hc.pc (ht.pc hci)).beq he).1 h2
  rw [e2, ← mul_assoc] at e3
  exact e3

end CFSG.KS.Ivk8Cent

end
