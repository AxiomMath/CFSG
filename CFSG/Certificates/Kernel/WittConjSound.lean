module

public import Certificates.Data.Kernel.WittConj
public import CFSG.Certificates.Kernel.WittCntSound

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt

theorem exists_mem_map' {α β : Type*} (f : α → β) (l : List α) (P : β → Prop) :
    (∃ b ∈ l.map f, P b) ↔ ∃ a ∈ l, P (f a) := by
  simp

theorem exists_mem_cons' {α : Type*} (a : α) (l : List α) (P : α → Prop) :
    (∃ b ∈ a :: l, P b) ↔ P a ∨ ∃ b ∈ l, P b := by
  simp

theorem pcomp_pkw5(σ τ : Equiv.Perm (Fin 22)) :
    pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (pkw 5 σ) (pkw 5 τ) = pkw 5 (σ * τ) := by
  have h := pkw_mul (n := 22) (w := 5) (by norm_num) (by norm_num) σ τ
  rw [mask_five] at h
  exact h

theorem pkw5_inj {σ τ : Equiv.Perm (Fin 22)} : pkw 5 σ = pkw 5 τ ↔ σ = τ :=
  ⟨pkw_inj (by norm_num), fun h => h ▸ rfl⟩

theorem invT_pkw (I : Nat) (hI : pkw 5 (1 : Equiv.Perm (Fin 22)) = I) (τ : Equiv.Perm (Fin 22)) :
    invT I (pkw 5 τ) = decide (∀ x, τ (τ x) = x) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, invT, Nat.beq_eq, pcomp_pkw5, ← hI, pkw5_inj]
  constructor
  · intro h x
    have := congrArg (fun g : Equiv.Perm (Fin 22) => g x) h
    simpa using this
  · intro h
    exact Equiv.ext fun x => by simpa using h x

theorem memN_iff (y : Nat) : ∀ Ls : List Nat, memN Ls y = true ↔ y ∈ Ls
  | [] => by simp [memN]
  | L :: Ls => by
    have h : memN (L :: Ls) y = (Nat.beq y L || memN Ls y) := by
      change Bool.rec (motive := fun _ => Bool) (memN Ls y) true (Nat.beq y L) = _
      cases Nat.beq y L <;> rfl
    rw [h, Bool.or_eq_true, memN_iff y Ls, Nat.beq_eq, List.mem_cons]

theorem memN_pkw (τ : Equiv.Perm (Fin 22)) (gs : List (Equiv.Perm (Fin 22))) :
    memN (gs.map (pkw 5)) (pkw 5 τ) = true ↔ τ ∈ gs := by
  rw [memN_iff, List.mem_map]
  constructor
  · rintro ⟨g, hg, e⟩
    rwa [← pkw5_inj.1 e]
  · intro h
    exact ⟨τ, h, rfl⟩

theorem conjR_iff (G y : Nat) : ∀ Rs : List Nat, conjR G y Rs = true ↔
    ∃ R ∈ Rs, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G y =
      pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) R G
  | [] => by simp [conjR]
  | R :: Rs => by
    have h : conjR G y (R :: Rs) = (Nat.beq (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G y)
        (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) R G) || conjR G y Rs) := by
      change Bool.rec (motive := fun _ => Bool) (conjR G y Rs) true (Nat.beq _ _) = _
      cases Nat.beq (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G y)
        (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) R G) <;> rfl
    rw [h, Bool.or_eq_true, conjR_iff G y Rs, Nat.beq_eq, exists_mem_cons']

theorem conjAny_iff (Rs : List Nat) (y : Nat) : ∀ Gs : List Nat, conjAny Gs Rs y = true ↔
    ∃ G ∈ Gs, conjR G y Rs = true
  | [] => by simp [conjAny]
  | G :: Gs => by
    have h : conjAny (G :: Gs) Rs y = (conjR G y Rs || conjAny Gs Rs y) := by
      change Bool.rec (motive := fun _ => Bool) (conjAny Gs Rs y) true (conjR G y Rs) = _
      cases conjR G y Rs <;> rfl
    rw [h, Bool.or_eq_true, conjAny_iff Rs y Gs, exists_mem_cons']

theorem conjAny_pkw_iff (τ : Equiv.Perm (Fin 22)) (gs rs : List (Equiv.Perm (Fin 22))) :
    conjAny (gs.map (pkw 5)) (rs.map (pkw 5)) (pkw 5 τ) = true ↔ ∃ g ∈ gs, ∃ r ∈ rs, g * τ = r * g := by
  rw [conjAny_iff, exists_mem_map']
  refine exists_congr fun g => and_congr_right fun _ => ?_
  rw [conjR_iff, exists_mem_map']
  refine exists_congr fun r => and_congr_right fun _ => ?_
  rw [pcomp_pkw5, pcomp_pkw5, pkw5_inj]

theorem pevalW_pkw (f : Fin 5 → Equiv.Perm (Fin 22)) (P PI : List Nat) (I : Nat)
    (hP : ∀ j : Fin 5, pkw 5 (f j) = P.getD j.val 0)
    (hPI : ∀ j : Fin 5, pkw 5 (f j)⁻¹ = PI.getD j.val 0)
    (hI : pkw 5 (1 : Equiv.Perm (Fin 22)) = I) :
    ∀ w : List (Fin 5 × Bool),
      pevalW P PI I w = pkw 5 (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod
  | [] => hI.symm
  | x :: w => by
    change pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31)
      (Bool.rec (motive := fun _ => Nat) (PI.getD x.1.val 0) (P.getD x.1.val 0) x.2)
      (pevalW P PI I w) = _
    rw [pevalW_pkw f P PI I hP hPI hI w, List.map_cons, List.prod_cons, ← pcomp_pkw5]
    congr 1
    cases x.2
    · exact (hPI x.1).symm
    · exact (hP x.1).symm

theorem pwordAB_nil (A B Bi G : Nat) : pwordAB A B Bi G [] = G := rfl

theorem pwordAB_cons (A B Bi G : Nat) (c : Char) (l : List Char) :
    pwordAB A B Bi G (c :: l) = pwordAB A B Bi (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G
      (if c = 'a' then A else if c = 'b' then B else Bi)) l := rfl

theorem eqL_iff : ∀ xs ys : List Nat, eqL xs ys = true ↔ xs = ys
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: xs, y :: ys => by
    have h : eqL (x :: xs) (y :: ys) = (Nat.beq x y && eqL xs ys) := by
      change Bool.rec (motive := fun _ => Bool) false (eqL xs ys) (Nat.beq x y) = _
      cases Nat.beq x y <;> rfl
    rw [h, Bool.and_eq_true, Nat.beq_eq, eqL_iff xs ys, List.cons.injEq]

theorem beq_pt_pkw (τ : Equiv.Perm (Fin 22)) (i k : Fin 22) :
    Nat.beq (pt (pkw 5 τ) i.val) k.val = decide (τ i = k) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, pt_pkw, decide_eq_true_iff, Fin.val_inj]

theorem presL_pkw (τ : Equiv.Perm (Fin 22)) (L : List (Fin 22)) (l : List Nat) (X : Nat)
    (hl : ∀ x : Fin 22, x ∈ L ↔ x.val ∈ l) (hlt : ∀ i ∈ l, i < 22)
    (hX : ∀ x : Fin 22, inM X x.val = true ↔ x ∈ L) :
    presT X l (pkw 5 τ) = decide (∀ p ∈ L, τ p ∈ L) := by
  rw [presT_pkw τ L.toFinset l X (fun x => by rw [List.mem_toFinset]; exact hl x) hlt
    (fun x => by rw [List.mem_toFinset]; exact hX x)]
  simp only [List.mem_toFinset]

end CFSG.KC.WCnt

end
