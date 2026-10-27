module

public import Certificates.Data.Kernel.He7222.Fib
public import Batteries.Data.List.Basic
import CFSG.Certificates.Kernel.He7222.ChainSound
import CFSG.Certificates.Kernel.OrbRow.LevelSound
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KS.PF

@[expose] def FibLeaf (w m : ℕ) (KTs : List (List ℕ)) (gs : List ℕ) (FT : List (List ℕ))
    (S0 : List (List ℕ)) (ks : List ℕ) : Prop :=
  okK (fun p => evK w m gs (evK w m ks p)) = true → ∃ ri t k2, (ri :: t :: k2) ∈ S0 ∧
    tupOK KTs k2 = true ∧ conjYK w m gs ks (stkK KTs k2) (stkK KTs (getLs FT t)) = true

theorem fleafK_sound {w m : ℕ} {KTs : List (List ℕ)} {gs : List ℕ} {FT : List (List ℕ)}
    {ks : List ℕ} {i : ℕ} {st : List (List ℕ)} {k : ℕ → List (List ℕ) → Bool}
    (h : fleafK w m KTs gs FT ks i st k = true) :
    (∃ i' st', (∀ r ∈ st', r ∈ st) ∧ k i' st' = true) ∧ FibLeaf w m KTs gs FT st ks := by
  unfold fleafK at h
  rw [strictB_eqP] at h
  cases st with
  | nil =>
    rw [bIf_iff] at h
    rcases h with ⟨-, h⟩ | ⟨ho, h⟩
    · exact absurd h (by simp)
    · exact ⟨⟨_, [], fun r hr => hr, h⟩, fun h' => by rw [ho] at h'; exact absurd h' (by simp)⟩
  | cons rec rest =>
    cases rec with
    | nil => exact absurd h (by simp)
    | cons ri tk =>
      change bIf(Nat.beq ri i, List.rec (motive := fun _ => Bool) false
          (fun t k2 _ => bAnd(tupOK KTs k2,
            bAnd(conjYK w m gs ks (stkK KTs k2) (stkK KTs (getLs FT t)), k (Nat.succ i) rest))) tk,
          bIf(okK (fun p => evK w m gs (evK w m ks p)), false,
            k (Nat.succ i) ((ri :: tk) :: rest))) = true at h
      rw [bIf_iff] at h
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · cases tk with
        | nil => exact absurd h (by simp)
        | cons t k2 =>
          change bAnd(tupOK KTs k2, bAnd(conjYK w m gs ks (stkK KTs k2) (stkK KTs (getLs FT t)),
            k (Nat.succ i) rest)) = true at h
          rw [bAnd_iff, bAnd_iff] at h
          exact ⟨⟨_, rest, fun r hr => List.mem_cons_of_mem _ hr, h.2.2⟩,
            fun _ => ⟨ri, t, k2, List.mem_cons_self, h.1, h.2.1⟩⟩
      · rw [bIf_iff] at h
        rcases h with ⟨-, h⟩ | ⟨ho, h⟩
        · exact absurd h (by simp)
        · exact ⟨⟨_, _, fun r hr => hr, h⟩, fun h' => by rw [ho] at h'; exact absurd h' (by simp)⟩

@[expose] noncomputable def fwalkL (w m : ℕ) (KTs : List (List ℕ)) (gs : List ℕ)
    (FT : List (List ℕ)) (Ls : List (List ℕ)) (stack : List ℕ) (lvl : List ℕ) :
    ℕ → List (List ℕ) → (ℕ → List (List ℕ) → Bool) → Bool :=
  List.rec
    (motive := fun _ => Nat → List (List Nat) → (Nat → List (List Nat) → Bool) → Bool)
    (fun i st k => k i st)
    (fun t _ ihT i st k => fwalkK w m KTs gs FT Ls (List.cons t stack) i st
      (fun i' st' => ihT i' st' k))
    lvl

theorem fwalkK_sound {w m : ℕ} {KTs : List (List ℕ)} {gs : List ℕ} {FT : List (List ℕ)}
    {S0 : List (List ℕ)} : ∀ (Ls : List (List ℕ)) (stack : List ℕ) (i : ℕ) (st : List (List ℕ))
    (k : ℕ → List (List ℕ) → Bool), (∀ r ∈ st, r ∈ S0) →
    fwalkK w m KTs gs FT Ls stack i st k = true →
    (∃ i' st', (∀ r ∈ st', r ∈ S0) ∧ k i' st' = true) ∧ ∀ ts : List ℕ,
      List.Forall₂ (· ∈ ·) ts Ls → FibLeaf w m KTs gs FT S0 (ts.reverse ++ stack) := by
  intro Ls
  induction Ls with
  | nil =>
    intro stack i st k hst h
    have h' : fleafK w m KTs gs FT stack i st k = true := h
    obtain ⟨⟨i', st', hst', hk⟩, hleaf⟩ := fleafK_sound h'
    refine ⟨⟨i', st', fun r hr => hst r (hst' r hr), hk⟩, fun ts hts => ?_⟩
    cases hts
    intro ho
    obtain ⟨ri, t, k2, hm, h1, h2⟩ := hleaf ho
    exact ⟨ri, t, k2, hst _ hm, h1, h2⟩
  | cons lvl Ls ih =>
    intro stack
    have inner : ∀ (lv : List ℕ) (i : ℕ) (st : List (List ℕ)) (k : ℕ → List (List ℕ) → Bool),
        (∀ r ∈ st, r ∈ S0) → fwalkL w m KTs gs FT Ls stack lv i st k = true →
        (∃ i' st', (∀ r ∈ st', r ∈ S0) ∧ k i' st' = true) ∧ ∀ t ∈ lv, ∀ ts : List ℕ,
          List.Forall₂ (· ∈ ·) ts Ls → FibLeaf w m KTs gs FT S0 (ts.reverse ++ t :: stack) := by
      intro lv
      induction lv with
      | nil => exact fun i st k hst h => ⟨⟨i, st, hst, h⟩, fun t ht => absurd ht List.not_mem_nil⟩
      | cons t lv ihl =>
        intro i st k hst h
        have h' : fwalkK w m KTs gs FT Ls (List.cons t stack) i st
            (fun i' st' => fwalkL w m KTs gs FT Ls stack lv i' st' k) = true := h
        obtain ⟨⟨i1, st1, hst1, hk1⟩, hleaf1⟩ := ih (t :: stack) i st _ hst h'
        obtain ⟨⟨i2, st2, hst2, hk2⟩, hleaf2⟩ := ihl i1 st1 k hst1 hk1
        refine ⟨⟨i2, st2, hst2, hk2⟩, fun t' ht' => ?_⟩
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact hleaf1
        · exact hleaf2 t' ht'
    intro i st k hst h
    obtain ⟨hk, hleaf⟩ := inner lvl i st k hst h
    refine ⟨hk, fun ts hts => ?_⟩
    cases hts with
    | cons ht hts' =>
      rename_i t ts
      have := hleaf t ht ts hts'
      rw [List.reverse_cons, List.append_assoc]
      exact this

theorem fibK_sound {w m : ℕ} {KTs Ls : List (List ℕ)} {gs : List ℕ} {FR FT : List (List ℕ)}
    (h : fibK w m KTs Ls gs FR FT = true) :
    ∀ ts : List ℕ, List.Forall₂ (· ∈ ·) ts Ls → FibLeaf w m KTs gs FT FR ts.reverse := by
  obtain ⟨-, hleaf⟩ := fwalkK_sound Ls [] 0 FR _ (fun r hr => hr) h
  intro ts hts
  have := hleaf ts hts
  rw [List.append_nil] at this
  exact this

theorem srW_sound {w m : ℕ} {Ts TIs KTs : List (List ℕ)} {ss : List ℕ} {h hI nr : ℕ}
    {KC : List (List ℕ)} {XR Sv : List ℕ} {SR : List (List ℕ)} :
    ∀ (L : List (List ℕ)) (q : ℕ), L = SR.drop q → q ≤ SR.length →
    List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q (lenS Sv))
      (fun rec _ ih q => List.rec (motive := fun _ => Bool) false
        (fun r k _ => strictB (getS Sv q) (fun n => strictB (getS XR r) (fun xr =>
          bAnd(Nat.blt r nr, bAnd(tupOK KTs k,
            bAnd(srEq w m h hI ss (stkK Ts (getLs KC n)) (stkIK TIs (getLs KC n) List.nil)
                (stkK Ts (getLs KC xr)) (stkIK TIs (getLs KC xr) List.nil) (stkK KTs k),
              strictB (Nat.succ q) ih))))))
        rec) L q = true →
    SR.length = Sv.length ∧ ∀ j, q ≤ j → j < SR.length → ∃ r k, SR.getD j [] = r :: k ∧
      r < nr ∧ tupOK KTs k = true ∧
      srEq w m h hI ss (stkK Ts (getLs KC (getS Sv j))) (stkIK TIs (getLs KC (getS Sv j)) [])
        (stkK Ts (getLs KC (getS XR r))) (stkIK TIs (getLs KC (getS XR r)) []) (stkK KTs k) =
        true := by
  intro L
  induction L with
  | nil =>
    intro q hL hq hw
    have hT : SR.length ≤ q := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq q (lenS Sv) = true := hw
    rw [CFSG.KC.OrbRow.lenS_eq] at h'
    have := Nat.eq_of_beq_eq_true h'
    exact ⟨by omega, fun j hj hj' => absurd hj' (by omega)⟩
  | cons rec L ih =>
    intro q hL hq hw
    have hqS : q < SR.length := by
      rcases Nat.lt_or_ge q SR.length with h1 | h1
      · exact h1
      · have : SR.drop q = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have hrec : SR.getD q [] = rec := by
      rw [List.getD_eq_getElem?_getD, ← List.head?_drop, ← hL, List.head?_cons, Option.getD_some]
    have hL' : L = SR.drop (q + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    cases rec with
    | nil => exact absurd hw (by simp)
    | cons r k =>
      have h' : strictB (getS Sv q) (fun n => strictB (getS XR r) (fun xr =>
          bAnd(Nat.blt r nr, bAnd(tupOK KTs k,
            bAnd(srEq w m h hI ss (stkK Ts (getLs KC n)) (stkIK TIs (getLs KC n) List.nil)
                (stkK Ts (getLs KC xr)) (stkIK TIs (getLs KC xr) List.nil) (stkK KTs k),
              strictB (Nat.succ q) (List.rec (motive := fun _ => Nat → Bool)
                (fun q => Nat.beq q (lenS Sv))
                (fun rec _ ih q => List.rec (motive := fun _ => Bool) false
                  (fun r k _ => strictB (getS Sv q) (fun n => strictB (getS XR r) (fun xr =>
                    bAnd(Nat.blt r nr, bAnd(tupOK KTs k,
                      bAnd(srEq w m h hI ss (stkK Ts (getLs KC n)) (stkIK TIs (getLs KC n) List.nil)
                          (stkK Ts (getLs KC xr)) (stkIK TIs (getLs KC xr) List.nil) (stkK KTs k),
                        strictB (Nat.succ q) ih))))))
                  rec) L)))))) = true := hw
      rw [strictB_eqP (getS Sv q), strictB_eqP (getS XR r), bAnd_iff, bAnd_iff, bAnd_iff,
        strictB_eqP (Nat.succ q), Nat.blt_eq] at h'
      obtain ⟨hr, ht, he, hrest⟩ := h'
      obtain ⟨hlen, hall⟩ := ih (q + 1) hL' hqS hrest
      refine ⟨hlen, fun j hj hjS => ?_⟩
      rcases Nat.lt_or_ge q j with hqj | hqj
      · exact hall j hqj hjS
      have : j = q := by omega
      subst this
      exact ⟨r, k, hrec, hr, ht, he⟩

theorem srK_sound {w m : ℕ} {Ts TIs KTs : List (List ℕ)} {ss : List ℕ} {h hI nr : ℕ}
    {KC : List (List ℕ)} {XR Sv : List ℕ} {SR : List (List ℕ)}
    (hs : srK w m Ts TIs KTs ss h hI nr KC XR Sv SR = true) :
    SR.length = Sv.length ∧ ∀ j < SR.length, ∃ r k, SR.getD j [] = r :: k ∧
      r < nr ∧ tupOK KTs k = true ∧
      srEq w m h hI ss (stkK Ts (getLs KC (getS Sv j))) (stkIK TIs (getLs KC (getS Sv j)) [])
        (stkK Ts (getLs KC (getS XR r))) (stkIK TIs (getLs KC (getS XR r)) []) (stkK KTs k) =
        true := by
  obtain ⟨h1, h2⟩ := srW_sound SR 0 rfl (Nat.zero_le _) hs
  exact ⟨h1, fun j hj => h2 j (Nat.zero_le _) hj⟩

end CFSG.KC.HeChain

end
