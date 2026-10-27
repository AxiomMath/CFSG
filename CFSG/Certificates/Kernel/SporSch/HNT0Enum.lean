module

public import CFSG.Certificates.Kernel.Spor.EnumBaseSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import Certificates.Data.Kernel.SporSch.HNT0

public section

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KS CFSG.KS.EnumBase CFSG.KS.PEnum

theorem mask8 : mask 8 = 255 := by decide

variable {Γ : Type*} [Group Γ] {V : Type*} [MulAction Γ V]

@[expose] def genSub (gens : ℕ → Γ) (ng : ℕ) : Subgroup Γ :=
  Subgroup.closure {x | ∃ j < ng, gens j = x}

@[expose] def Rep (pt : ℕ → V) (n : ℕ) (g : Γ) (t : ℕ) : Prop :=
  ∀ i < n, pg 8 255 t i < n ∧ g • pt i = pt (pg 8 255 t i)

theorem clK_spec {n w m ng N : Nat} {G T POS : Nat → Nat} {k : Nat}
    (h : clK n w m ng N G T POS k = true) :
    ∀ j < ng, r32 POS (k * ng + j) < N ∧ T (r32 POS (k * ng + j)) = pcomp n w m (G j) (T k) := by
  intro j hj
  unfold clK at h
  rw [strictB_eq] at h
  have h1 := allN_spec h j hj
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩

section Rep

variable {pt : ℕ → V} {n : ℕ}

theorem rep_one (hn : n < 255) : Rep pt n (1 : Γ) (pidn n 8) := by
  intro i hi
  have e := CFSG.KS.PF.pg_pidn (n := n) (w := 8) (by omega) (by norm_num; omega) hi
  rw [mask8] at e
  rw [e, one_smul]
  exact ⟨hi, rfl⟩

theorem rep_mul (hn : n < 255) {g h : Γ} {a b : ℕ} (hg : Rep pt n g a) (hh : Rep pt n h b) :
    Rep pt n (g * h) (pcomp n 8 255 a b) := by
  intro i hi
  have e := CFSG.KS.PF.pg_pcomp (n := n) (w := 8) (p := a) (q := b) (by omega) hi
  rw [mask8] at e
  rw [e, mul_smul, (hh i hi).2, (hg _ (hh i hi).1).2]
  exact ⟨(hg _ (hh i hi).1).1, rfl⟩

theorem eq_of_rep (hfaith : ∀ g h : Γ, (∀ i < n, g • pt i = h • pt i) → g = h) {g h : Γ}
    {t : ℕ} (hg : Rep pt n g t) (hh : Rep pt n h t) : g = h :=
  hfaith g h fun i hi => by rw [(hg i hi).2, (hh i hi).2]

end Rep

section Enum

variable {pt : ℕ → V} {n ng N : ℕ} {gens : ℕ → Γ} {G T PL POS : ℕ → ℕ}

theorem exists_rep (hn : n < 255) (hG : ∀ j < ng, Rep pt n (gens j) (G j))
    (hrec : ∀ k < N, recK n 8 255 ng G T PL k = true) :
    ∀ k < N, ∃ g ∈ genSub gens ng, Rep pt n g (T k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨h0, h1⟩ := recK_spec (hrec k hk)
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, one_mem _, by rw [h0 rfl]; exact rep_one hn⟩
    · obtain ⟨hp, hl, ht⟩ := h1 (by omega)
      obtain ⟨g, hgQ, hg⟩ := ih _ hp (by omega)
      refine ⟨gens (labOf PL k) * g, mul_mem (Subgroup.subset_closure ⟨_, hl, rfl⟩) hgQ, ?_⟩
      rw [ht]
      exact rep_mul hn (hG _ hl) hg

theorem enum_surj [Finite Γ] (hn : n < 255)
    (hfaith : ∀ g h : Γ, (∀ i < n, g • pt i = h • pt i) → g = h)
    (hG : ∀ j < ng, Rep pt n (gens j) (G j)) (hN : 0 < N)
    (hrec : ∀ k < N, recK n 8 255 ng G T PL k = true)
    (hcl : ∀ k < N, clK n 8 255 ng N G T POS k = true) {ι : ℕ → Γ}
    (hι : ∀ k < N, Rep pt n (ι k) (T k)) :
    ∀ x ∈ genSub gens ng, ∃ k < N, ι k = x := by
  have hstep : ∀ j < ng, ∀ k < N, ∃ q < N, ι q = gens j * ι k := by
    intro j hj k hk
    obtain ⟨hq, hT⟩ := clK_spec (hcl k hk) j hj
    refine ⟨_, hq, eq_of_rep hfaith (hι _ hq) ?_⟩
    rw [hT]
    exact rep_mul hn (hG j hj) (hι k hk)
  have hpow : ∀ j < ng, ∀ e : ℕ, ∀ k < N, ∃ q < N, ι q = gens j ^ e * ι k := by
    intro j hj e
    induction e with
    | zero => intro k hk; exact ⟨k, hk, by rw [pow_zero, one_mul]⟩
    | succ e ih =>
      intro k hk
      obtain ⟨q, hq, e1⟩ := ih k hk
      obtain ⟨r, hr, e2⟩ := hstep j hj q hq
      exact ⟨r, hr, by rw [e2, e1, ← mul_assoc, ← pow_succ']⟩
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one =>
    refine ⟨0, hN, eq_of_rep hfaith (hι 0 hN) ?_⟩
    rw [(recK_spec (hrec 0 hN)).1 rfl]
    exact rep_one hn
  | mul_left x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := ih
    exact hstep j hj k hk
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨q, hq, e⟩ := hpow j hj (orderOf (gens j) - 1) k hk
    refine ⟨q, hq, e.trans ?_⟩
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos (gens j)), pow_orderOf_eq_one]

theorem keyK_congr {w : Nat} {s t : Nat} :
    ∀ ps : List Nat, (∀ p ∈ ps, pg w (mask w) s p = pg w (mask w) t p) →
      CFSG.KC.BfsPin.keyK n w ps s = CFSG.KC.BfsPin.keyK n w ps t
  | [], _ => rfl
  | p :: ps, h => by
    change Nat.add (pg w (mask w) s p) (Nat.mul n (CFSG.KC.BfsPin.keyK n w ps s)) =
      Nat.add (pg w (mask w) t p) (Nat.mul n (CFSG.KC.BfsPin.keyK n w ps t))
    rw [h p List.mem_cons_self, keyK_congr ps fun q hq => h q (List.mem_cons_of_mem p hq)]

theorem enum_inj {BP SK : List ℕ} (hptinj : ∀ i < n, ∀ j < n, pt i = pt j → i = j)
    (hkeys : CFSG.KC.BfsPin.keysSK n 8 BP N T SK = true) (hBP : ∀ p ∈ BP, p < n)
    {ι : ℕ → Γ} (hι : ∀ k < N, Rep pt n (ι k) (T k)) :
    ∀ k < N, ∀ l < N, (∀ p ∈ BP, ι k • pt p = ι l • pt p) → k = l := by
  intro k hk l hl h
  refine CFSG.KC.BfsPin.keysSK_spec hkeys k hk l hl (keyK_congr BP fun p hp => ?_)
  have hk' := hι k hk p (hBP p hp)
  have hl' := hι l hl p (hBP p hp)
  rw [mask8]
  exact hptinj _ hk'.1 _ hl'.1 (by rw [← hk'.2, ← hl'.2, h p hp])

end Enum

section Card

variable {pt : ℕ → V} {n ng N : ℕ} {gens : ℕ → Γ} {ι : ℕ → Γ} {BP : List ℕ}

theorem eq_of_base (hsurj : ∀ x ∈ genSub gens ng, ∃ k < N, ι k = x)
    (hinj : ∀ k < N, ∀ l < N, (∀ p ∈ BP, ι k • pt p = ι l • pt p) → k = l) {x y : Γ}
    (hx : x ∈ genSub gens ng) (hy : y ∈ genSub gens ng) (h : ∀ p ∈ BP, x • pt p = y • pt p) :
    x = y := by
  obtain ⟨k, hk, rfl⟩ := hsurj x hx
  obtain ⟨l, hl, rfl⟩ := hsurj y hy
  rw [hinj k hk l hl h]

theorem card_genSub (hmem : ∀ k < N, ι k ∈ genSub gens ng)
    (hsurj : ∀ x ∈ genSub gens ng, ∃ k < N, ι k = x)
    (hinj : ∀ k < N, ∀ l < N, ι k = ι l → k = l) : Nat.card (genSub gens ng) = N := by
  have hb : Function.Bijective fun k : Fin N => (⟨ι k, hmem k k.2⟩ : genSub gens ng) := by
    refine ⟨fun a b e => Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨k, hk, e⟩ := hsurj x x.2
    exact ⟨⟨k, hk⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

end Card

end CFSG.KS.HNT0

end
