module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

public section

namespace CFSG.Certificates.ThDemp.Chain

open Finset

variable {G α : Type*} [Group G]

structure ChainHyp (act : α → G → α) (L n : ℕ) (fr N : ℕ → ℕ) (b : ℕ → α) (s : ℕ → G)
    (O : ℕ → ℕ → α) (t : ℕ → ℕ → G) : Prop where
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x g h, act x (g * h) = act (act x g) h
  frL : fr L = n
  mono : ∀ l < L, fr l ≤ fr (l + 1)
  pos : ∀ l < L, 0 < N l
  t0 : ∀ l < L, t l 0 = 1
  O0 : ∀ l < L, O l 0 = b l
  tmem : ∀ l < L, ∀ i < N l, t l i ∈ Subgroup.closure {x | ∃ g, fr l ≤ g ∧ g < n ∧ x = s g}
  tpt : ∀ l < L, ∀ i < N l, act (b l) (t l i) = O l i
  inj : ∀ l < L, ∀ i j, i < N l → j < N l → O l i = O l j → i = j
  fix : ∀ l < L, ∀ g, fr (l + 1) ≤ g → g < n → act (b l) (s g) = b l
  res : ∀ l < L, ∀ i < N l, ∀ g, fr l ≤ g → g < n → ∃ z < N l,
    t l i * s g * (t l z)⁻¹ ∈ Subgroup.closure {x | ∃ g, fr (l + 1) ≤ g ∧ g < n ∧ x = s g}

variable {act : α → G → α} {L n : ℕ} {fr N : ℕ → ℕ} {b : ℕ → α} {s : ℕ → G}
  {O : ℕ → ℕ → α} {t : ℕ → ℕ → G}

@[expose] def lev (fr : ℕ → ℕ) (n : ℕ) (s : ℕ → G) (l : ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ g, fr l ≤ g ∧ g < n ∧ x = s g}

namespace ChainHyp

variable (H : ChainHyp act L n fr N b s O t)
include H

theorem lev_succ_le {l : ℕ} (hl : l < L) : lev fr n s (l + 1) ≤ lev fr n s l := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨g, hg1, hg2, rfl⟩
  exact ⟨g, (H.mono l hl).trans hg1, hg2, rfl⟩

theorem act_inv (x : α) (g : G) : act (act x g) g⁻¹ = x := by
  rw [← H.act_mul, mul_inv_cancel, H.act_one]

theorem fix_lev {l : ℕ} (hl : l < L) {h : G} (hh : h ∈ lev fr n s (l + 1)) :
    act (b l) h = b l := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg1, hg2, rfl⟩ := hx
    exact H.fix l hl g hg1 hg2
  | one => exact H.act_one _
  | mul x y _ _ hx hy => rw [H.act_mul, hx, hy]
  | inv x _ hx =>
    have e := H.act_inv (b l) x
    rw [hx] at e
    exact e

theorem act_ht {l : ℕ} (hl : l < L) {h : G} (hh : h ∈ lev fr n s (l + 1)) {z : ℕ}
    (hz : z < N l) : act (b l) (h * t l z) = O l z := by
  rw [H.act_mul, H.fix_lev hl hh, H.tpt l hl z hz]

theorem res_unique {l : ℕ} (hl : l < L) {i g z z' : ℕ} (hz : z < N l) (hz' : z' < N l)
    (h1 : t l i * s g * (t l z)⁻¹ ∈ lev fr n s (l + 1))
    (h2 : t l i * s g * (t l z')⁻¹ ∈ lev fr n s (l + 1)) : z = z' := by
  have e1 := H.act_ht hl h1 hz
  have e2 := H.act_ht hl h2 hz'
  rw [inv_mul_cancel_right] at e1 e2
  exact H.inj l hl z z' hz hz' (e1.symm.trans e2)

theorem decomp {l : ℕ} (hl : l < L) {x : G} (hx : x ∈ lev fr n s l) :
    ∃ h ∈ lev fr n s (l + 1), ∃ z < N l, x = h * t l z := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨1, Subgroup.one_mem _, 0, H.pos l hl, by rw [H.t0 l hl, one_mul]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨g, hg1, hg2, rfl⟩ := hy
    obtain ⟨h, hh, z, hz, rfl⟩ := ih
    obtain ⟨z', hz', hres⟩ := H.res l hl z hz g hg1 hg2
    refine ⟨h * (t l z * s g * (t l z')⁻¹), Subgroup.mul_mem _ hh hres, z', hz', ?_⟩
    group
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨g, hg1, hg2, rfl⟩ := hy
    obtain ⟨h, hh, z, hz, rfl⟩ := ih
    have hex : ∀ i : Fin (N l), ∃ z' : Fin (N l),
        t l i * s g * (t l z')⁻¹ ∈ lev fr n s (l + 1) := by
      intro i
      obtain ⟨z', hz', hr⟩ := H.res l hl i i.isLt g hg1 hg2
      exact ⟨⟨z', hz'⟩, hr⟩
    choose f hf using hex
    have finj : Function.Injective f := by
      intro i j e
      have ei := H.act_ht hl (hf i) (f i).isLt
      have ej := H.act_ht hl (hf j) (f j).isLt
      rw [inv_mul_cancel_right, H.act_mul, H.tpt l hl i i.isLt] at ei
      rw [inv_mul_cancel_right, H.act_mul, H.tpt l hl j j.isLt] at ej
      rw [e] at ei
      have e2 : O l i = O l j := by
        have := congrArg (fun y => act y (s g)⁻¹) (ei.trans ej.symm)
        simpa only [H.act_inv] using this
      exact Fin.ext (H.inj l hl i j i.isLt j.isLt e2)
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 finj) ⟨z, hz⟩
    have hr := hf i
    rw [hi] at hr
    refine ⟨h * (t l i * s g * (t l z)⁻¹)⁻¹, Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hr), i,
      i.isLt, ?_⟩
    group

theorem card_lev {l : ℕ} (hl : l < L) :
    Nat.card (lev fr n s l) = Nat.card (lev fr n s (l + 1)) * N l := by
  have hle := H.lev_succ_le hl
  let φ : lev fr n s (l + 1) × Fin (N l) → lev fr n s l := fun p =>
    ⟨p.1 * t l p.2, Subgroup.mul_mem _ (hle p.1.2) (H.tmem l hl p.2 p.2.isLt)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨h, z⟩ ⟨h', z'⟩ e
      have e' : h.1 * t l z = h'.1 * t l z' := congrArg Subtype.val e
      have hz : (z : ℕ) = z' := by
        have a1 := H.act_ht hl h.2 z.isLt
        have a2 := H.act_ht hl h'.2 z'.isLt
        rw [e'] at a1
        exact H.inj l hl z z' z.isLt z'.isLt (a1.symm.trans a2)
      have hz' : z = z' := Fin.ext hz
      subst hz'
      have hh : h = h' := Subtype.ext (mul_right_cancel e')
      rw [hh]
    · rintro ⟨x, hx⟩
      obtain ⟨h, hh, z, hz, rfl⟩ := H.decomp hl hx
      exact ⟨(⟨h, hh⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Fin (N l)), Fintype.card_fin]

theorem lev_L : lev fr n s L = ⊥ := by
  rw [lev, eq_bot_iff, Subgroup.closure_le]
  rintro x ⟨g, hg1, hg2, -⟩
  rw [H.frL] at hg1
  omega

theorem card_lev_eq : ∀ l ≤ L, Nat.card (lev fr n s l) = ∏ k ∈ Ico l L, N k := by
  intro l hl
  induction h : L - l generalizing l with
  | zero =>
    have e : l = L := by omega
    subst e
    rw [H.lev_L, Subgroup.card_bot, Ico_self, prod_empty]
  | succ m ih =>
    have hlL : l < L := by omega
    rw [H.card_lev hlL, ih (l + 1) hlL (by omega), prod_eq_prod_Ico_succ_bot hlL, mul_comm]

theorem card_lev_zero : Nat.card (lev fr n s 0) = ∏ k ∈ range L, N k := by
  rw [H.card_lev_eq 0 (Nat.zero_le _), range_eq_Ico]

end ChainHyp

end CFSG.Certificates.ThDemp.Chain

end
