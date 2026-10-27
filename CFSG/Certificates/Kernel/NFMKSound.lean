module

public import Certificates.Data.Kernel.NFMK
public import CFSG.Certificates.Kernel.HSMKSound
public import CFSG.Certificates.Kernel.PCentCheck
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
import all CFSG.Certificates.Kernel.WEMKSound
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CFSG.StandardType.ZS.NFMK

open Certificates.WEMK Certificates.HSMK Certificates.NFMK CFSG.KC.PCent CFSG.StandardType.ZS.WEMK
open CFSG.StandardType.ZS.HSMK CFSG.StandardType.ZS Certificates.ExcModel

theorem commute_of_inf_bot {G : Type*} [Group G] {N E : Subgroup G} [N.Normal] [E.Normal] (h : N ⊓ E = ⊥)
    {x : G} (hx : x ∈ N) {e : G} (he : e ∈ E) : Commute x e := by
  have hN : x * e * x⁻¹ * e⁻¹ ∈ N := by
    have h1 : e * x⁻¹ * e⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ (inv_mem hx) e
    have h2 := mul_mem hx h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  have hE : x * e * x⁻¹ * e⁻¹ ∈ E :=
    mul_mem (Subgroup.Normal.conj_mem inferInstance _ he x) (inv_mem he)
  have hb : x * e * x⁻¹ * e⁻¹ ∈ N ⊓ E := ⟨hN, hE⟩
  rw [h, Subgroup.mem_bot] at hb
  have h3 : x * e * x⁻¹ = e := mul_inv_eq_one.mp hb
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem exists_central_of_normal {G : Type*} [Group G] (E : Subgroup G) [E.Normal] [Finite E]
    (h4 : ∀ e ∈ E, e ^ 4 = 1) (P : G → Prop) (hP : ∀ g, (∀ e ∈ E, Commute g e) → P g)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : ∃ c ∈ N, c ≠ 1 ∧ P c := by
  by_cases h : N ⊓ E = ⊥
  · obtain ⟨x, hx, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hN ((Subgroup.eq_bot_iff_forall N).mpr hc)
    exact ⟨x, hx, hx1, hP x fun e he => commute_of_inf_bot h hx he⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 E := fun g => ⟨2, by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      exact h4 g g.2⟩
    have : Group.IsNilpotent E := h2.isNilpotent
    have hK : (N.subgroupOf E).Normal := inferInstance
    have hK0 : N.subgroupOf E ≠ ⊥ := by
      intro hb
      apply h
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : E) ∈ N.subgroupOf E := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.1
      rw [hb, Subgroup.mem_bot] at hx'
      exact congrArg Subtype.val hx'
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hK0
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ N.subgroupOf E ⊓ Subgroup.center E, y ≠ 1 := by
      by_contra hc'
      push Not at hc'
      exact hc ((Subgroup.eq_bot_iff_forall _).mpr hc')
    refine ⟨y, (Subgroup.mem_subgroupOf).mp hy.1, fun e => hy1 (Subtype.ext e), hP _ fun e he => ?_⟩
    have := Subgroup.mem_center_iff.mp hy.2 ⟨e, he⟩
    exact (congrArg Subtype.val this).symm

theorem scalar_cases : ∀ c : ZMod 13, (c ^ 4) ^ 2 = 1 → c ≠ 1 → c = -1 ∨ c ^ 2 = -1 := by
  decide

theorem scalar_of_commute_span {n : ℕ} (A : Mat n) (M : Set (Mat n))
    (hspan : ∀ i j : Fin n, Matrix.single i j (1 : ZMod 13) ∈ Submodule.span (ZMod 13) M)
    (hA : ∀ m ∈ M, Commute A m) : A ∈ Set.range (Matrix.scalar (Fin n)) := by
  rw [Matrix.mem_range_scalar_iff_commute_single']
  intro i j
  have hs := hspan i j
  refine (Submodule.span_induction (p := fun x _ => Commute x A) ?_ ?_ ?_ ?_ hs)
  · intro m hm
    exact (hA m hm).symm
  · exact Commute.zero_left A
  · intro x y _ _ hx hy
    exact hx.add_left hy
  · intro c x _ hx
    exact hx.smul_left c

theorem orderOf_le_of_class {G : Type*} [Group G] (t : G) (V : Set G) (hV : ∀ g, IsConj t g → g ∈ V)
    (hP : ∀ r ∈ V, ∃ e, 0 < e ∧ e ≤ 4 ∧ (t * r) ^ e = 1) (g h : G) (hg : IsConj t g) (hh : IsConj t h) :
    orderOf (g * h) ≤ 4 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  obtain ⟨d, rfl⟩ := isConj_iff.mp hh
  set r := (c⁻¹ * d) * t * (c⁻¹ * d)⁻¹
  have hr : r ∈ V := hV r (isConj_iff.mpr ⟨c⁻¹ * d, rfl⟩)
  have he : c * t * c⁻¹ * (d * t * d⁻¹) = c * (t * r) * c⁻¹ := by
    simp only [r]
    group
  obtain ⟨e, he0, he4, hpow⟩ := hP r hr
  rw [he]
  have hc : orderOf (c * (t * r) * c⁻¹) = orderOf (t * r) := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective (t * r)
    simpa [MulAut.conj_apply] using this
  rw [hc]
  exact (orderOf_le_of_pow_eq_one he0 hpow).trans he4

def Forms {G : Type*} [Group G] (t z g : G) : Prop :=
  g = 1 ∨ IsConj t g ∨ IsConj t (z * g) ∨ (∃ a b, IsConj t a ∧ IsConj t b ∧ g = a * b) ∨
    ∃ a b, IsConj t a ∧ IsConj t b ∧ g = z * (a * b)

theorem forms_conj {G : Type*} [Group G] (t z : G) (hz : ∀ x, Commute z x) (x g : G) (h : Forms t z g) :
    Forms t z (x * g * x⁻¹) := by
  have hc : ∀ a, IsConj t a → IsConj t (x * a * x⁻¹) := fun a ha =>
    ha.trans (isConj_iff.mpr ⟨x, rfl⟩)
  rcases h with rfl | h | h | ⟨a, b, ha, hb, rfl⟩ | ⟨a, b, ha, hb, rfl⟩
  · left
    group
  · exact Or.inr (Or.inl (hc g h))
  · refine Or.inr (Or.inr (Or.inl ?_))
    have e : z * (x * g * x⁻¹) = x * (z * g) * x⁻¹ := by
      rw [show x * (z * g) * x⁻¹ = (x * z) * g * x⁻¹ by group, ← (hz x).eq]
      group
    rw [e]
    exact hc _ h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨x * a * x⁻¹, x * b * x⁻¹, hc a ha, hc b hb, by group⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨x * a * x⁻¹, x * b * x⁻¹, hc a ha, hc b hb, ?_⟩)))
    rw [show x * (z * (a * b)) * x⁻¹ = (x * z) * (a * b) * x⁻¹ by group, ← (hz x).eq]
    group

theorem cover_of_table {G : Type*} [Group G] (E : Subgroup G) [E.Normal] (S : Set G)
    (hS : Subgroup.closure S = ⊤) (hinv : ∀ s ∈ S, s * s = 1) (C : ℕ → G) (nC : ℕ) (h0 : 0 < nC) (hC0 : C 0 = 1)
    (hT : ∀ i < nC, ∀ s ∈ S, ∃ j < nC, ∃ e ∈ E, C i * s = C j * e) :
    ∀ g : G, ∃ i < nC, ∃ e ∈ E, g = C i * e := by
  have hstep : ∀ g : G, (∃ i < nC, ∃ e ∈ E, g = C i * e) → ∀ s ∈ S, ∃ i < nC, ∃ e ∈ E, g * s = C i * e := by
    rintro g ⟨i, hi, e, he, rfl⟩ s hs
    obtain ⟨j, hj, f, hf, hjf⟩ := hT i hi s hs
    have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hinv s hs)
    refine ⟨j, hj, f * (s⁻¹ * e * s), mul_mem hf ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem inferInstance e he s⁻¹
      rwa [inv_inv] at this
    · calc C i * e * s = C i * s * (s⁻¹ * e * s) := by group
        _ = C j * (f * (s⁻¹ * e * s)) := by rw [hjf]; group
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, h0, 1, one_mem _, by rw [hC0, mul_one]⟩
  | mul_right x _ s hs ih => exact hstep x ih s hs
  | mul_inv_cancel x _ s hs ih =>
    have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hinv s hs)
    rw [hss]
    exact hstep x ih s hs

theorem sq_mem_of_invol {G : Type*} [Group G] (E : Subgroup G) [E.Normal] (c e : G) (he : e ∈ E)
    (h : c * e * (c * e) = 1) : c * c ∈ E := by
  have hc : c⁻¹ * e * c ∈ E := by
    have := Subgroup.Normal.conj_mem inferInstance e he c⁻¹
    rwa [inv_inv] at this
  have h2 : c * c = (c * e * (c * e)) * ((c⁻¹ * e * c) * e)⁻¹ := by group
  rw [h2, h, one_mul]
  exact inv_mem (mul_mem hc he)

theorem forms_of_tree {G : Type*} [Group G] (E : Subgroup G) [E.Normal] (t z : G) (hz : ∀ x, Commute z x)
    (C : ℕ → G) (nC : ℕ) (hcov : ∀ g : G, ∃ i < nC, ∃ e ∈ E, g = C i * e) (F : ℕ → Prop) (d : ℕ → ℕ)
    (hF : ∀ i < nC, C i * C i ∈ E → F i)
    (hstep : ∀ i < nC, F i → 0 < d i → ∃ s : G, s * s = 1 ∧ ∃ c < nC, F c ∧ d c < d i ∧ ∃ e ∈ E, s * C i * s = C c * e)
    (hroot : ∀ i < nC, F i → d i = 0 → ∀ e ∈ E, C i * e * (C i * e) = 1 → Forms t z (C i * e)) :
    ∀ g : G, g * g = 1 → Forms t z g := by
  have key : ∀ m, ∀ i < nC, F i → d i ≤ m → ∀ e ∈ E, C i * e * (C i * e) = 1 → Forms t z (C i * e) := by
    intro m
    induction m with
    | zero =>
      intro i hi hFi hd e he hinv
      exact hroot i hi hFi (Nat.le_zero.mp hd) e he hinv
    | succ m ih =>
      intro i hi hFi hd e he hinv
      rcases Nat.eq_zero_or_pos (d i) with h0 | hpos
      · exact hroot i hi hFi h0 e he hinv
      obtain ⟨s, hs, c, hc, hFc, hdc, f, hf, hsc⟩ := hstep i hi hFi hpos
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      have hses : s * e * s ∈ E := by
        have := Subgroup.Normal.conj_mem inferInstance e he s
        rwa [hsi] at this
      have hconj : s * (C i * e) * s = C c * (f * (s * e * s)) := by
        calc s * (C i * e) * s = (s * C i * s) * (s * e * s) := by
              rw [show (s * C i * s) * (s * e * s) = s * C i * (s * s) * e * s by group, hs]
              group
          _ = C c * (f * (s * e * s)) := by rw [hsc]; group
      have hinv' : C c * (f * (s * e * s)) * (C c * (f * (s * e * s))) = 1 := by
        rw [← hconj]
        calc s * (C i * e) * s * (s * (C i * e) * s) = s * (C i * e) * (s * s) * (C i * e) * s := by group
          _ = 1 := by rw [hs, mul_one, mul_assoc s, hinv, mul_one, hs]
      have hF' := ih c hc hFc (by omega) _ (mul_mem hf hses) hinv'
      rw [← hconj] at hF'
      have := forms_conj t z hz s _ hF'
      rwa [hsi, show s * (s * (C i * e) * s) * s = (s * s) * (C i * e) * (s * s) by group, hs, one_mul,
        mul_one] at this
  intro g hg
  obtain ⟨i, hi, e, he, rfl⟩ := hcov g
  have hsq := sq_mem_of_invol E (C i) e he hg
  exact key (d i) i hi (hF i hi hsq) le_rfl e he hg

theorem tree_mem {M : Type*} [Monoid M] (f : ℕ → M) (Y : Set M) (N : ℕ) (h0 : f 0 = 1)
    (hp : ∀ k < N, k ≠ 0 → ∃ p < k, ∃ y ∈ Y, f k = f p * y) : ∀ k < N, f k ∈ Submonoid.closure Y := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [h0]
      exact one_mem _
    obtain ⟨p, hpk, y, hy, he⟩ := hp k hk (by omega)
    rw [he]
    exact mul_mem (ih p hpk (by omega)) (Submonoid.subset_closure hy)

theorem closure_sub {M : Type*} [Monoid M] (L Y : Set M) (h1 : 1 ∈ L) (hcl : ∀ x ∈ L, ∀ y ∈ Y, x * y ∈ L) :
    (Submonoid.closure Y : Set M) ⊆ L := by
  intro z hz
  induction hz using Submonoid.closure_induction_right with
  | one => exact h1
  | mul_right x _ y hy ih => exact hcl x ih y hy

theorem zip_all_getD {α β : Type*} {f : α × β → Bool} {l₁ : List α} {l₂ : List β}
    (h : (List.zip l₁ l₂).all f = true) (hl : l₁.length = l₂.length) (d₁ : α) (d₂ : β) {i : ℕ}
    (hi : i < l₁.length) : f (l₁.getD i d₁, l₂.getD i d₂) = true := by
  have hi' : i < (List.zip l₁ l₂).length := by
    rw [List.length_zip]
    omega
  have := List.all_eq_true.mp h _ (List.getElem_mem hi')
  rw [List.getElem_zip] at this
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]

theorem zip_range_all {β : Type*} {f : ℕ × β → Bool} {m : ℕ} {l : List β}
    (h : (List.zip (List.range m) l).all f = true) (hl : l.length = m) (d : β) {i : ℕ} (hi : i < m) :
    f (i, l.getD i d) = true := by
  have := zip_all_getD h (by simp [hl]) 0 d (by simpa using hi)
  rwa [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_range] at this

theorem zip_getD {α β : Type*} (l₁ : List α) (l₂ : List β) (d₁ : α) (d₂ : β) {i : ℕ} (h₁ : i < l₁.length)
    (h₂ : i < l₂.length) : (List.zip l₁ l₂).getD i (d₁, d₂) = (l₁.getD i d₁, l₂.getD i d₂) := by
  rw [List.getD_eq_getElem _ _ (by simp [h₁, h₂]), List.getElem_zip, List.getD_eq_getElem _ _ h₁,
    List.getD_eq_getElem _ _ h₂]

theorem wf_of_wfM {n : ℕ} {A : NMat} (h : wfM n A = true) : WF n A := by
  simp only [wfM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem foldl_word {n : ℕ} {S : List NMat} (hS : ∀ s ∈ S, WF n s) :
    ∀ (w : List ℕ) (x : NMat), Red n x → (∀ s ∈ w, s < S.length) →
      Red n (w.foldl (fun x s => nmul n x (S.getD s [])) x) ∧
      toM n (w.foldl (fun x s => nmul n x (S.getD s [])) x) =
        toM n x * (w.map fun s => toM n (S.getD s [])).prod
  | [], x, hx, _ => ⟨hx, by simp⟩
  | s :: w, x, hx, hw => by
    have hs : WF n (S.getD s []) := hS _ (getD_mem_of_lt (hw s (by simp)))
    obtain ⟨h1, h2⟩ := foldl_word hS w (nmul n x (S.getD s [])) (wf_nmul n _ _ hx.1.1 hs)
      (fun t ht => hw t (by simp [ht]))
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    refine ⟨h1, ?_⟩
    rw [h2, toM_nmul n _ _ hx.1.1 hs, mul_assoc]

theorem toM_wordN {n : ℕ} {S : List NMat} (hS : ∀ s ∈ S, WF n s) (w : List ℕ) (hw : ∀ s ∈ w, s < S.length) :
    toM n (wordN n S w) = (w.map fun s => toM n (S.getD s [])).prod := by
  rw [wordN, (foldl_word hS w (idN n) (wf_idN n) hw).2, idN_spec, one_mul]

theorem wf_scalN (n c : ℕ) : WF n (scalN n c) := by
  refine ⟨by simp [scalN], ?_⟩
  intro r hr
  simp only [scalN, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp

theorem scalN_spec (n c : ℕ) : toM n (scalN n c) = Matrix.scalar (Fin n) (c : ZMod 13) := by
  ext i j
  rw [toM_apply]
  simp only [scalN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2,
    List.getElem?_range j.2, Option.map_some, Option.getD_some, Matrix.scalar_apply, Matrix.diagonal_apply,
    Fin.ext_iff]
  split_ifs <;> simp

theorem unitN_spec (n : ℕ) (i j : Fin n) : toM n (unitN n (n * i + j)) = Matrix.single i j (1 : ZMod 13) := by
  ext a b
  rw [toM_apply]
  simp only [unitN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range a.2,
    List.getElem?_range b.2, Option.map_some, Option.getD_some, Matrix.single_apply]
  have key : n * (a : ℕ) + b = n * i + j ↔ i = a ∧ j = b := by
    constructor
    · intro h
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) b.2
      have h1 := congrArg (· / n) h
      have h2 := congrArg (· % n) h
      simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt b.2, Nat.div_eq_of_lt j.2, Nat.mul_add_mod,
        Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt j.2, Nat.add_zero] at h1 h2
      exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  by_cases hab : i = a ∧ j = b
  · rw [if_pos (key.mpr hab), if_pos hab]
    simp
  · rw [if_neg (fun h => hab (key.mp h)), if_neg hab]
    simp

theorem toM_maddN {n : ℕ} (c : ℕ) {A B : NMat} (hA : WF n A) (hB : WF n B) :
    WF n (maddN c A B) ∧ toM n (maddN c A B) = (c : ZMod 13) • toM n A + toM n B := by
  constructor
  · refine ⟨by simp [maddN, hA.1, hB.1], ?_⟩
    intro r hr
    simp only [maddN, List.mem_iff_getElem, List.length_zipWith, List.getElem_zipWith] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    simp [hA.2 _ (List.getElem_mem _), hB.2 _ (List.getElem_mem _)]
  · ext i j
    have hi : (i : ℕ) < A.length := by rw [hA.1]; exact i.2
    have hi' : (i : ℕ) < B.length := by rw [hB.1]; exact i.2
    have hra := hA.2 _ (List.getElem_mem hi)
    have hrb := hB.2 _ (List.getElem_mem hi')
    have hj : (j : ℕ) < A[(i : ℕ)].length := by rw [hra]; exact j.2
    have hj' : (j : ℕ) < B[(i : ℕ)].length := by rw [hrb]; exact j.2
    have hl : (i : ℕ) < (maddN c A B).length := by simp [maddN, hA.1, hB.1]
    have hr : (maddN c A B)[(i : ℕ)] = List.zipWith (fun x y => (c * x + y) % 13) A[(i : ℕ)] B[(i : ℕ)] := by
      simp [maddN]
    have hl2 : (j : ℕ) < (maddN c A B)[(i : ℕ)].length := by
      rw [hr]
      simp [hra, hrb]
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, toM_apply, toM_apply, toM_apply,
      List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl2, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
    simp only [hr, List.getElem_zipWith]
    push_cast [ZMod.natCast_mod]
    ring

theorem lcombN_mem {n : ℕ} (Z : NMat) (hZ : WF n Z) (hZ0 : toM n Z = 0) (P : Submodule (ZMod 13) (Mat n)) :
    ∀ (cs : List ℕ) (Ms : List NMat), (∀ M ∈ Ms, WF n M ∧ toM n M ∈ P) →
      WF n (lcombN Z cs Ms) ∧ toM n (lcombN Z cs Ms) ∈ P
  | [], _, _ => ⟨hZ, by
      change toM n Z ∈ P
      rw [hZ0]
      exact P.zero_mem⟩
  | _ :: _, [], _ => ⟨hZ, by
      change toM n Z ∈ P
      rw [hZ0]
      exact P.zero_mem⟩
  | c :: cs, M :: Ms, hM => by
    obtain ⟨h1, h2⟩ := lcombN_mem Z hZ hZ0 P cs Ms (fun M' h' => hM M' (by simp [h']))
    obtain ⟨hw, he⟩ := hM M (by simp)
    obtain ⟨w, e⟩ := toM_maddN c hw h1
    rw [lcombN]
    exact ⟨w, by rw [e]; exact P.add_mem (P.smul_mem _ he) h2⟩

theorem el_sound {n : ℕ} {S E : List NMat} {Yi : List ℕ} {YW ET EN : List (List ℕ)} {Ep : List (ℕ × ℕ)}
    (h : kEl n S E (treeOf E) Yi YW ET EN Ep = true) (hS : ∀ s ∈ S, WF n s) :
    0 < E.length ∧ toM n (E.getD 0 []) = 1 ∧
    (∀ k < E.length, Red n (E.getD k []) ∧ toM n (E.getD k []) ^ 4 = 1) ∧
    (∀ y < Yi.length, Yi.getD y 0 < E.length ∧ (∀ s ∈ YW.getD y [], s < S.length) ∧
      toM n (E.getD (Yi.getD y 0) []) = ((YW.getD y []).map fun s => toM n (S.getD s [])).prod) ∧
    (∀ k < E.length, ∀ y < Yi.length, ∃ k' < E.length,
      toM n (E.getD k []) * toM n (E.getD (Yi.getD y 0) []) = toM n (E.getD k' [])) ∧
    (∀ k < E.length, k ≠ 0 → ∃ p < k, ∃ y < Yi.length,
      toM n (E.getD k []) = toM n (E.getD p []) * toM n (E.getD (Yi.getD y 0) [])) ∧
    (∀ s < S.length, ∀ y < Yi.length, ∃ k' < E.length,
      toM n (S.getD s []) * toM n (E.getD (Yi.getD y 0) []) * toM n (S.getD s []) = toM n (E.getD k' [])) := by
  simp only [kEl, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hwf⟩, h4⟩, hYl⟩, hYW⟩, hETl⟩, hET⟩, hEpl⟩, hEp⟩, hENl⟩, hEN⟩ := h
  have gT : ∀ i, getT (treeOf E) i = E.getD i [] := fun i => getT_treeOf E i
  have hE0 : 0 < E.length ∧ E.getD 0 [] = idN n := by
    cases E with
    | nil => simp at h0
    | cons a l => simpa using h0
  have hWE : ∀ k < E.length, WF n (E.getD k []) := fun k hk =>
    wf_of_wfM (List.all_eq_true.mp hwf _ (getD_mem_of_lt hk))
  have hWS : ∀ s < S.length, WF n (S.getD s []) := fun s hs => hS _ (getD_mem_of_lt hs)
  have hrow : ∀ k < E.length, ∀ y < Yi.length, (ET.getD k []).getD y 0 < E.length ∧
      nmul n (E.getD k []) (E.getD (Yi.getD y 0) []) = E.getD ((ET.getD k []).getD y 0) [] := by
    intro k hk y hy
    have r := zip_all_getD hET hETl.symm [] [] hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at r
    have q := zip_all_getD r.2 r.1.symm 0 0 hy
    simp only [Bool.and_eq_true, decide_eq_true_eq, gT] at q
    exact q
  have hYrow : ∀ y < Yi.length, Yi.getD y 0 < E.length ∧ (∀ s ∈ YW.getD y [], s < S.length) ∧
      wordN n S (YW.getD y []) = E.getD (Yi.getD y 0) [] := by
    intro y hy
    have r := zip_all_getD hYW hYl 0 [] hy
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, gT] at r
    exact ⟨r.1.1, r.1.2, r.2⟩
  have hpar : ∀ k < E.length, k ≠ 0 → ∃ p < k, ∃ y < Yi.length,
      nmul n (E.getD p []) (E.getD (Yi.getD y 0) []) = E.getD k [] := by
    intro k hk hk0
    have r := zip_range_all hEp hEpl (0, 0) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at r
    rcases r with r | ⟨⟨hp, hy⟩, he⟩
    · exact absurd r hk0
    · refine ⟨_, hp, _, hy, ?_⟩
      have := (hrow (Ep.getD k (0, 0)).1 (by omega) _ hy).2
      rwa [he] at this
  have hRE : ∀ k < E.length, Red n (E.getD k []) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [hE0.2]
      exact wf_idN n
    · obtain ⟨p, hp, y, hy, he⟩ := hpar k hk hk0
      rw [← he]
      exact wf_nmul n _ _ (hWE p (by omega)).1 (hWE _ (hYrow y hy).1)
  have hpow : ∀ k < E.length, toM n (E.getD k []) ^ 4 = 1 := by
    intro k hk
    have i := List.all_eq_true.mp h4 _ (getD_mem_of_lt (d := []) hk)
    have w := hWE k hk
    have w2 := wf_nmul n _ _ w.1 w
    rw [← isOneN_sound i, toM_nmul n _ _ w2.1.1 w2.1, toM_nmul n _ _ w.1 w]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨hE0.1, by rw [hE0.2, idN_spec], fun k hk => ⟨hRE k hk, hpow k hk⟩, fun y hy => ?_,
    fun k hk y hy => ?_, fun k hk hk0 => ?_, fun s hs y hy => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hYrow y hy
    exact ⟨h1, h2, by rw [← h3, toM_wordN hS _ h2]⟩
  · obtain ⟨h1, h2⟩ := hrow k hk y hy
    exact ⟨_, h1, by rw [← h2, toM_nmul n _ _ (hWE k hk).1 (hWE _ (hYrow y hy).1)]⟩
  · obtain ⟨p, hp, y, hy, he⟩ := hpar k hk hk0
    exact ⟨p, hp, y, hy, by rw [← he, toM_nmul n _ _ (hWE p (by omega)).1 (hWE _ (hYrow y hy).1)]⟩
  · have r := zip_all_getD hEN hENl.symm [] [] hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at r
    have q := zip_all_getD r.2 r.1.symm 0 0 hy
    simp only [Bool.and_eq_true, decide_eq_true_eq, gT] at q
    have ws := hWS s hs
    have wy := hWE _ (hYrow y hy).1
    refine ⟨_, q.1, ?_⟩
    rw [← q.2, toM_nmul n _ _ (wf_nmul n _ _ ws.1 wy).1.1 ws, toM_nmul n _ _ ws.1 wy]

theorem span_sound {n : ℕ} {E : List NMat} {B : List ℕ} {CF : List (List ℕ)}
    (h : kSpan n E (treeOf E) B CF = true) (hE : ∀ k < E.length, Red n (E.getD k [])) :
    ∀ i j : Fin n, Matrix.single i j (1 : ZMod 13) ∈
      Submodule.span (ZMod 13) ((fun k => toM n (E.getD k [])) '' {k | k < E.length}) := by
  simp only [kSpan, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hB⟩, hCl⟩, hCF⟩ := h
  intro i j
  have hu : n * (i : ℕ) + j < n * n := by
    calc n * (i : ℕ) + j < n * i + n := by have := j.2; omega
      _ = n * (i + 1) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left _ i.2
  have r := zip_range_all hCF hCl [] hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at r
  rw [← unitN_spec, ← r.2]
  refine (lcombN_mem (scalN n 0) (wf_scalN n 0) (by rw [scalN_spec, Nat.cast_zero, map_zero]) _ _ _ ?_).2
  intro M hM
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hM
  have hb' := of_decide_eq_true (List.all_eq_true.mp hB b hb)
  rw [getT_treeOf]
  exact ⟨(hE b hb').1, Submodule.subset_span ⟨b, hb', rfl⟩⟩

theorem words_sound {n : ℕ} {S : List NMat} {ZW IW : List ℕ} (h : kWords n S ZW IW = true) (hS : ∀ s ∈ S, WF n s) :
    (∀ s ∈ ZW, s < S.length) ∧ (∀ s ∈ IW, s < S.length) ∧
    (ZW.map fun s => toM n (S.getD s [])).prod = Matrix.scalar (Fin n) (-1 : ZMod 13) ∧
    (IW.map fun s => toM n (S.getD s [])).prod = Matrix.scalar (Fin n) (5 : ZMod 13) := by
  simp only [kWords, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hZ, hI⟩, hz⟩, hi⟩ := h
  refine ⟨hZ, hI, ?_, ?_⟩
  · have h12 : ((12 : ℕ) : ZMod 13) = -1 := by decide
    rw [← toM_wordN hS _ hZ, hz, scalN_spec, h12]
  · rw [← toM_wordN hS _ hI, hi, scalN_spec, Nat.cast_ofNat]

theorem cos_sound {n : ℕ} {S E C : List NMat} {CT : List (List (ℕ × ℕ))} {CP : List (ℕ × ℕ)}
    (h : kCos n S E C (treeOf C) (treeOf E) CT CP = true) (hS : ∀ s ∈ S, WF n s)
    (hE : ∀ k < E.length, WF n (E.getD k [])) (hE0 : toM n (E.getD 0 []) = 1) :
    0 < C.length ∧ toM n (C.getD 0 []) = 1 ∧ (∀ i < C.length, WF n (C.getD i [])) ∧
    (∀ i < C.length, ∀ s < S.length, ∃ j < C.length, ∃ k < E.length,
      toM n (C.getD i []) * toM n (S.getD s []) = toM n (C.getD j []) * toM n (E.getD k [])) ∧
    ∀ i < C.length, i ≠ 0 → ∃ p < i, ∃ s < S.length, toM n (C.getD i []) = toM n (C.getD p []) * toM n (S.getD s []) := by
  simp only [kCos, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, hwf⟩, hCTl⟩, hCT⟩, hCPl⟩, hCP⟩ := h
  have gC : ∀ i, getT (treeOf C) i = C.getD i [] := fun i => getT_treeOf C i
  have gE : ∀ i, getT (treeOf E) i = E.getD i [] := fun i => getT_treeOf E i
  have hC0 : 0 < C.length ∧ C.getD 0 [] = idN n := by
    cases C with
    | nil => simp at h0
    | cons a l => simpa using h0
  have hWC : ∀ i < C.length, WF n (C.getD i []) := fun i hi =>
    wf_of_wfM (List.all_eq_true.mp hwf _ (getD_mem_of_lt hi))
  have hWS : ∀ s < S.length, WF n (S.getD s []) := fun s hs => hS _ (getD_mem_of_lt hs)
  have hrow : ∀ i < C.length, ∀ s < S.length, ((CT.getD i []).getD s (0, 0)).1 < C.length ∧
      ((CT.getD i []).getD s (0, 0)).2 < E.length ∧
      nmul n (C.getD i []) (S.getD s []) = nmul n (C.getD ((CT.getD i []).getD s (0, 0)).1 [])
        (E.getD ((CT.getD i []).getD s (0, 0)).2 []) := by
    intro i hi s hs
    have r := zip_all_getD hCT hCTl.symm [] [] hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at r
    have q := zip_all_getD r.2 r.1.symm [] (0, 0) hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, gC, gE] at q
    exact ⟨q.1.1, q.1.2, q.2⟩
  have tm : ∀ i < C.length, ∀ s < S.length, ∀ j < C.length, ∀ k < E.length,
      nmul n (C.getD i []) (S.getD s []) = nmul n (C.getD j []) (E.getD k []) →
      toM n (C.getD i []) * toM n (S.getD s []) = toM n (C.getD j []) * toM n (E.getD k []) := by
    intro i hi s hs j hj k hk e
    rw [← toM_nmul n _ _ (hWC i hi).1 (hWS s hs), e, toM_nmul n _ _ (hWC j hj).1 (hE k hk)]
  refine ⟨hC0.1, by rw [hC0.2, idN_spec], hWC, fun i hi s hs => ?_, fun i hi hi0 => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hrow i hi s hs
    exact ⟨_, h1, _, h2, tm i hi s hs _ h1 _ h2 h3⟩
  · have r := zip_range_all hCP hCPl (0, 0) hi
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at r
    rcases r with r | ⟨⟨hp, hs⟩, he⟩
    · exact absurd r hi0
    · obtain ⟨-, h2, h3⟩ := hrow (CP.getD i (0, 0)).1 (by omega) _ hs
      rw [he] at h2 h3
      refine ⟨_, hp, _, hs, ?_⟩
      have := tm _ (by omega) _ hs i hi 0 h2 h3
      rw [hE0, mul_one] at this
      exact this.symm

theorem orb_sound {n : ℕ} {S E C : List NMat} {OT : List (List ℕ)} {roots : List ℕ}
    (h : kOrbT n S E C (treeOf C) (treeOf E) OT roots = true) (hS : ∀ s ∈ S, WF n s)
    (hE : ∀ k < E.length, Red n (E.getD k [])) (hC : ∀ i < C.length, WF n (C.getD i [])) :
    ∀ i < C.length,
      ((∃ k < E.length, toM n (C.getD i []) * toM n (C.getD i []) = toM n (E.getD k [])) →
        (OT.getD i []).getD 0 0 = 1) ∧
      ((OT.getD i []).getD 0 0 = 1 → ((OT.getD i []).getD 1 0 = 0 ∧ i ∈ roots) ∨
        (0 < (OT.getD i []).getD 1 0 ∧ ∃ s < S.length, ∃ c < C.length,
          (OT.getD c []).getD 1 0 < (OT.getD i []).getD 1 0 ∧ ∃ k < E.length,
          toM n (S.getD s []) * toM n (C.getD i []) * toM n (S.getD s []) =
            toM n (C.getD c []) * toM n (E.getD k []))) := by
  simp only [kOrbT, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hrows⟩ := h
  have gC : ∀ i, getT (treeOf C) i = C.getD i [] := fun i => getT_treeOf C i
  have gE : ∀ i, getT (treeOf E) i = E.getD i [] := fun i => getT_treeOf E i
  have gO : ∀ i, getT (treeOf OT) i = OT.getD i [] := fun i => getT_treeOf OT i
  intro i hi
  have r := zip_range_all hrows (by simp [hl]) ([], []) hi
  rw [zip_getD C OT [] [] hi (by omega)] at r
  simp only [kOrbRow, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, List.contains_iff_mem, gC, gE, gO] at r
  refine ⟨fun ⟨k, hk, he⟩ => ?_, fun h1 => ?_⟩
  · rcases r.1 with hc | hc
    · have hx := hC i hi
      have hsq := wf_nmul n _ _ hx.1 hx
      have heq : nmul n (C.getD i []) (C.getD i []) = E.getD k [] :=
        toM_inj n hsq (hE k hk) (by rw [toM_nmul n _ _ hx.1 hx, he])
      have hm : Certificates.TWLK.kVKey 13 (nmul n (C.getD i []) (C.getD i [])) ∈
          E.map (Certificates.TWLK.kVKey 13) :=
        List.mem_map.mpr ⟨_, getD_mem_of_lt hk, by rw [heq]⟩
      rw [List.contains_iff_mem.mpr hm] at hc
      exact absurd hc (by decide)
    · exact hc
  · rcases r.2 with (h2 | ⟨h20, hroot⟩) | ⟨⟨⟨⟨⟨hd, hc⟩, hs⟩, hk⟩, hdc⟩, he⟩
    · exact absurd h1 h2
    · exact Or.inl ⟨h20, hroot⟩
    · refine Or.inr ⟨hd, _, hs, _, hc, hdc, _, hk, ?_⟩
      have ws := hS _ (getD_mem_of_lt (d := []) hs)
      have wx := hC i hi
      rw [← toM_nmul n _ _ ws.1 wx, ← toM_nmul n _ _ (wf_nmul n _ _ ws.1 wx).1.1 ws, he,
        toM_nmul n _ _ (hC _ hc).1 (hE _ hk).1]

theorem scan_sound {n : ℕ} {E C : List NMat} {V : List KPair} {W : List (ℕ × List (ℕ × ℕ × ℕ))}
    (h : kScan n E (treeOf C) C.length V W = true) (hE : ∀ k < E.length, Red n (E.getD k []))
    (hC : ∀ i < C.length, WF n (C.getD i [])) :
    ∀ p ∈ W, p.1 < C.length ∧ ∀ k < E.length,
      let x := toM n (C.getD p.1 []) * toM n (E.getD k [])
      let z := Matrix.scalar (Fin n) (-1 : ZMod 13)
      x * x ≠ 1 ∨ x = 1 ∨ (∃ a < V.length, x = Lm n V a) ∨ (∃ a < V.length, z * x = Lm n V a) ∨
        (∃ a < V.length, ∃ b < V.length, Lm n V a * x = Lm n V b) ∨
        (∃ a < V.length, ∃ b < V.length, Lm n V a * (z * x) = Lm n V b) := by
  have gC : ∀ i, getT (treeOf C) i = C.getD i [] := fun i => getT_treeOf C i
  have gV : ∀ i, getT (treeOf V) i = V.getD i kP0 := fun i => getT_treeOf V i
  intro p hp
  have r := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at r
  obtain ⟨⟨h1, h2⟩, h3⟩ := r
  refine ⟨h1, fun k hk => ?_⟩
  dsimp only
  have q := zip_all_getD h3 h2.symm [] (0, 0, 0) hk
  rw [gC] at q
  dsimp only at q
  have hx := wf_nmul n _ _ (hC _ h1).1 (hE k hk).1
  have wz := wf_scalN n 12
  have h12 : ((12 : ℕ) : ZMod 13) = -1 := by decide
  have tz : toM n (scalN n 12) = Matrix.scalar (Fin n) (-1 : ZMod 13) := by rw [scalN_spec, h12]
  have wzx := wf_nmul n _ _ wz.1 hx.1
  rw [← toM_nmul n _ _ (hC _ h1).1 (hE k hk).1]
  unfold Lm
  generalize p.2.getD k (0, 0, 0) = w at q
  obtain ⟨f, a, b⟩ := w
  match f, q with
  | 0, q =>
    simp only [kWit1, Bool.not_eq_true', isOneN, decide_eq_false_iff_not] at q
    refine Or.inl fun he => ?_
    exact q (toM_inj n (wf_nmul n _ _ hx.1.1 hx.1) (wf_idN n) (by rw [toM_nmul n _ _ hx.1.1 hx.1, he, idN_spec]))
  | 1, q =>
    simp only [kWit1] at q
    exact Or.inr (Or.inl (isOneN_sound q))
  | 2, q =>
    simp only [kWit1, Bool.and_eq_true, decide_eq_true_eq, gV] at q
    exact Or.inr (Or.inr (Or.inl ⟨a, q.1, by rw [q.2]⟩))
  | 3, q =>
    simp only [kWit1, Bool.and_eq_true, decide_eq_true_eq, gV] at q
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, q.1, by rw [← tz, ← toM_nmul n _ _ wz.1 hx.1, q.2]⟩)))
  | 4, q =>
    simp only [kWit1, Bool.and_eq_true, decide_eq_true_eq, gV] at q
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, q.1.1, b, q.1.2, by
      rw [← toM_nmul n _ _ (wf_mat n _).1.1 hx.1, q.2]⟩))))
  | 5, q =>
    simp only [kWit1, Bool.and_eq_true, decide_eq_true_eq, gV] at q
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, q.1.1, b, q.1.2, by
      rw [← tz, ← toM_nmul n _ _ wz.1 hx.1, ← toM_nmul n _ _ (wf_mat n _).1.1 wzx.1, q.2]⟩))))
  | f + 6, q =>
    simp [kWit1] at q

theorem pair_sound {n : ℕ} {V : List KPair} (h : kPairO n V = true) :
    ∀ i < V.length, ∃ e, 0 < e ∧ e ≤ 4 ∧ (Lm n V 0 * Lm n V i) ^ e = 1 := by
  intro i hi
  have h1 := List.all_eq_true.mp h _ (getD_mem_of_lt (d := kP0) hi)
  simp only [Bool.or_eq_true] at h1
  have hA := wf_mat n (V.getD 0 kP0)
  have hB := wf_mat n (V.getD i kP0)
  have hP := wf_nmul n _ _ hA.1.1 hB.1
  have hP2 := wf_nmul n _ _ hP.1.1 hP.1
  have eP : toM n (nmul n (mat n (V.getD 0 kP0)) (mat n (V.getD i kP0))) = Lm n V 0 * Lm n V i :=
    toM_nmul n _ _ hA.1.1 hB.1
  have eP2 : toM n (nmul n (nmul n (mat n (V.getD 0 kP0)) (mat n (V.getD i kP0)))
      (nmul n (mat n (V.getD 0 kP0)) (mat n (V.getD i kP0)))) = (Lm n V 0 * Lm n V i) ^ 2 := by
    rw [toM_nmul n _ _ hP.1.1 hP.1, eP, sq]
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact ⟨1, by norm_num, by norm_num, by rw [pow_one, ← eP, isOneN_sound h1]⟩
  · exact ⟨2, by norm_num, by norm_num, by rw [← eP2, isOneN_sound h1]⟩
  · refine ⟨3, by norm_num, by norm_num, ?_⟩
    rw [pow_succ, ← eP2, ← eP, ← toM_nmul n _ _ hP2.1.1 hP.1, isOneN_sound h1]
  · refine ⟨4, by norm_num, by norm_num, ?_⟩
    have e4 : (Lm n V 0 * Lm n V i) ^ 4 = (Lm n V 0 * Lm n V i) ^ 2 * (Lm n V 0 * Lm n V i) ^ 2 := by
      rw [← pow_add]
    rw [e4, ← eP2, ← toM_nmul n _ _ hP2.1.1 hP2.1, isOneN_sound h1]

end CFSG.StandardType.ZS.NFMK

end
