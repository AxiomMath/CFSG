module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open scoped commutatorElement

section Level

variable {G : Type*} [Group G] {ι : Type*}

@[expose] def lvl (X : ι → Subgroup G) (P : Set ι) (lev : ι → ℤ) (r : ℤ) : Subgroup G :=
  ⨆ γ ∈ {γ | γ ∈ P ∧ r ≤ lev γ}, X γ

variable (X : ι → Subgroup G) (P : Set ι) (lev : ι → ℤ)

theorem le_lvl {γ : ι} (hγ : γ ∈ P) {r : ℤ} (h : r ≤ lev γ) : X γ ≤ lvl X P lev r :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ P ∧ r ≤ lev γ}) => X γ) γ ⟨hγ, h⟩ le_rfl

theorem lvl_anti {r s : ℤ} (h : s ≤ r) : lvl X P lev r ≤ lvl X P lev s :=
  iSup₂_le fun _ hγ => le_lvl X P lev hγ.1 (h.trans hγ.2)

theorem lvl_eq_bot {r : ℤ} (h : ∀ γ ∈ P, lev γ < r) : lvl X P lev r = ⊥ :=
  eq_bot_iff.2 (iSup₂_le fun _ hγ => absurd hγ.2 (not_le.2 (h _ hγ.1)))

theorem lvl_eq_succ {r : ℤ} (h : ∀ γ ∈ P, lev γ ≠ r) : lvl X P lev r = lvl X P lev (r + 1) :=
  le_antisymm (iSup₂_le fun _ hγ => le_lvl X P lev hγ.1
    (by have := hγ.2; have := h _ hγ.1; omega)) (lvl_anti X P lev (by omega))

variable {X P lev}

theorem lvl_induction {r : ℤ} {C : G → Prop} {y : G} (hy : y ∈ lvl X P lev r)
    (mem : ∀ δ ∈ P, r ≤ lev δ → ∀ z ∈ X δ, C z) (one : C 1)
    (mul : ∀ a b, C a → C b → C (a * b)) : C y := by
  refine Subgroup.iSup_induction _ (C := C) hy (fun δ z hz => ?_) one mul
  refine Subgroup.iSup_induction _ (C := C) hz (fun hδ w hw => mem δ hδ.1 hδ.2 w hw) one mul

structure LevelData (X : ι → Subgroup G) (P : Set ι) (lev : ι → ℤ) : Prop where
  pos : ∀ γ ∈ P, 1 ≤ lev γ
  inj : ∀ γ ∈ P, ∀ δ ∈ P, lev γ = lev δ → γ = δ
  comm : ∀ γ ∈ P, ∀ δ ∈ P, ∀ x ∈ X γ, ∀ y ∈ X δ, ⁅x, y⁆ ∈ lvl X P lev (lev γ + lev δ)

namespace LevelData

variable (h : LevelData X P lev)
include h

theorem conj_mem {γ : ι} (hγ : γ ∈ P) {x : G} (hx : x ∈ X γ) {r : ℤ} {y : G}
    (hy : y ∈ lvl X P lev r) : x * y * x⁻¹ ∈ lvl X P lev r := by
  refine lvl_induction (C := fun y => x * y * x⁻¹ ∈ lvl X P lev r) hy (fun δ hδ hrδ z hz => ?_)
    (by simp) (fun a b ha hb => ?_)
  · have h1 : ⁅x, z⁆ ∈ lvl X P lev r :=
      lvl_anti X P lev (by have := h.pos γ hγ; omega) (h.comm γ hγ δ hδ x hx z hz)
    have h2 : x * z * x⁻¹ = ⁅x, z⁆ * z := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem h1 (le_lvl X P lev hδ hrδ hz)
  · have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact mul_mem ha hb

theorem lvl_decomp {γ : ι} (hγ : γ ∈ P) {a : G} (ha : a ∈ lvl X P lev (lev γ)) :
    ∃ x ∈ X γ, ∃ k ∈ lvl X P lev (lev γ + 1), a = x * k := by
  refine lvl_induction (C := fun a => ∃ x ∈ X γ, ∃ k ∈ lvl X P lev (lev γ + 1), a = x * k) ha
    (fun δ hδ hle z hz => ?_) ⟨1, one_mem _, 1, one_mem _, by simp⟩ (fun a b ha hb => ?_)
  · rcases hle.eq_or_lt with heq | hlt
    · have := h.inj γ hγ δ hδ heq
      subst this
      exact ⟨z, hz, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, z, le_lvl X P lev hδ (by omega) hz, by simp⟩
  · obtain ⟨x, hx, k, hk, rfl⟩ := ha
    obtain ⟨x', hx', k', hk', rfl⟩ := hb
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * k * x' * k', mul_mem ?_ hk', by group⟩
    have := h.conj_mem hγ (inv_mem hx') hk
    simpa using this

end LevelData

noncomputable def leadSet (hP : P.Finite) (A : Subgroup G) : Finset ι := by
  classical
  exact hP.toFinset.filter fun γ => A ⊓ lvl X P lev (lev γ + 1) ≠ A ⊓ lvl X P lev (lev γ)

theorem mem_leadSet {hP : P.Finite} {A : Subgroup G} {γ : ι} :
    γ ∈ leadSet (X := X) (lev := lev) hP A ↔
      γ ∈ P ∧ A ⊓ lvl X P lev (lev γ + 1) ≠ A ⊓ lvl X P lev (lev γ) := by
  classical
  simp [leadSet]

theorem exists_of_mem_leadSet {hP : P.Finite} {A : Subgroup G} {γ : ι}
    (hγ : γ ∈ leadSet (X := X) (lev := lev) hP A) :
    ∃ a ∈ A, a ∈ lvl X P lev (lev γ) ∧ a ∉ lvl X P lev (lev γ + 1) := by
  obtain ⟨hγP, hne⟩ := mem_leadSet.1 hγ
  by_contra hcon
  push Not at hcon
  apply hne
  refine le_antisymm (inf_le_inf_left _ (lvl_anti X P lev (by omega))) ?_
  intro a ha
  exact ⟨ha.1, hcon a ha.1 ha.2⟩

theorem card_inf_lvl_le [Finite G] (h : LevelData X P lev) {γ : ι} (hγ : γ ∈ P)
    (A : Subgroup G) :
    Nat.card ↥(A ⊓ lvl X P lev (lev γ)) ≤
      Nat.card ↥(X γ) * Nat.card ↥(A ⊓ lvl X P lev (lev γ + 1)) := by
  set J := lvl X P lev (lev γ) with hJ
  set K := lvl X P lev (lev γ + 1) with hK
  have hKJ : K ≤ J := lvl_anti X P lev (by omega)
  have h1 := Subgroup.relIndex_mul_card K (A ⊓ J)
  have h2 : K ⊓ (A ⊓ J) = A ⊓ K := by
    ext g
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b, _⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a, hKJ b⟩⟩
  rw [h2] at h1
  have h3 : K.relIndex (A ⊓ J) ≤ K.relIndex J :=
    Subgroup.relIndex_le_of_le_right inf_le_right (Subgroup.index_ne_zero_of_finite)
  have h4 : K.relIndex J ≤ Nat.card ↥(X γ) := by
    have hXJ : X γ ≤ J := le_lvl X P lev hγ le_rfl
    let f : ↥(X γ) → ↥J ⧸ K.subgroupOf J := fun x => QuotientGroup.mk ⟨x.1, hXJ x.2⟩
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, hx, k, hk, rfl⟩ := h.lvl_decomp hγ ha
      refine ⟨⟨x, hx⟩, ?_⟩
      show (QuotientGroup.mk ⟨x, hXJ hx⟩ : ↥J ⧸ K.subgroupOf J) = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hk
    exact Nat.card_le_card_of_surjective f hf
  calc Nat.card ↥(A ⊓ J) = K.relIndex (A ⊓ J) * Nat.card ↥(A ⊓ K) := h1.symm
    _ ≤ Nat.card ↥(X γ) * Nat.card ↥(A ⊓ K) := Nat.mul_le_mul_right _ (h3.trans h4)

theorem card_le_pow_leadSet [Finite G] (h : LevelData X P lev) (hP : P.Finite) {q : ℕ}
    (hq1 : 1 ≤ q) (hq : ∀ γ ∈ P, Nat.card ↥(X γ) ≤ q) {A : Subgroup G}
    (hA : A ≤ lvl X P lev 1) :
    Nat.card ↥A ≤ q ^ (leadSet (X := X) (lev := lev) hP A).card := by
  classical
  obtain ⟨M, hM⟩ := (hP.image lev).bddAbove
  have hN : ∀ γ ∈ P, lev γ < M + 1 := fun γ hγ => by
    have := hM ⟨γ, hγ, rfl⟩
    omega
  set L := leadSet (X := X) (lev := lev) hP A with hL
  have key : ∀ n : ℕ, Nat.card ↥(A ⊓ lvl X P lev (M + 1 - n)) ≤
      q ^ (L.filter fun γ => M + 1 - n ≤ lev γ).card := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, sub_zero, lvl_eq_bot X P lev hN]
      have : Nat.card ↥(A ⊓ (⊥ : Subgroup G)) = 1 := by simp
      rw [this]
      have hem : (L.filter fun γ => M + 1 ≤ lev γ) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun γ hγ => ?_
        have := hN γ (mem_leadSet.1 hγ).1
        omega
      rw [hem]; simp
    | succ n ih =>
      set r : ℤ := M + 1 - (n + 1 : ℕ) with hr
      have hr1 : M + 1 - (n : ℕ) = r + 1 := by rw [hr]; push_cast; ring
      rw [hr1] at ih
      by_cases heq : A ⊓ lvl X P lev r = A ⊓ lvl X P lev (r + 1)
      · rw [heq]
        refine ih.trans (Nat.pow_le_pow_right hq1 (Finset.card_le_card ?_))
        intro γ hγ
        simp only [Finset.mem_filter] at hγ ⊢
        exact ⟨hγ.1, by omega⟩
      · have hex : ∃ γ ∈ P, lev γ = r := by
          by_contra hno
          push Not at hno
          exact heq (by rw [lvl_eq_succ X P lev hno])
        obtain ⟨γ, hγP, hγr⟩ := hex
        have hγL : γ ∈ L := by
          rw [mem_leadSet]
          refine ⟨hγP, fun hcon => heq ?_⟩
          rw [← hγr]
          exact hcon.symm
        have hstep := card_inf_lvl_le h hγP A
        rw [hγr] at hstep
        have hlt : (L.filter fun δ => r + 1 ≤ lev δ).card + 1 ≤
            (L.filter fun δ => r ≤ lev δ).card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨γ, ?_, ?_⟩)
          · intro δ hδ
            simp only [Finset.mem_filter] at hδ ⊢
            exact ⟨hδ.1, by omega⟩
          · simp [Finset.mem_filter, hγL, hγr]
          · simp [Finset.mem_filter, hγr]
        calc Nat.card ↥(A ⊓ lvl X P lev r)
            ≤ Nat.card ↥(X γ) * Nat.card ↥(A ⊓ lvl X P lev (r + 1)) := hstep
          _ ≤ q * q ^ (L.filter fun δ => r + 1 ≤ lev δ).card :=
              Nat.mul_le_mul (hq γ hγP) ih
          _ = q ^ ((L.filter fun δ => r + 1 ≤ lev δ).card + 1) := by ring
          _ ≤ q ^ (L.filter fun δ => r ≤ lev δ).card := Nat.pow_le_pow_right hq1 hlt
  have hlow : ∀ γ ∈ L, 1 ≤ lev γ := fun γ hγ => h.pos γ (mem_leadSet.1 hγ).1
  by_cases h1M : 1 ≤ M + 1
  · have := key (M + 1 - 1).toNat
    have e : (M + 1 - ((M + 1 - 1).toNat : ℕ) : ℤ) = 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [e] at this
    have hfil : (L.filter fun γ => 1 ≤ lev γ) = L :=
      Finset.filter_true_of_mem hlow
    rw [hfil] at this
    have hAeq : A ⊓ lvl X P lev 1 = A := inf_eq_left.2 hA
    rwa [hAeq] at this
  ·
    have hbot : lvl X P lev 1 = ⊥ := lvl_eq_bot X P lev fun γ hγ => by
      have := hN γ hγ; omega
    have hAb : A = ⊥ := eq_bot_iff.2 (hA.trans hbot.le)
    subst hAb
    simpa using Nat.one_le_pow _ _ hq1

end Level

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
