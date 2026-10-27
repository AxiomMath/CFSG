module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsBits

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Function Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_stable_modEq {p : ℕ} [Fact p.Prime] [Finite V] (C : Module.End (ZMod 2) V)
    (hC : C ^ p = 1) (W : Submodule (ZMod 2) V) (hW : ∀ w ∈ W, C w ∈ W) :
    Nat.card W ≡ Nat.card ↥(W ⊓ LinearMap.ker (C - 1)) [MOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let f : Function.End W := fun w => ⟨C w, hW w w.2⟩
  have hpow : ∀ (n : ℕ) (w : W), (((f ^ n) w : W) : V) = (C ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      exact ih (f w)
  have hf : f ^ (p ^ 1) = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hpow, hC]
    rfl
  have key := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hfix : ∀ w : W, w ∈ fixedPoints f ↔ C w = w := by
    intro w
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have e : ↥(W ⊓ LinearMap.ker (C - 1)) ≃ ↑(fixedPoints f) :=
    { toFun := fun x => ⟨⟨x.1, (Submodule.mem_inf.1 x.2).1⟩, (hfix _).2 (by
        have := (Submodule.mem_inf.1 x.2).2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
        simpa using this)⟩
      invFun := fun y => ⟨y.1.1, Submodule.mem_inf.2 ⟨y.1.2, by
        have := (hfix _).1 y.2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        simpa using this⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact key

theorem natCard_submodule [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_eq_of_card [Finite V] (hV : Nat.card V = 2 ^ 11) :
    Module.finrank (ZMod 2) V = 11 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [Nat.card_zmod, hV] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem fix_eq_bot [Finite V] (hV : Nat.card V = 2 ^ 11) (C : Module.End (ZMod 2) V)
    (hC : C ^ 23 = 1) (hC1 : C ≠ 1) : LinearMap.ker (C - 1) = ⊥ := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hfr := finrank_eq_of_card hV
  have h := card_stable_modEq (p := 23) C hC ⊤ (fun _ _ => Submodule.mem_top)
  rw [top_inf_eq] at h
  have h1 : Nat.card (⊤ : Submodule (ZMod 2) V) = 2 ^ 11 := by
    rw [← hV]; exact Nat.card_congr (Submodule.topEquiv.toEquiv)
  rw [h1, natCard_submodule] at h
  have hd11 : Module.finrank (ZMod 2) (LinearMap.ker (C - 1)) ≤ 11 :=
    hfr ▸ Submodule.finrank_le _
  have hcases : Module.finrank (ZMod 2) (LinearMap.ker (C - 1)) = 0 ∨
      Module.finrank (ZMod 2) (LinearMap.ker (C - 1)) = 11 := by
    have : ∀ n < 12, 2 ^ 11 % 23 = 2 ^ n % 23 → n = 0 ∨ n = 11 := by decide
    exact this _ (by omega) h
  rcases hcases with h0 | h11
  · exact Submodule.finrank_eq_zero.1 h0
  · exfalso
    have htop : LinearMap.ker (C - 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h11, hfr])
    apply hC1
    rw [LinearMap.ker_eq_top] at htop
    exact sub_eq_zero.1 htop

theorem stable_eq_top [Finite V] (hV : Nat.card V = 2 ^ 11) (C : Module.End (ZMod 2) V)
    (hC : C ^ 23 = 1) (hC1 : C ≠ 1) (W : Submodule (ZMod 2) V) (hW : ∀ w ∈ W, C w ∈ W)
    (hW0 : W ≠ ⊥) : W = ⊤ := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hfr := finrank_eq_of_card hV
  have h := card_stable_modEq (p := 23) C hC W hW
  rw [fix_eq_bot hV C hC hC1, inf_bot_eq, natCard_submodule, natCard_submodule, finrank_bot,
    pow_zero] at h
  have hd11 : Module.finrank (ZMod 2) W ≤ 11 := hfr ▸ Submodule.finrank_le _
  have hcases : Module.finrank (ZMod 2) W = 0 ∨ Module.finrank (ZMod 2) W = 11 := by
    have : ∀ n < 12, 2 ^ n % 23 = 1 % 23 → n = 0 ∨ n = 11 := by decide
    exact this _ (by omega) h
  rcases hcases with h0 | h11
  · exact absurd (Submodule.finrank_eq_zero.1 h0) hW0
  · exact Submodule.eq_top_of_finrank_eq (by rw [h11, hfr])

theorem exists_fixed_vector [Finite V] (hV : Nat.card V = 2 ^ 11) (Y : Module.End (ZMod 2) V)
    (hY : Y ^ 11 = 1) : ∃ v : V, v ≠ 0 ∧ Y v = v := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h := card_stable_modEq (p := 11) Y hY ⊤ (fun _ _ => Submodule.mem_top)
  rw [top_inf_eq] at h
  have h1 : Nat.card (⊤ : Submodule (ZMod 2) V) = 2 ^ 11 := by
    rw [← hV]; exact Nat.card_congr (Submodule.topEquiv.toEquiv)
  rw [h1, natCard_submodule] at h
  have hne : LinearMap.ker (Y - 1) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, pow_zero] at h
    exact absurd h (by decide)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  refine ⟨v, hv0, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
  simpa using hv

theorem exists_cyclic_basis [Finite V] (hV : Nat.card V = 2 ^ 11) (C Y : Module.End (ZMod 2) V)
    (hC : C ^ 23 = 1) (hC1 : C ≠ 1) (hY : Y ^ 11 = 1) :
    ∃ (v : V) (b : Module.Basis (Fin 11) (ZMod 2) V), Y v = v ∧
      ∀ j : Fin 11, b j = (C ^ (j : ℕ)) v := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hfr := finrank_eq_of_card hV
  obtain ⟨v, hv0, hYv⟩ := exists_fixed_vector hV Y hY
  let seq : ℕ → V := fun n => (C ^ n) v
  let S : ℕ → Submodule (ZMod 2) V := fun d =>
    Submodule.span (ZMod 2) (Set.range fun j : Fin d => seq j)
  have hseq_succ : ∀ n, seq (n + 1) = C (seq n) := by
    intro n; simp [seq, pow_succ', Module.End.mul_apply]
  have hnot : ∀ d ≤ 10, seq d ∉ S d := by
    intro d hd hmem
    have hd0 : d ≠ 0 := by
      rintro rfl
      have : S 0 = ⊥ := by simp [S]
      rw [this] at hmem
      simp [seq] at hmem
      exact hv0 hmem
    have hstable : ∀ w ∈ S d, C w ∈ S d := by
      have : S d ≤ (S d).comap C := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        show C (seq j) ∈ S d
        rw [← hseq_succ]
        by_cases hj : (j : ℕ) + 1 < d
        · exact Submodule.subset_span ⟨⟨(j : ℕ) + 1, hj⟩, rfl⟩
        · have : (j : ℕ) + 1 = d := by omega
          rw [this]; exact hmem
      exact fun w hw => this hw
    have hne : S d ≠ ⊥ := by
      intro hbot
      have : v ∈ S d := by
        have := Submodule.subset_span (R := ZMod 2) (s := Set.range fun j : Fin d => seq j)
          ⟨⟨0, Nat.pos_of_ne_zero hd0⟩, rfl⟩
        simpa [seq] using this
      rw [hbot] at this
      exact hv0 (by simpa using this)
    have htop := stable_eq_top hV C hC hC1 (S d) hstable hne
    have hle : Module.finrank (ZMod 2) (S d) ≤ d := by
      have := finrank_range_le_card (R := ZMod 2) (fun j : Fin d => seq j)
      simp only [Fintype.card_fin] at this
      exact this
    rw [htop, finrank_top, hfr] at hle
    omega
  have hli : ∀ d ≤ 11, LinearIndependent (ZMod 2) (fun j : Fin d => seq j) := by
    intro d
    induction d with
    | zero => intro _; exact linearIndependent_empty_type
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hnot d (by omega)
      have := linearIndependent_finSnoc.2 ⟨h1, h2⟩
      convert this using 1
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp
      · simp
  refine ⟨v, basisOfLinearIndependentOfCardEqFinrank (hli 11 le_rfl) (by simp [hfr]), hYv, ?_⟩
  intro j
  simp [seq]

theorem toMatrix_cyclic (b : Module.Basis (Fin 11) (ZMod 2) V) (C : Module.End (ZMod 2) V)
    (v : V) (hb : ∀ j : Fin 11, b j = (C ^ (j : ℕ)) v) :
    LinearMap.toMatrix b b C = comp (b.repr (C (b 10))) := by
  ext r j
  rw [LinearMap.toMatrix_apply, comp, Matrix.of_apply]
  by_cases hj : j.val = 10
  · have hj10 : j = 10 := Fin.ext hj
    subst hj10
    simp
  · have hj' : j.val < 10 := by have := j.isLt; omega
    have hnext : C (b j) = b ⟨j.val + 1, by omega⟩ := by
      rw [hb, hb]
      simp [pow_succ']
    rw [hnext, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [hj, ↓reduceIte]
    by_cases hr : r.val = j.val + 1
    · have : (⟨j.val + 1, by omega⟩ : Fin 11) = r := Fin.ext hr.symm
      simp only [this, hr, ↓reduceIte]
    · have : ¬ (⟨j.val + 1, by omega⟩ : Fin 11) = r := fun h => hr (by rw [← h])
      simp only [this, hr, ↓reduceIte]

theorem toMatrix_fixed (b : Module.Basis (Fin 11) (ZMod 2) V) (Y : Module.End (ZMod 2) V)
    (h : Y (b 0) = b 0) : LinearMap.toMatrix b b Y *ᵥ e0 = e0 := by
  have h0 : e0 = Pi.single (0 : Fin 11) 1 := rfl
  rw [h0, Matrix.mulVec_single_one]
  ext r
  simp only [Matrix.col_apply]
  rw [LinearMap.toMatrix_apply, h, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  rcases eq_or_ne r 0 with hr | hr
  · subst hr; simp
  · simp [hr, hr.symm]

end CFSG.EvenSporadicStandard.Wong77.Cls
