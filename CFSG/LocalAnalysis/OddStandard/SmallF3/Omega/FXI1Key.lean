module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Lin
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

private theorem fx_key_gram (b : ℕ → ℕ → ZMod 3) (hs : ∀ i j, b i j = b j i)
    (hz : ∀ i j, 4 ≤ i → b i j = 0)
    (hR : ∀ i j, b (i + 1) j + b i (j + 1) + b (i + 1) (j + 1) = 0) :
    b 3 0 = 0 ∧ b 3 1 = 0 ∧ b 3 2 = 0 ∧ b 3 3 = 0 := by
  have hz4 : ∀ i j, 4 ≤ j → b i j = 0 := fun i j hj => by rw [hs i j, hz j i hj]
  have h33 : b 3 3 = 0 := by
    have h := hR 3 2
    simp only [Nat.reduceAdd] at h
    rw [hz 4 2 (by norm_num), hz 4 3 (by norm_num)] at h
    simpa using h
  have h32 : b 3 2 = 0 := by
    have h := hR 3 1
    simp only [Nat.reduceAdd] at h
    rw [hz 4 1 (by norm_num), hz 4 2 (by norm_num)] at h
    simpa using h
  have h31 : b 3 1 = 0 := by
    have h := hR 3 0
    simp only [Nat.reduceAdd] at h
    rw [hz 4 0 (by norm_num), hz 4 1 (by norm_num)] at h
    simpa using h
  have h22 : b 2 2 = 0 := by
    have h := hR 2 1
    simp only [Nat.reduceAdd] at h
    rw [h31, h32] at h
    simpa using h
  have h21 : b 2 1 = 0 := by
    have h := hR 1 1
    simp only [Nat.reduceAdd] at h
    rw [hs 1 2, h22] at h
    have key : ∀ x : ZMod 3, x + x = 0 → x = 0 := by decide
    exact key (b 2 1) (by simpa using h)
  have h30 : b 3 0 = 0 := by
    have h := hR 2 0
    simp only [Nat.reduceAdd] at h
    rw [h31, h21] at h
    simpa using h
  exact ⟨h30, h31, h32, h33⟩

private theorem fx_key_indep (N : Module.End (ZMod 3) V) (v : V) (h3 : (N ^ 3) v ≠ 0)
    (h4 : (N ^ 4) v = 0) :
    LinearIndependent (ZMod 3) (fun i : Fin 4 => (N ^ (i : ℕ)) v) := by
  have h5 : ∀ k, 4 ≤ k → (N ^ k) v = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_add, Module.End.mul_apply, h4, map_zero]
  have hNpow : ∀ a b : ℕ, (N ^ a) ((N ^ b) v) = (N ^ (a + b)) v := by
    intro a b
    rw [← Module.End.mul_apply, ← pow_add]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • (N ^ 0) v + c 1 • (N ^ 1) v + c 2 • (N ^ 2) v +
      c 3 • (N ^ 3) v = 0 := by
    simpa [Fin.sum_univ_four] using hc
  have hc0 : c 0 • (N ^ 3) v = 0 := by
    have h := congrArg (fun x => (N ^ 3) x) hc'
    simp only [map_add, map_smul, hNpow, Nat.reduceAdd, h5 4 (by norm_num),
      h5 5 (by norm_num), h5 6 (by norm_num), map_zero, smul_zero, zero_smul,
      add_zero, zero_add] at h
    simpa using h
  have hc0z : c 0 = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hc0 with h | h
    · exact h
    · exact absurd h h3
  have hc1 : c 1 • (N ^ 3) v = 0 := by
    have h := congrArg (fun x => (N ^ 2) x) hc'
    simp only [map_add, map_smul, hNpow, Nat.reduceAdd, hc0z, h5 4 (by norm_num),
      h5 5 (by norm_num), map_zero, smul_zero, zero_smul, add_zero, zero_add] at h
    simpa using h
  have hc1z : c 1 = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hc1 with h | h
    · exact h
    · exact absurd h h3
  have hc2 : c 2 • (N ^ 3) v = 0 := by
    have h := congrArg (fun x => (N ^ 1) x) hc'
    simp only [map_add, map_smul, hNpow, Nat.reduceAdd, hc0z, hc1z,
      h5 4 (by norm_num), map_zero, smul_zero, zero_smul, add_zero, zero_add] at h
    simpa using h
  have hc2z : c 2 = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hc2 with h | h
    · exact h
    · exact absurd h h3
  have hc3 : c 3 • (N ^ 3) v = 0 := by
    have h := hc'
    simp only [hc0z, hc1z, hc2z, zero_smul, zero_add] at h
    simpa using h
  have hc3z : c 3 = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hc3 with h | h
    · exact h
    · exact absurd h h3
  have key : ∀ i : Fin 4, c i = 0 := by
    change ∀ i : Fin (3 + 1), c i = 0
    rw [Fin.forall_fin_succ]
    refine ⟨hc0z, ?_⟩
    change ∀ i : Fin (2 + 1), c i.succ = 0
    rw [Fin.forall_fin_succ]
    refine ⟨by simpa using hc1z, ?_⟩
    change ∀ i : Fin (1 + 1), c i.succ.succ = 0
    rw [Fin.forall_fin_succ]
    refine ⟨by simpa using hc2z, ?_⟩
    change ∀ i : Fin (0 + 1), c i.succ.succ.succ = 0
    rw [Fin.forall_fin_succ]
    exact ⟨by simpa using hc3z, fun i => i.elim0⟩
  exact key

private theorem fx_key_span (W : Submodule (ZMod 3) V) (f : Fin 4 → V)
    (hf : LinearIndependent (ZMod 3) f) (hfW : ∀ i, f i ∈ W)
    (hW4 : Module.finrank (ZMod 3) W ≤ 4) :
    ∀ w ∈ W, ∃ c : Fin 4 → ZMod 3, ∑ i, c i • f i = w := by
  intro w hw
  have hle : Submodule.span (ZMod 3) (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hfW i
  have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range f)) = 4 := by
    rw [finrank_span_eq_card hf]
    simp
  have heq : Submodule.span (ZMod 3) (Set.range f) = W :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq] at hw
  exact Submodule.mem_span_range_iff_exists_fun (ZMod 3) |>.mp hw

theorem fx_key (B : LinearMap.BilinForm (ZMod 3) V) (hsymm : ∀ a b, B a b = B b a)
    {U : Module.End (ZMod 3) V} (hiso : ∀ a b, B (U a) (U b) = B a b) (hU9 : U ^ 9 = 1)
    {W : Submodule (ZMod 3) V} (hWU : ∀ w ∈ W, U w ∈ W)
    (hW4 : Module.finrank (ZMod 3) W ≤ 4)
    (hWnd : ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0) : ∀ w ∈ W, (U ^ 3) w = w := by
  intro v hv
  by_contra hne
  set N : Module.End (ZMod 3) V := U - 1 with hNdef
  have hN9 : N ^ 9 = 0 := fx_sub_one_pow_nine U hU9
  have hNU : ∀ w, N w = U w - w := fun w => by simp [hNdef]
  have hN3 : (N ^ 3) v ≠ 0 := by
    intro h
    apply hne
    have h3 : N ^ 3 = U ^ 3 - 1 := fx_sub_one_pow_three U
    rw [h3] at h
    simpa [sub_eq_zero] using h
  have hNW : ∀ w ∈ W, N w ∈ W := fun w hw => by
    rw [hNU]
    exact sub_mem (hWU w hw) hw
  have hNk : ∀ k, ∀ w ∈ W, (N ^ k) w ∈ W := fun k w hw =>
    Module.End.pow_apply_mem_of_forall_mem k hNW w hw
  have hrel : ∀ a b, B (N a) b + B a (N b) + B (N a) (N b) = 0 := by
    intro a b
    have h := hiso a b
    have ha : U a = a + N a := by rw [hNU]; abel
    have hb : U b = b + N b := by rw [hNU]; abel
    rw [ha, hb] at h
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h
  have h4 : (N ^ 4) v = 0 := by
    have h := fx_pow_finrank_apply_eq_zero N hN9 hNW hv
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hW4
    rw [hj, pow_add, Module.End.mul_apply, h, map_zero]
  set f : ℕ → V := fun i => (N ^ i) v with hfdef
  have hfs : ∀ i, f (i + 1) = N (f i) := fun i => by simp [hfdef, pow_succ']
  have hf4 : ∀ i, 4 ≤ i → f i = 0 := fun i hi => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    simp [hfdef, pow_add, h4]
  have hfW : ∀ i, f i ∈ W := fun i => hNk i v hv
  have hbs : ∀ i j, B (f i) (f j) = B (f j) (f i) := fun i j => hsymm _ _
  have hbz : ∀ i j, 4 ≤ i → B (f i) (f j) = 0 := fun i j hi => by simp [hf4 i hi]
  have hbR : ∀ i j, B (f (i + 1)) (f j) + B (f i) (f (j + 1)) +
      B (f (i + 1)) (f (j + 1)) = 0 := fun i j => by
    rw [hfs, hfs]
    exact hrel (f i) (f j)
  obtain ⟨b30, b31, b32, b33⟩ := fx_key_gram (fun i j => B (f i) (f j)) hbs hbz hbR
  have hind := fx_key_indep N v hN3 h4
  have hspan := fx_key_span W (fun i : Fin 4 => f i) hind (fun i => hfW i) hW4
  have horth : ∀ w' ∈ W, B (f 3) w' = 0 := by
    intro w' hw'
    obtain ⟨c, rfl⟩ := hspan w' hw'
    simp only [map_sum, map_smul, smul_eq_mul, Fin.sum_univ_four]
    simp [b30, b31, b32, b33]
  exact hN3 (hWnd _ (hfW 3) horth)

end CFSG.OddStandard.SmallF3.Omega
