module

public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv

@[expose] def shiftPerm (p q : ℕ) [NeZero p] (g : Multiplicative (Fin q → ZMod p)) :
    Perm (Fin q × ZMod p) where
  toFun x := (x.1, x.2 + g.toAdd x.1)
  invFun x := (x.1, x.2 - g.toAdd x.1)
  left_inv x := by simp
  right_inv x := by simp

@[expose] def shiftHom (p q : ℕ) [NeZero p] :
    Multiplicative (Fin q → ZMod p) →* Perm (Fin q × ZMod p) :=
  MonoidHom.mk' (shiftPerm p q) (by
    intro g h
    ext x <;> simp [shiftPerm, Perm.mul_apply] ; ring)

theorem shiftHom_injective (p q : ℕ) [NeZero p] : Function.Injective (shiftHom p q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : ∀ j, g.toAdd j = 0 := by
    intro j
    have := congrArg (fun σ : Perm (Fin q × ZMod p) => (σ (j, 0)).2) hg
    simpa [shiftHom, shiftPerm] using this
  apply Multiplicative.toAdd.injective
  funext j
  simpa using this j

theorem blockEmb_lt {p q n : ℕ} [NeZero p] (h : q * p + 4 ≤ n) (x : Fin q × ZMod p) :
    4 + x.1.val * p + x.2.val < n := by
  have h1 := x.1.isLt
  have h2 := ZMod.val_lt x.2
  have : (x.1.val + 1) * p ≤ q * p := Nat.mul_le_mul_right _ h1
  nlinarith

@[expose] def blockEmb (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n) : Fin q × ZMod p ↪ Fin n where
  toFun x := ⟨4 + x.1.val * p + (x.2.val), blockEmb_lt h x⟩
  inj' := by
    intro x y hxy
    have hxy' : x.1.val * p + x.2.val = y.1.val * p + y.2.val := by
      have := congrArg Fin.val hxy
      simp only at this
      omega
    have hx2 := ZMod.val_lt x.2
    have hy2 := ZMod.val_lt y.2
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have d1 : (x.2.val + x.1.val * p) / p = x.1.val := by
      rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hx2]; simp
    have d2 : (y.2.val + y.1.val * p) / p = y.1.val := by
      rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy2]; simp
    have e1 : x.1.val = y.1.val := by
      rw [← d1, ← d2, add_comm x.2.val, add_comm y.2.val, hxy']
    have e2 : x.2.val = y.2.val := by
      rw [e1] at hxy'; omega
    exact Prod.ext (Fin.ext e1) (ZMod.val_injective p e2)

@[expose] noncomputable def blockHom (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n) :
    Multiplicative (Fin q → ZMod p) →* Perm (Fin n) :=
  (Perm.viaEmbeddingHom (blockEmb p q n h)).comp (shiftHom p q)

theorem blockHom_injective (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n) :
    Function.Injective (blockHom p q n h) :=
  (Perm.viaEmbeddingHom_injective _).comp (shiftHom_injective p q)

theorem blockHom_fix (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n)
    (g : Multiplicative (Fin q → ZMod p)) (a : Fin n) (ha : a.val < 4) :
    blockHom p q n h g a = a := by
  apply Perm.viaEmbedding_apply_of_notMem
  rintro ⟨x, hx⟩
  have := congrArg Fin.val hx
  simp [blockEmb] at this
  omega

theorem blockHom_pow (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n)
    (g : Multiplicative (Fin q → ZMod p)) : blockHom p q n h g ^ p = 1 := by
  rw [← map_pow]
  have : g ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp
  rw [this, map_one]

@[expose] def invol (n : ℕ) (hn : 4 ≤ n) : Perm (Fin n) :=
  swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩

theorem invol_sq (n : ℕ) (hn : 4 ≤ n) : invol n hn ^ 2 = 1 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have hc : Commute (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
      (swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩) := by
    apply Perm.Disjoint.commute
    intro a
    by_cases h : a = ⟨0, by omega⟩ ∨ a = ⟨1, by omega⟩
    · right
      apply swap_apply_of_ne_of_ne <;> rcases h with h | h <;> simp [h, Fin.ext_iff]
    · left
      push Not at h
      exact swap_apply_of_ne_of_ne h.1 h.2
  rw [invol, hc.mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self, one_mul]

theorem invol_ne_one (n : ℕ) (hn : 4 ≤ n) : invol n hn ≠ 1 := by
  intro h
  have := congrArg (fun σ : Perm (Fin n) => σ ⟨0, by omega⟩) h
  simp [invol, swap_apply_of_ne_of_ne, Fin.ext_iff] at this

theorem invol_fix (n : ℕ) (hn : 4 ≤ n) (a : Fin n) (ha : 4 ≤ a.val) : invol n hn a = a := by
  have h1 : swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩ a = a :=
    swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
  simp only [invol, Perm.mul_apply, h1]
  exact swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem invol_mem_alt (n : ℕ) (hn : 4 ≤ n) : invol n hn ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, invol, map_mul,
    Perm.sign_swap (by simp [Fin.ext_iff]), Perm.sign_swap (by simp [Fin.ext_iff])]
  decide

theorem invol_commute (p q n : ℕ) [NeZero p] (h : q * p + 4 ≤ n) (hn : 4 ≤ n)
    (g : Multiplicative (Fin q → ZMod p)) : Commute (blockHom p q n h g) (invol n hn) := by
  apply Perm.Disjoint.commute
  intro a
  by_cases ha : a.val < 4
  · left; exact blockHom_fix p q n h g a ha
  · right; exact invol_fix n hn a (by omega)

theorem blockHom_mem_alt {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (q n : ℕ) (h : q * p + 4 ≤ n)
    (g : Multiplicative (Fin q → ZMod p)) :
    blockHom p q n h g ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hpow : Perm.sign (blockHom p q n h g) ^ p = 1 := by
    rw [← map_pow, blockHom_pow, map_one]
  rcases Int.units_eq_one_or (Perm.sign (blockHom p q n h g)) with h1 | h1
  · exact h1
  · rw [h1, hodd.neg_one_pow] at hpow
    exact absurd hpow (by decide)

theorem exists_elemAbelian_centralizing_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ E T : Subgroup (alternatingGroup (Fin n)),
      IsMulCommutative E ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ ((n - 4) / p) ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.centralizer (T : Set (alternatingGroup (Fin n))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (n - 4) / p := ⟨_, rfl⟩
  rw [← hq]
  have h : q * p + 4 ≤ n := by
    have := Nat.div_mul_le_self (n - 4) p
    rw [← hq] at this
    omega
  set A := alternatingGroup (Fin n) with hA
  set E₀ : Subgroup (Perm (Fin n)) := (blockHom p q n h).range with hE₀
  set T₀ : Subgroup (Perm (Fin n)) := Subgroup.zpowers (invol n hn) with hT₀
  have hE₀A : E₀ ≤ A := by
    rintro _ ⟨g, rfl⟩
    exact blockHom_mem_alt hp hp2 q n h g
  have hT₀A : T₀ ≤ A := by
    rw [hT₀, Subgroup.zpowers_le]
    exact invol_mem_alt n hn
  refine ⟨E₀.subgroupOf A, T₀.subgroupOf A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · intro x hx
    obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hg]
    exact blockHom_pow p q n h g
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective (blockHom_injective p q n h)).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp
  · intro hT
    have hmem : (⟨invol n hn, invol_mem_alt n hn⟩ : A) ∈ T₀.subgroupOf A :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
    rw [hT, Subgroup.mem_bot] at hmem
    exact invol_ne_one n hn (congrArg Subtype.val hmem)
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hg : (g : A).val ∈ T₀ := Subgroup.mem_subgroupOf.mp g.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [invol_sq]
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hg]
    have ht' : (t : Perm (Fin n)) ∈ T₀ := Subgroup.mem_subgroupOf.mp ht
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ht'
    rw [← hm]
    exact ((invol_commute p q n h hn g).zpow_right m).symm.eq

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
