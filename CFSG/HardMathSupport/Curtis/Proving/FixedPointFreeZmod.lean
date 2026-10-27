module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.HardMathSupport.Curtis.Proving

theorem card_modEq_card_fixed_of_pow {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (r : ℕ) [hr : Fact r.Prime] (g : G) (hg : ∃ k : ℕ, g ^ (r ^ k) = 1) :
    Nat.card X ≡ Nat.card {x : X // g • x = x} [MOD r] := by
  have hH : IsPGroup r (Subgroup.zpowers g) := by
    intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h.2
    obtain ⟨k, hk⟩ := hg
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hk, one_zpow]
  have key := IsPGroup.card_modEq_card_fixedPoints hH X
  have hset : MulAction.fixedPoints (Subgroup.zpowers g) X = {x : X | g • x = x} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h y
      have hg' : g ∈ MulAction.stabilizer G x := MulAction.mem_stabilizer_iff.mpr h
      have hy : (y : G) ∈ MulAction.stabilizer G x := by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
        rw [← hm]
        exact (MulAction.stabilizer G x).zpow_mem hg' m
      exact MulAction.mem_stabilizer_iff.mp hy
  rw [hset] at key
  exact key

theorem pow_four_modEq_one {p r : ℕ} (hdvd : r ∣ p ^ 2 + 1) :
    p ^ 4 ≡ 1 [MOD r] := by
  have hx2 : (p : ZMod r) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (p ^ 2 + 1) r).mpr hdvd
    push_cast at this
    exact this
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have h4 : (p : ZMod r) ^ 4 - 1 = ((p : ZMod r) ^ 2 - 1) * ((p : ZMod r) ^ 2 + 1) := by ring
  rw [← sub_eq_zero, h4, hx2, mul_zero]

theorem pow_modEq_one_forces {p r d : ℕ} [hp : Fact p.Prime] (hdvd : r ∣ p ^ 2 + 1)
    (hndvd : ¬ r ∣ p ^ 2 - 1) (hd : d ≤ 4) (h : p ^ d ≡ 1 [MOD r]) :
    d = 0 ∨ d = 4 := by
  have hx2 : (p : ZMod r) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (p ^ 2 + 1) r).mpr hdvd
    push_cast at this
    exact this
  have hne : (p : ZMod r) ^ 2 ≠ 1 := by
    intro h1
    apply hndvd
    rw [← ZMod.natCast_eq_zero_iff]
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    rw [Nat.cast_sub hp1]
    push_cast
    rw [h1, sub_self]
  have hd' : (p : ZMod r) ^ d = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (p ^ d) 1 r).mpr h
    push_cast at this
    exact this
  have h4 : (p : ZMod r) ^ 4 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (p ^ 4) 1 r).mpr (pow_four_modEq_one hdvd)
    push_cast at this
    exact this
  interval_cases d
  · exact Or.inl rfl
  · exfalso
    apply hne
    rw [pow_one] at hd'
    rw [hd', one_pow]
  · exfalso
    exact hne hd'
  · exfalso
    apply hne
    have h41 : (p : ZMod r) ^ 4 = (p : ZMod r) := by
      calc (p : ZMod r) ^ 4 = (p : ZMod r) * (p : ZMod r) ^ 3 := by ring
        _ = (p : ZMod r) := by rw [hd', mul_one]
    have hx : (p : ZMod r) = 1 := h41.symm.trans h4
    rw [hx, one_pow]
  · exact Or.inr rfl

theorem natCard_eq_pow_finrank_zmod (p : ℕ) [hp : Fact p.Prime] {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U] [FiniteDimensional (ZMod p) U] :
    Nat.card U = p ^ Module.finrank (ZMod p) U := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Finite U := Module.finite_of_finite (ZMod p)
  have := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := U),
    ZMod.card p]

theorem invariant_subspace_eq_bot_or_top {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hdvd : r ∣ p ^ 2 + 1) (hndvd : ¬ r ∣ p ^ 2 - 1)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (hV : Module.finrank (ZMod p) V = 4)
    (c : V ≃ₗ[ZMod p] V) (hc : ∃ k : ℕ, c ^ (r ^ k) = 1) (hne : c ≠ 1)
    (W : Submodule (ZMod p) V) (hW : ∀ w ∈ W, c w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  set F : Submodule (ZMod p) V := LinearMap.ker ((c : V →ₗ[ZMod p] V) - LinearMap.id) with hFdef
  have hfixF : ∀ v : V, c v = v ↔ v ∈ F := by
    intro v
    rw [hFdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have h1 := card_modEq_card_fixed_of_pow (G := V ≃ₗ[ZMod p] V) (X := V) r c hc
  have hFcard : Nat.card {x : V // c • x = x} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => hfixF v))
  rw [hFcard, natCard_eq_pow_finrank_zmod (U := V) p, natCard_eq_pow_finrank_zmod (U := F) p,
    hV] at h1
  have hfrF : Module.finrank (ZMod p) F ≤ 4 := hV ▸ Submodule.finrank_le F
  have hFdim : Module.finrank (ZMod p) F = 0 ∨ Module.finrank (ZMod p) F = 4 :=
    pow_modEq_one_forces hdvd hndvd hfrF (h1.symm.trans (pow_four_modEq_one hdvd))
  have hF0 : F = ⊥ := by
    rcases hFdim with h0 | h4
    · exact Submodule.finrank_eq_zero.mp h0
    · exfalso
      have hFtop : F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4, hV])
      apply hne
      apply LinearEquiv.ext
      intro v
      show c v = v
      exact (hfixF v).mpr (by rw [hFtop]; exact Submodule.mem_top)
  have hfix0 : ∀ v : V, c v = v → v = 0 := by
    intro v hv
    have := (hfixF v).mp hv
    rw [hF0] at this
    exact Submodule.mem_bot _ |>.mp this
  have hWmap : W.map (c : V →ₗ[ZMod p] V) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.map_le_iff_le_comap.mpr (fun w hw => hW w hw)
    · rw [LinearEquiv.finrank_map_eq]
  let cW : W ≃ₗ[ZMod p] W := LinearEquiv.ofSubmodules c W W hWmap
  have hcW_apply : ∀ (n : ℕ) (w : W), ((cW ^ n) w : V) = ((c ^ n) w : V) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [ih]
      rfl
  have hcWpow : ∃ k : ℕ, cW ^ (r ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hc
    refine ⟨k, LinearEquiv.ext fun w => Subtype.ext ?_⟩
    rw [hcW_apply, hk]
    rfl
  have h2 := card_modEq_card_fixed_of_pow (G := W ≃ₗ[ZMod p] W) (X := W) r cW hcWpow
  have hfixW : Nat.card {w : W // cW • w = w} = 1 := by
    have hz : ∀ a : {w : W // cW • w = w}, (a : W) = 0 := fun a => by
      apply Subtype.ext
      have ha : c ((a : W) : V) = ((a : W) : V) := congrArg Subtype.val a.2
      exact hfix0 _ ha
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ((hz a).trans (hz b).symm)⟩,
      ⟨⟨0, ?_⟩⟩⟩
    show cW 0 = 0
    simp
  rw [hfixW, natCard_eq_pow_finrank_zmod p] at h2
  have hfrW : Module.finrank (ZMod p) W ≤ 4 := hV ▸ Submodule.finrank_le W
  have hWdim : Module.finrank (ZMod p) W = 0 ∨ Module.finrank (ZMod p) W = 4 :=
    pow_modEq_one_forces hdvd hndvd hfrW h2
  rcases hWdim with h0 | h4
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (by rw [h4, hV]))

end CFSG.HardMathSupport.Curtis.Proving

end
