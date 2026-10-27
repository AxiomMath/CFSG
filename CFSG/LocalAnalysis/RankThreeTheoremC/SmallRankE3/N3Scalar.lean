module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

@[expose] def scalarSubgroup (q : ℕ) (E : Type) [Group E] (hq : q.Prime)
    (hexp : ∀ e : E, e ^ q = 1) (hnt : Nontrivial E) : Subgroup (MulAut E) where
  carrier := {g | ∃ k : ℕ, ∀ e : E, g e = e ^ k}
  mul_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m * n, fun e => ?_⟩
    rw [MulAut.mul_apply, hn, map_pow, hm, ← pow_mul]
  one_mem' := by
    refine ⟨1, fun e => ?_⟩
    rw [MulAut.one_apply, pow_one]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    have hqa : ¬ q ∣ a := by
      rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ := exists_ne (1 : E)
      apply hx
      apply g.injective
      rw [ha, pow_mul, hexp, one_pow, map_one]
    have hcop : Nat.Coprime a q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqa).symm
    obtain ⟨a', -, ha'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
    refine ⟨a', fun u => ?_⟩
    have key : ∀ x : E, x ^ (a * a') = x := fun x => by
      rw [pow_eq_pow_mod (a * a') (hexp x), ha', pow_one]
    calc (g⁻¹ : MulAut E) u = (g⁻¹ u) ^ (a * a') := (key _).symm
      _ = ((g⁻¹ u) ^ a) ^ a' := pow_mul _ _ _
      _ = (g (g⁻¹ u)) ^ a' := by rw [← ha]
      _ = u ^ a' := by rw [MulAut.apply_inv_self]

theorem scalarSubgroup_central {q : ℕ} {E : Type} [Group E] {hq : q.Prime}
    {hexp : ∀ e : E, e ^ q = 1} {hnt : Nontrivial E} :
    ∀ k ∈ scalarSubgroup q E hq hexp hnt, ∀ g : MulAut E, g * k = k * g := by
  rintro k ⟨a, ha⟩ g
  ext e
  simp only [MulAut.mul_apply, ha, map_pow]

theorem scalar_involution_cases {q : ℕ} {E : Type} [Group E] (hq : q.Prime)
    (hexp : ∀ e : E, e ^ q = 1) (hnt : Nontrivial E) (g : MulAut E) (a : ℕ)
    (ha : ∀ e : E, g e = e ^ a) (hg : g * g = 1) :
    g = 1 ∨ (a : ZMod q) = -1 := by
  haveI := Fact.mk hq
  obtain ⟨e0, he0⟩ := exists_ne (1 : E)
  have h1 : e0 ^ (a * a) = e0 := by
    have h := congrArg (fun h : MulAut E => h e0) hg
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [ha, ha, ← pow_mul] at h
    exact h
  have h2 : e0 ^ (a * a) = e0 ^ 1 := by rw [pow_one]; exact h1
  have hord : orderOf e0 = q := orderOf_eq_prime (hexp e0) he0
  have hmod : a * a ≡ 1 [MOD q] := by
    rw [← hord]
    exact pow_eq_pow_iff_modEq.1 h2
  have hsq : ((a * a : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at hsq
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · left
    have ha1 : a % q = 1 := by
      have h' : a ≡ 1 [MOD q] :=
        (ZMod.natCast_eq_natCast_iff a 1 q).1 (by rw [Nat.cast_one]; exact h)
      unfold Nat.ModEq at h'
      rw [h', Nat.mod_eq_of_lt hq.one_lt]
    ext e
    rw [ha, pow_eq_pow_mod a (hexp e), ha1, pow_one, MulAut.one_apply]
  · exact Or.inr h

theorem scalarSubgroup_two {q : ℕ} {E : Type} [Group E] [Finite E] {hq : q.Prime}
    {hexp : ∀ e : E, e ^ q = 1} {hnt : Nontrivial E} :
    ∀ k ∈ scalarSubgroup q E hq hexp hnt, k * k = 1 → ∀ k' ∈ scalarSubgroup q E hq hexp hnt,
      k' * k' = 1 → k = 1 ∨ k' = 1 ∨ k = k' := by
  rintro k ⟨a, ha⟩ hk k' ⟨b, hb⟩ hk'
  rcases scalar_involution_cases hq hexp hnt k a ha hk with h1 | h1
  · exact Or.inl h1
  rcases scalar_involution_cases hq hexp hnt k' b hb hk' with h2 | h2
  · exact Or.inr (Or.inl h2)
  right
  right
  have hab : a % q = b % q := (ZMod.natCast_eq_natCast_iff a b q).1 (by rw [h1, h2])
  ext e
  rw [ha, hb, pow_eq_pow_mod a (hexp e), pow_eq_pow_mod b (hexp e), hab]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
