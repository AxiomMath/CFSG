module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open scoped Pointwise

@[expose] def fixS {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (g : G) :
    Finset Ω := Finset.univ.filter fun i => g • i = i

theorem mem_fixS {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {g : G} {i : Ω} : i ∈ (fixS g : Finset Ω) ↔ g • i = i := by simp [fixS]

section General

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

theorem card_fixS_conj (c g : G) :
    (fixS (c * g * c⁻¹) : Finset Ω).card = (fixS g : Finset Ω).card := by
  refine Finset.card_bij (fun i _ => c⁻¹ • i) ?_ ?_ ?_
  · intro i hi
    rw [mem_fixS] at hi ⊢
    have h1 : ((c * g * c⁻¹) • i) = i := hi
    have h2 : c • g • c⁻¹ • i = i := by simpa [mul_smul] using h1
    calc g • c⁻¹ • i = c⁻¹ • (c • g • c⁻¹ • i) := (inv_smul_smul c _).symm
      _ = c⁻¹ • i := by rw [h2]
  · intro i _ j _ h
    simpa using h
  · intro j hj
    refine ⟨c • j, ?_, by simp⟩
    rw [mem_fixS] at hj ⊢
    have : ((c * g * c⁻¹) • c • j) = c • j := by
      calc ((c * g * c⁻¹) • c • j) = c • g • j := by simp [mul_smul]
        _ = c • j := by rw [hj]
    exact this

theorem card_fixS_conj_inv (g x : G) :
    (fixS (g⁻¹ * x * g) : Finset Ω).card = (fixS x : Finset Ω).card := by
  have := card_fixS_conj (Ω := Ω) g⁻¹ x
  rwa [inv_inv] at this

theorem card_modEq_filter {p : ℕ} [Fact p.Prime] {y : G} (hy : y ^ p = 1) (S : Finset Ω)
    (hS : ∀ i ∈ S, y • i ∈ S) :
    S.card ≡ (S.filter fun i => y • i = i).card [MOD p] := by
  let f : Function.End S := fun i => ⟨y • i.1, hS i.1 i.2⟩
  have hfk : ∀ k : ℕ, ∀ i : S, ((f ^ k) i).1 = (y ^ k) • i.1 := by
    intro k
    induction k with
    | zero => intro i; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ k ih =>
      intro i
      rw [pow_succ', Function.End.mul_def]
      change y • ((f ^ k) i).1 = _
      rw [ih, pow_succ', mul_smul]
  have hf : f ^ p ^ 1 = 1 := by
    funext i
    apply Subtype.ext
    rw [pow_one, hfk, hy, one_smul]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_coe] at h
  convert h using 1
  rw [Fintype.card_subtype]
  refine (Finset.card_bij (fun (x : S) _ => x.1) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_fixedPoints,
      Function.IsFixedPt] at hx
    have := congrArg Subtype.val hx
    exact Finset.mem_filter.2 ⟨x.2, this⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro i hi
    obtain ⟨hiS, hiy⟩ := Finset.mem_filter.1 hi
    refine ⟨⟨i, hiS⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_fixedPoints,
      Function.IsFixedPt]
    exact Subtype.ext hiy

theorem card_fix_modEq_of_commute {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {x y : G} (hx : x ^ p = 1)
    (hy : y ^ q = 1) (hxy : x * y = y * x) :
    ∃ k : ℕ, k ≤ (fixS y : Finset Ω).card ∧ (fixS x : Finset Ω).card ≡ k [MOD q] ∧
      (fixS y : Finset Ω).card ≡ k [MOD p] := by
  have hS1 : ∀ i ∈ (fixS x : Finset Ω), y • i ∈ (fixS x : Finset Ω) := by
    intro i hi
    rw [mem_fixS] at hi ⊢
    calc x • y • i = (x * y) • i := (mul_smul x y i).symm
      _ = (y * x) • i := by rw [hxy]
      _ = y • x • i := mul_smul y x i
      _ = y • i := by rw [hi]
  have hS2 : ∀ i ∈ (fixS y : Finset Ω), x • i ∈ (fixS y : Finset Ω) := by
    intro i hi
    rw [mem_fixS] at hi ⊢
    calc y • x • i = (y * x) • i := (mul_smul y x i).symm
      _ = (x * y) • i := by rw [hxy]
      _ = x • y • i := mul_smul x y i
      _ = x • i := by rw [hi]
  have e1 := card_modEq_filter (p := q) hy _ hS1
  have e2 := card_modEq_filter (p := p) hx _ hS2
  have hset : ((fixS x : Finset Ω).filter fun i => y • i = i) =
      ((fixS y : Finset Ω).filter fun i => x • i = i) := by
    ext i
    simp only [Finset.mem_filter, mem_fixS]
    tauto
  refine ⟨((fixS x : Finset Ω).filter fun i => y • i = i).card, ?_, e1, ?_⟩
  · rw [hset]
    exact Finset.card_filter_le _ _
  · rw [hset]
    exact e2

theorem fixS_subset_pow (g : G) (n : ℕ) : (fixS g : Finset Ω) ⊆ fixS (g ^ n) := by
  intro i hi
  rw [mem_fixS] at hi ⊢
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, hi, ih]

theorem fixS_pow_eq {g : G} {n m : ℕ} (h : (g ^ n) ^ m = g) :
    (fixS (g ^ n) : Finset Ω) = fixS g := by
  apply Finset.Subset.antisymm
  · have := fixS_subset_pow (Ω := Ω) (g ^ n) m
    rw [h] at this
    exact fun i hi => this hi
  · exact fixS_subset_pow g n

theorem exists_conj_le_sylow_of_card [Finite G] {p : ℕ} [Fact p.Prime] (P K : Subgroup G)
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) (hK : IsPGroup p K) :
    ∃ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ P := by
  obtain ⟨Q, hKQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  have hP' : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] using this.symm
  refine ⟨g, fun k hk => ?_⟩
  rw [hP']
  exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
    ⟨k, hKQ hk, by simp [MulAut.smul_def]⟩

end General

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
