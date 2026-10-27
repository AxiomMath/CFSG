module

public import CFSG.GH74.GLS.Balance.Bender.Ambient

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem l55_exists_pow_coprime {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] (g : G) :
    ∃ k : ℕ, Nat.Coprime (orderOf (g ^ (p ^ k))) p := by
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨(orderOf g).factorization p, ?_⟩
  rw [orderOf_pow' g (pow_ne_zero _ hp.ne_zero)]
  have hd : p ^ (orderOf g).factorization p ∣ orderOf g := Nat.ordProj_dvd (orderOf g) p
  rw [Nat.gcd_eq_right hd]
  exact (Nat.coprime_ordCompl hp hn0).symm

theorem l55_pow_mem_oResOf {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {B : Subgroup G}
    {b : G} (hb : b ∈ B) : ∃ k : ℕ, b ^ (p ^ k) ∈ oResOf p B := by
  obtain ⟨k, hk⟩ := l55_exists_pow_coprime (Fact.out : p.Prime) b
  exact ⟨k, mem_oResOf (B.pow_mem hb _) hk⟩

theorem l55_mem_of_pow_mem {p : ℕ} {G : Type*} [Group G] [Finite G] {K : Subgroup G} {y : G}
    (hy : Nat.Coprime (orderOf y) p) (k : ℕ) (h : y ^ (p ^ k) ∈ K) : y ∈ K := by
  have hcop : Nat.Coprime (p ^ k) (orderOf y) := (hy.pow_right k).symm
  rcases Nat.lt_or_ge 1 (orderOf y) with h1 | h1
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : y = (y ^ (p ^ k)) ^ m := by
      rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
    rw [this]; exact K.pow_mem h m
  · have h0 : orderOf y = 1 := le_antisymm h1 (orderOf_pos y)
    have : y = 1 := orderOf_eq_one_iff.mp h0
    rw [this]; exact K.one_mem

theorem l55_mul_pow_mem {G : Type*} [Group G] {A : Subgroup G} {a b : G} (ha : a ∈ A)
    (hb : b ∈ normalizer (A : Set G)) (j : ℕ) : ∃ a' ∈ A, (a * b) ^ j = a' * b ^ j := by
  induction j with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hbj : b ^ j ∈ normalizer (A : Set G) := Subgroup.pow_mem _ hb j
    have hc : b ^ j * a * (b ^ j)⁻¹ ∈ A := (mem_normalizer_iff.mp hbj a).mp ha
    refine ⟨a' * (b ^ j * a * (b ^ j)⁻¹), A.mul_mem ha' hc, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem l55_aux {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {X A B : Subgroup G}
    (hX : oResOf p X = X) (hBn : B ≤ normalizer (A : Set G)) (hXAB : X ≤ A ⊔ B) :
    X ≤ A ⊔ oResOf p B := by
  calc X = oResOf p X := hX.symm
    _ ≤ A ⊔ oResOf p B := by
      apply oResOf_le_of
      intro x hx hxp
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hBn).1 (hXAB hx)
      obtain ⟨k, hk⟩ := l55_pow_mem_oResOf (p := p) hb
      obtain ⟨a', ha', h'⟩ := l55_mul_pow_mem ha (hBn hb) (p ^ k)
      refine l55_mem_of_pow_mem hxp k ?_
      rw [h']
      exact mul_mem_sup ha' hk

theorem l55_orderOf_conj {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h : SemiconjBy g x (g * x * g⁻¹) := by
    simp [SemiconjBy, mul_assoc]
  exact (h.orderOf_eq g).symm

theorem l55_conj_mem_oResOf {p : ℕ} {G : Type} [Group G] {C : Subgroup G} {g : G}
    (hg : g ∈ normalizer (C : Set G)) {x : G} (hx : x ∈ oResOf p C) :
    g * x * g⁻¹ ∈ oResOf p C := by
  rw [oResOf_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨(mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    rw [l55_orderOf_conj]; exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

theorem l55_le_normalizer_oResOf {p : ℕ} {G : Type} [Group G] {C P : Subgroup G}
    (h : P ≤ normalizer (C : Set G)) : P ≤ normalizer (oResOf p C : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨l55_conj_mem_oResOf (h hg), fun hx => ?_⟩
  have hg' : g⁻¹ ∈ normalizer (C : Set G) := Subgroup.inv_mem _ (h hg)
  have := l55_conj_mem_oResOf (p := p) hg' hx
  simpa [mul_assoc] using this

theorem l55_map_conj_eq {G : Type*} [Group G] {H : Subgroup G} {c : G}
    (hc : c ∈ normalizer (H : Set G)) : H.map (MulAut.conj c).toMonoidHom = H := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hc y).mp hy
  · intro hz
    refine ⟨c⁻¹ * z * c, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp hc (c⁻¹ * z * c)).mpr (by simpa [mul_assoc] using hz)
      exact h1
    · simp [MulAut.conj_apply, mul_assoc]

theorem l55_mem_normalizer_commutator {G : Type*} [Group G] {X P : Subgroup G} {c : G}
    (hcX : c ∈ normalizer (X : Set G)) (hcP : c ∈ centralizer (P : Set G)) :
    c ∈ normalizer ((⁅X, P⁆ : Subgroup G) : Set G) := by
  have hP : P.map (MulAut.conj c).toMonoidHom = P := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := mem_centralizer_iff.mp hcP y hy
      have h2 : c * y * c⁻¹ = y := by
        calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [this]
          _ = y := by simp
      simpa [MulAut.conj_apply, h2] using hy
    · intro hz
      refine ⟨z, hz, ?_⟩
      have := mem_centralizer_iff.mp hcP z hz
      calc (MulAut.conj c).toMonoidHom z = c * z * c⁻¹ := rfl
        _ = z * c * c⁻¹ := by rw [this]
        _ = z := by simp
  have hmap : (⁅X, P⁆).map (MulAut.conj c).toMonoidHom = ⁅X, P⁆ := by
    rw [Subgroup.map_commutator, l55_map_conj_eq hcX, hP]
  rw [mem_normalizer_iff]
  intro z
  rw [← Subgroup.mem_map_iff_mem (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective, hmap]
  rfl

end CFSG.GH74.GLS.Balance
