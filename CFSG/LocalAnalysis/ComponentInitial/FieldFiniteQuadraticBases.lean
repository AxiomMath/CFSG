module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized
public import CFSG.LocalAnalysis.ComponentInitial.BinaryQuadraticRefinement

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

section Space

variable (V K : Type*) [AddCommGroup V] [Field K]

@[expose] def quadraticMapSpace : Submodule K (V → K) where
  carrier := {q | q 0 = 0 ∧ ∃ B : V →+ V →+ K, ∀ v w, B v w = q (v + w) + q v + q w}
  add_mem' := by
    rintro q q' ⟨h0, B, hB⟩ ⟨h0', B', hB'⟩
    refine ⟨by simp [h0, h0'], B + B', fun v w => ?_⟩
    simp only [AddMonoidHom.add_apply, Pi.add_apply, hB, hB']
    ring
  zero_mem' := ⟨rfl, 0, fun v w => by simp⟩
  smul_mem' := by
    rintro c q ⟨h0, B, hB⟩
    refine ⟨by simp [h0], c • B, fun v w => ?_⟩
    simp only [AddMonoidHom.smul_apply, Pi.smul_apply, smul_eq_mul, hB]
    ring

variable {V K}

theorem mem_quadraticMapSpace {q : V → K} :
    q ∈ quadraticMapSpace V K ↔
      q 0 = 0 ∧ ∃ B : V →+ V →+ K, ∀ v w, B v w = q (v + w) + q v + q w :=
  Iff.rfl

theorem diag_mem_quadraticMapSpace [CharP K 2] (b : V →+ V →+ K) :
    (fun v => b v v) ∈ quadraticMapSpace V K := by
  refine ⟨by simp, b + b.flip, fun v w => ?_⟩
  simp only [AddMonoidHom.add_apply, AddMonoidHom.flip_apply, map_add]
  linear_combination (-(b v v) - b w w) * (CharTwo.two_eq_zero : (2 : K) = 0)

end Space

section Monomials

variable {K : Type*} [Field K] [CharP K 2]

theorem pow_add_mem_quadraticMapSpace (i j : ℕ) :
    (fun x : K => x ^ (2 ^ i + 2 ^ j)) ∈ quadraticMapSpace K K := by
  have h : (fun x : K => x ^ (2 ^ i + 2 ^ j)) = fun x => frobPowHom₂ K 2 i j x x :=
    funext fun x => by rw [frobPowHom₂_apply, pow_add]
  rw [h]
  exact diag_mem_quadraticMapSpace _

theorem fst_pow_add_mem_quadraticMapSpace (i j : ℕ) :
    (fun v : K × K => v.1 ^ (2 ^ i + 2 ^ j)) ∈ quadraticMapSpace (K × K) K := by
  have h : (fun v : K × K => v.1 ^ (2 ^ i + 2 ^ j)) = fun v =>
      ((frobPowHom₂ K 2 i j).comp (AddMonoidHom.fst K K)).compl₂ (AddMonoidHom.fst K K) v v :=
    funext fun v => by simp [frobPowHom₂_apply, pow_add]
  rw [h]
  exact diag_mem_quadraticMapSpace _

theorem snd_pow_add_mem_quadraticMapSpace (i j : ℕ) :
    (fun v : K × K => v.2 ^ (2 ^ i + 2 ^ j)) ∈ quadraticMapSpace (K × K) K := by
  have h : (fun v : K × K => v.2 ^ (2 ^ i + 2 ^ j)) = fun v =>
      ((frobPowHom₂ K 2 i j).comp (AddMonoidHom.snd K K)).compl₂ (AddMonoidHom.snd K K) v v :=
    funext fun v => by simp [frobPowHom₂_apply, pow_add]
  rw [h]
  exact diag_mem_quadraticMapSpace _

theorem fst_pow_mul_snd_pow_mem_quadraticMapSpace (i j : ℕ) :
    (fun v : K × K => v.1 ^ 2 ^ i * v.2 ^ 2 ^ j) ∈ quadraticMapSpace (K × K) K := by
  have h : (fun v : K × K => v.1 ^ 2 ^ i * v.2 ^ 2 ^ j) = fun v =>
      ((frobPowHom₂ K 2 i j).comp (AddMonoidHom.fst K K)).compl₂ (AddMonoidHom.snd K K) v v :=
    funext fun v => by simp [frobPowHom₂_apply]
  rw [h]
  exact diag_mem_quadraticMapSpace _

end Monomials

theorem sum_sum_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → M) :
    ∑ i, ∑ j, F i j = ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2},
      if p.1.1 = p.1.2 then F p.1.1 p.1.2 else F p.1.1 p.1.2 + F p.1.2 p.1.1 := by
  classical
  rw [← Finset.sum_subtype (p := fun p : Fin n × Fin n => p.1 ≤ p.2)
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2) (fun p => by simp)
      (fun p : Fin n × Fin n => if p.1 = p.2 then F p.1 p.2 else F p.1 p.2 + F p.2 p.1),
    Finset.sum_filter, ← Fintype.sum_prod_type' F]
  have hswap : ∑ p : Fin n × Fin n, (if p.2 < p.1 then F p.1 p.2 else 0) =
      ∑ p : Fin n × Fin n, (if p.1 < p.2 then F p.2 p.1 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => rfl
  calc ∑ p : Fin n × Fin n, F p.1 p.2
      = ∑ p : Fin n × Fin n,
          ((if p.1 ≤ p.2 then F p.1 p.2 else 0) + (if p.2 < p.1 then F p.1 p.2 else 0)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p.1 ≤ p.2
        · simp [h, not_lt.2 h]
        · simp [h, not_le.1 h]
    _ = ∑ p : Fin n × Fin n,
          ((if p.1 ≤ p.2 then F p.1 p.2 else 0) + (if p.1 < p.2 then F p.2 p.1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hswap]
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · simp [h.le, h.ne, h]
        · simp [h]
        · simp [not_le.2 h, not_lt.2 h.le]

theorem card_pairs_le (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n * (n + 1) / 2 := by
  have h1 : ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2}, (if p.1.1 = p.1.2 then 1 else 1 + 1 : ℕ) =
      n * n := by
    rw [← sum_sum_eq_sum_le (M := ℕ) fun _ _ => 1]
    simp
  have h2 : ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2}, (if p.1.1 = p.1.2 then 1 else 0 : ℕ) = n := by
    have h := sum_sum_eq_sum_le (M := ℕ) (n := n) fun i j => if i = j then 1 else 0
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    refine (Finset.sum_congr rfl fun p _ => ?_).trans h.symm
    by_cases hp : p.1.1 = p.1.2
    · simp [hp]
    · simp [hp, Ne.symm hp]
  have h3 : ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2},
      ((if p.1.1 = p.1.2 then 1 else 1 + 1 : ℕ) + (if p.1.1 = p.1.2 then 1 else 0)) =
      ∑ _p : {p : Fin n × Fin n // p.1 ≤ p.2}, 2 :=
    Finset.sum_congr rfl fun p _ => by by_cases hp : p.1.1 = p.1.2 <;> simp [hp]
  rw [Finset.sum_add_distrib, h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h3
  rw [Nat.mul_succ]
  omega

section Criterion

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem exists_sq_eq (y : K) : ∃ x : K, x ^ 2 = y := by
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 (frobenius_inj K 2)) y
  exact ⟨x, by rwa [frobenius_def] at hx⟩

theorem coeff_eq_zero_of_forall_sum_sum_eq_zero {n : ℕ} (hn : 2 ^ (n - 1) < Fintype.card K)
    {C : Fin n → Fin n → K}
    (hC : ∀ x : K, ∑ i, ∑ j, C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) = 0) :
    (∀ i j, C i j + C j i = 0) ∧ ∀ i, C i i = 0 := by
  have hpol : ∀ x y : K,
      ∑ i, ∑ j, (C i j + C j i) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) = 0 := by
    intro x y
    have e : ∀ i j : Fin n, C i j * ((x + y) ^ 2 ^ (i : ℕ) * (x + y) ^ 2 ^ (j : ℕ)) =
        C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) +
          C i j * (y ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) +
          (C i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) +
            C i j * (y ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ))) := fun i j => by
      rw [add_pow_char_pow, add_pow_char_pow]
      ring
    have hswap : ∑ i, ∑ j, C i j * (y ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) =
        ∑ i, ∑ j, C j i * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h := hC (x + y)
    simp only [e, Finset.sum_add_distrib, hC x, hC y, zero_add, hswap] at h
    rw [← h]
    simp only [add_mul, Finset.sum_add_distrib]
  have hsym : ∀ i j, C i j + C j i = 0 := fun i j =>
    congrFun (congrFun (eq_zero_of_forall_sum_sum_mul_pow_eq_zero hn hpol) i) j
  refine ⟨hsym, ?_⟩
  have hdiag : ∀ x : K, ∑ i, C i i * (x ^ 2) ^ 2 ^ (i : ℕ) = 0 := by
    intro x
    rw [← hC x]
    have e1 : ∑ i, C i i * (x ^ 2) ^ 2 ^ (i : ℕ) =
        ∑ i, ∑ j, if i = j then C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ← pow_mul, ← pow_add, ← two_mul,
        ← pow_succ', pow_succ]
    rw [e1, sum_sum_eq_sum_le, sum_sum_eq_sum_le]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1.1 = p.1.2
    · simp [h]
    · have h0 : C p.1.1 p.1.2 * (x ^ 2 ^ (p.1.1 : ℕ) * x ^ 2 ^ (p.1.2 : ℕ)) +
          C p.1.2 p.1.1 * (x ^ 2 ^ (p.1.2 : ℕ) * x ^ 2 ^ (p.1.1 : ℕ)) = 0 := by
        rw [mul_comm (x ^ 2 ^ (p.1.2 : ℕ)), ← add_mul, hsym, zero_mul]
      simp [h, Ne.symm h, h0]
  intro i
  have h := eq_zero_of_forall_sum_mul_pow_eq_zero hn (a := fun i => C i i) fun y => by
    obtain ⟨x, rfl⟩ := exists_sq_eq y
    exact hdiag x
  exact congrFun h i

end Criterion

section Unary

variable {K : Type*} [Field K]

theorem exists_unary_expansion {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {q : K → K}
    (hq : q ∈ quadraticMapSpace K K) :
    ∃ a : {p : Fin n × Fin n // p.1 ≤ p.2} → K,
      ∀ x, q x = ∑ p, a p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨hq0, B, hB⟩ := hq
  obtain ⟨-, b, hb⟩ := binary_quadratic_bilinear_refinement q hq0 (addMonoidHom₂LinearEquiv K 2 B)
    fun u v => by rw [addMonoidHom₂LinearEquiv_apply, hB]
  obtain ⟨c, hc, -⟩ := (finite_field_linearized_linearMap_bases (p := 2) Nat.prime_two hn hK).2.1 b
  refine ⟨fun p => if p.1.1 = p.1.2 then c p.1.1 p.1.2 else c p.1.1 p.1.2 + c p.1.2 p.1.1,
    fun x => ?_⟩
  rw [← hb x, hc x x, sum_sum_eq_sum_le]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1.1 = p.1.2
  · simp only [h, ↓reduceIte, pow_add]
  · simp only [h, ↓reduceIte, pow_add, add_mul]
    rw [mul_comm (x ^ 2 ^ (p.1.2 : ℕ))]

theorem unary_expansion_unique [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 2 ^ (n - 1) < Fintype.card K) {a a' : {p : Fin n × Fin n // p.1 ≤ p.2} → K}
    (h : ∀ x : K, ∑ p, a p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) =
      ∑ p, a' p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ))) : a = a' := by
  classical
  let d := a - a'
  let C : Fin n → Fin n → K := fun i j => if hij : i ≤ j then d ⟨(i, j), hij⟩ else 0
  have hC : ∀ x : K, ∑ i, ∑ j, C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) =
      ∑ p, d p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) := fun x => by
    rw [sum_sum_eq_sum_le]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : C p.1.1 p.1.2 = d p := by simp [C, p.2]
    by_cases hpe : p.1.1 = p.1.2
    · simp only [hpe, ↓reduceIte] at hp ⊢
      rw [hp, pow_add]
    · have hlt : ¬ p.1.2 ≤ p.1.1 := fun hle => hpe (le_antisymm p.2 hle)
      simp only [hpe, ↓reduceIte, hp, C, hlt, ↓reduceDIte, zero_mul, add_zero,
        pow_add]
  have hd : ∀ x : K, ∑ i, ∑ j, C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) = 0 := fun x => by
    rw [hC x]
    simp only [d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, h x, sub_self]
  obtain ⟨hsym, hdiag⟩ := coeff_eq_zero_of_forall_sum_sum_eq_zero hn hd
  funext p
  rw [← sub_eq_zero]
  change d p = 0
  by_cases hpe : p.1.1 = p.1.2
  · have := hdiag p.1.1
    simp only [C, le_refl, ↓reduceDIte] at this
    rwa [show (⟨(p.1.1, p.1.1), le_refl _⟩ : {p : Fin n × Fin n // p.1 ≤ p.2}) = p from
      Subtype.ext (Prod.ext rfl hpe)] at this
  · have hlt : ¬ p.1.2 ≤ p.1.1 := fun hle => hpe (le_antisymm p.2 hle)
    have := hsym p.1.1 p.1.2
    simp only [C, p.2, hlt, ↓reduceDIte, add_zero] at this
    exact this

end Unary

section Binary

variable {K : Type*} [Field K]

theorem exists_binary_expansion {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {q : K × K → K} (hq : q ∈ quadraticMapSpace (K × K) K) :
    ∃ a : ({p : Fin n × Fin n // p.1 ≤ p.2} → K) × ({p : Fin n × Fin n // p.1 ≤ p.2} → K) ×
        (Fin n → Fin n → K),
      ∀ x y, q (x, y) = ∑ p, a.1 p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ p, a.2.1 p * y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ i, ∑ j, a.2.2 i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  obtain ⟨hq0, B, hB⟩ := hq
  have h1 : (fun x => q (x, 0)) ∈ quadraticMapSpace K K :=
    ⟨hq0, (B.comp (AddMonoidHom.inl K K)).compl₂ (AddMonoidHom.inl K K), fun x x' => by
      simp [hB]⟩
  have h2 : (fun y => q (0, y)) ∈ quadraticMapSpace K K :=
    ⟨hq0, (B.comp (AddMonoidHom.inr K K)).compl₂ (AddMonoidHom.inr K K), fun y y' => by
      simp [hB]⟩
  obtain ⟨a, ha⟩ := exists_unary_expansion hn hK h1
  obtain ⟨b, hb⟩ := exists_unary_expansion hn hK h2
  obtain ⟨c, hc, -⟩ := (finite_field_linearized_map_bases Nat.prime_two hn hK).2.1
    ((B.comp (AddMonoidHom.inl K K)).compl₂ (AddMonoidHom.inr K K))
  refine ⟨(a, b, c), fun x y => ?_⟩
  have hc' := hc x y
  simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.comp_apply, AddMonoidHom.inl_apply,
    AddMonoidHom.inr_apply, hB, Prod.mk_add_mk, add_zero, zero_add] at hc'
  rw [← ha x, ← hb y, ← hc']
  linear_combination (-(q (x, 0)) - q (0, y)) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem binary_expansion_unique [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 2 ^ (n - 1) < Fintype.card K)
    {a a' : ({p : Fin n × Fin n // p.1 ≤ p.2} → K) × ({p : Fin n × Fin n // p.1 ≤ p.2} → K) ×
      (Fin n → Fin n → K)}
    (h : ∀ x y : K, ∑ p, a.1 p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ p, a.2.1 p * y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ i, ∑ j, a.2.2 i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) =
      ∑ p, a'.1 p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ p, a'.2.1 p * y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
        ∑ i, ∑ j, a'.2.2 i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) : a = a' := by
  have hz : ∀ p : {p : Fin n × Fin n // p.1 ≤ p.2},
      (0 : K) ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) = 0 := fun p => zero_pow (by positivity)
  have hz' : ∀ i : Fin n, (0 : K) ^ 2 ^ (i : ℕ) = 0 := fun i => zero_pow (by positivity)
  have h1 : a.1 = a'.1 := unary_expansion_unique hn fun x => by
    simpa [hz, hz'] using h x 0
  have h2 : a.2.1 = a'.2.1 := unary_expansion_unique hn fun y => by
    simpa [hz, hz'] using h 0 y
  have h3 : a.2.2 = a'.2.2 := by
    have := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hn (a := a.2.2 - a'.2.2) fun x y => by
      have e := h x y
      rw [h1, h2, add_right_inj] at e
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, e, sub_self]
    funext i j
    exact sub_eq_zero.1 (congrFun (congrFun this i) j)
  exact Prod.ext h1 (Prod.ext h2 h3)

end Binary

theorem exists_basis_of_unique_expansion {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Fintype ι] (v : ι → M) (hspan : ∀ m : M, ∃ a : ι → K, m = ∑ i, a i • v i)
    (hli : ∀ a : ι → K, ∑ i, a i • v i = 0 → a = 0) :
    ∃ B : Module.Basis ι K M, ∀ i, B i = v i := by
  have hl : LinearIndependent K v :=
    Fintype.linearIndependent_iff.2 fun a ha i => congrFun (hli a ha) i
  have hs : ⊤ ≤ Submodule.span K (Set.range v) := fun m _ => by
    obtain ⟨a, rfl⟩ := hspan m
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hl hs, fun i => Module.Basis.mk_apply hl hs i⟩

theorem binary_finite_field_quadratic_map_bases {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    (∀ q ∈ quadraticMapSpace K K, ∃! a : {p : Fin n × Fin n // p.1 ≤ p.2} → K,
      ∀ x, q x = ∑ p, a p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ))) ∧
    (∀ q ∈ quadraticMapSpace (K × K) K,
      ∃! a : ({p : Fin n × Fin n // p.1 ≤ p.2} → K) × ({p : Fin n × Fin n // p.1 ≤ p.2} → K) ×
          (Fin n → Fin n → K),
        ∀ x y, q (x, y) = ∑ p, a.1 p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
          ∑ p, a.2.1 p * y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
          ∑ i, ∑ j, a.2.2 i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) ∧
    (∃ B : Module.Basis {p : Fin n × Fin n // p.1 ≤ p.2} K (quadraticMapSpace K K),
      ∀ p x, (B p : K → K) x = x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ))) ∧
    (∃ B : Module.Basis ({p : Fin n × Fin n // p.1 ≤ p.2} ⊕ {p : Fin n × Fin n // p.1 ≤ p.2} ⊕
        (Fin n × Fin n)) K (quadraticMapSpace (K × K) K),
      (∀ p x y, (B (.inl p) : K × K → K) (x, y) = x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ))) ∧
      (∀ p x y, (B (.inr (.inl p)) : K × K → K) (x, y) =
        y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ))) ∧
      ∀ i j x y, (B (.inr (.inr (i, j))) : K × K → K) (x, y) =
        x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) ∧
    Module.finrank K (quadraticMapSpace K K) = n * (n + 1) / 2 ∧
    Module.finrank K (quadraticMapSpace (K × K) K) = 2 * n ^ 2 + n := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  let v₁ : {p : Fin n × Fin n // p.1 ≤ p.2} → quadraticMapSpace K K := fun p =>
    ⟨fun x => x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)), pow_add_mem_quadraticMapSpace _ _⟩
  have hv₁ : ∀ (a : {p : Fin n × Fin n // p.1 ≤ p.2} → K) (x : K),
      ((∑ p, a p • v₁ p : quadraticMapSpace K K) : K → K) x =
        ∑ p, a p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) := fun a x => by
    simp [v₁, Finset.sum_apply]
  obtain ⟨B₁, hB₁⟩ := exists_basis_of_unique_expansion v₁
    (fun q => by
      obtain ⟨a, ha⟩ := exists_unary_expansion hn hK q.2
      exact ⟨a, Subtype.ext (funext fun x => by rw [hv₁, ha x])⟩)
    fun a ha => unary_expansion_unique hlt fun x => by
      have := congrFun (congrArg Subtype.val ha) x
      rw [hv₁] at this
      simpa using this
  let v₂ : ({p : Fin n × Fin n // p.1 ≤ p.2} ⊕ {p : Fin n × Fin n // p.1 ≤ p.2} ⊕
      (Fin n × Fin n)) → quadraticMapSpace (K × K) K :=
    Sum.elim (fun p => ⟨fun v => v.1 ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)),
        fst_pow_add_mem_quadraticMapSpace _ _⟩)
      (Sum.elim (fun p => ⟨fun v => v.2 ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)),
          snd_pow_add_mem_quadraticMapSpace _ _⟩)
        fun ij => ⟨fun v => v.1 ^ 2 ^ (ij.1 : ℕ) * v.2 ^ 2 ^ (ij.2 : ℕ),
          fst_pow_mul_snd_pow_mem_quadraticMapSpace _ _⟩)
  have hv₂ : ∀ (a : ({p : Fin n × Fin n // p.1 ≤ p.2} ⊕ {p : Fin n × Fin n // p.1 ≤ p.2} ⊕
      (Fin n × Fin n)) → K) (x y : K),
      ((∑ i, a i • v₂ i : quadraticMapSpace (K × K) K) : K × K → K) (x, y) =
        ∑ p, a (.inl p) * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
          ∑ p, a (.inr (.inl p)) * y ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) +
          ∑ i, ∑ j, a (.inr (.inr (i, j))) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
    intro a x y
    simp [v₂, Finset.sum_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      add_assoc]
  obtain ⟨B₂, hB₂⟩ := exists_basis_of_unique_expansion v₂
    (fun q => by
      obtain ⟨a, ha⟩ := exists_binary_expansion hn hK q.2
      refine ⟨Sum.elim a.1 (Sum.elim a.2.1 fun ij => a.2.2 ij.1 ij.2),
        Subtype.ext (funext fun v => ?_)⟩
      rw [show v = (v.1, v.2) from rfl, hv₂, ha v.1 v.2]
      rfl)
    fun a ha => by
      have key := binary_expansion_unique hlt
        (a := (fun p => a (.inl p), fun p => a (.inr (.inl p)),
          fun i j => a (.inr (.inr (i, j))))) (a' := 0) fun x y => by
        have := congrFun (congrArg Subtype.val ha) (x, y)
        rw [hv₂] at this
        simpa using this
      funext i
      rcases i with p | p | ⟨i, j⟩
      · exact congrFun (congrArg Prod.fst key) p
      · exact congrFun (congrArg (fun a => a.2.1) key) p
      · exact congrFun (congrFun (congrArg (fun a => a.2.2) key) i) j
  have huni₁ : ∀ q ∈ quadraticMapSpace K K, ∃! a : {p : Fin n × Fin n // p.1 ≤ p.2} → K,
      ∀ x, q x = ∑ p, a p * x ^ (2 ^ (p.1.1 : ℕ) + 2 ^ (p.1.2 : ℕ)) := fun q hq => by
    obtain ⟨a, ha⟩ := exists_unary_expansion hn hK hq
    exact ⟨a, ha, fun a' ha' => unary_expansion_unique hlt fun x => by rw [← ha' x, ← ha x]⟩
  refine ⟨huni₁, fun q hq => ?_, ⟨B₁, fun p x => by rw [hB₁]⟩,
    ⟨B₂, fun p x y => by rw [hB₂]; rfl, fun p x y => by rw [hB₂]; rfl,
      fun i j x y => by rw [hB₂]; rfl⟩, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_binary_expansion hn hK hq
    exact ⟨a, ha, fun a' ha' => binary_expansion_unique hlt fun x y => by
      rw [← ha' x y, ← ha x y]⟩
  · rw [Module.finrank_eq_card_basis B₁, card_pairs_le]
  · rw [Module.finrank_eq_card_basis B₂, Fintype.card_sum, Fintype.card_sum, card_pairs_le,
      Fintype.card_prod, Fintype.card_fin]
    have h2 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    nlinarith [hk]

end CFSG.LocalAnalysis.ComponentInitial
