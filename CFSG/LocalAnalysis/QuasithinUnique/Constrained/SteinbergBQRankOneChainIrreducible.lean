module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.QuasithinUnique

open Module

namespace SteinbergBQ.RankOne

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem inv_apply_apply (t : LinearMap.GeneralLinearGroup F V) (x : V) :
    ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) ((t : V →ₗ[F] V) x) = x := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem apply_inv_apply (t : LinearMap.GeneralLinearGroup F V) (x : V) :
    (t : V →ₗ[F] V) (((t⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x) = x := by
  rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

variable {t : LinearMap.GeneralLinearGroup F V} {v : V} {φ : Dual F V}

theorem mem_of_rankOne (h : ∀ x, (t : V →ₗ[F] V) x - x = φ x • v) {U : Submodule F V}
    (hv : v ∈ U) {u : V} (hu : u ∈ U) : (t : V →ₗ[F] V) u ∈ U := by
  have h1 : (t : V →ₗ[F] V) u = u + φ u • v := by rw [← h u]; abel
  rw [h1]
  exact U.add_mem hu (U.smul_mem _ hv)

theorem apply_eq_of_rankOne (h : ∀ x, (t : V →ₗ[F] V) x - x = φ x • v) {u : V} (hu : φ u = 0) :
    (t : V →ₗ[F] V) u = u := by
  have h1 := h u
  rw [hu, zero_smul, sub_eq_zero] at h1
  exact h1

theorem inv_mem_of_rankOne (h : ∀ x, (t : V →ₗ[F] V) x - x = φ x • v) {U : Submodule F V}
    (hv : v ∈ U) {u : V} (hu : u ∈ U) :
    ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) u ∈ U := by
  set y := ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) u
  have h1 : (t : V →ₗ[F] V) y = u := apply_inv_apply t u
  have h2 : y = u - φ y • v := by
    rw [← h1, ← h y]
    abel
  rw [h2]
  exact U.sub_mem hu (U.smul_mem _ hv)

theorem inv_apply_eq_of_rankOne (h : ∀ x, (t : V →ₗ[F] V) x - x = φ x • v) {u : V}
    (hu : φ u = 0) : ((t⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) u = u := by
  conv_lhs => rw [← apply_eq_of_rankOne h hu]
  exact inv_apply_apply t u

theorem closure_preserves {D : Set (LinearMap.GeneralLinearGroup F V)}
    {v : LinearMap.GeneralLinearGroup F V → V} {φ : LinearMap.GeneralLinearGroup F V → Dual F V}
    (h : ∀ t ∈ D, ∀ x, (t : V →ₗ[F] V) x - x = φ t x • v t) {U : Submodule F V}
    (hU : ∀ t ∈ D, v t ∈ U ∨ ∀ u ∈ U, φ t u = 0) {n : LinearMap.GeneralLinearGroup F V}
    (hn : n ∈ Subgroup.closure D) : ∀ u ∈ U, (n : V →ₗ[F] V) u ∈ U := by
  induction hn using Subgroup.closure_induction'' with
  | mem t ht =>
    intro u hu
    rcases hU t ht with h1 | h1
    · exact mem_of_rankOne (h t ht) h1 hu
    · rw [apply_eq_of_rankOne (h t ht) (h1 u hu)]
      exact hu
  | inv_mem t ht =>
    intro u hu
    rcases hU t ht with h1 | h1
    · exact inv_mem_of_rankOne (h t ht) h1 hu
    · rw [inv_apply_eq_of_rankOne (h t ht) (h1 u hu)]
      exact hu
  | one =>
    intro u hu
    exact hu
  | mul x y _ _ hx hy =>
    intro u hu
    rw [Units.val_mul, Module.End.mul_apply]
    exact hx _ (hy u hu)

theorem eq_zero_of_span_eq_top {S : Set (Dual F V)} (hS : Submodule.span F S = ⊤) {u : V}
    (hu : ∀ ψ ∈ S, ψ u = 0) : u = 0 := by
  have h1 : Submodule.span F S ≤ LinearMap.ker (Dual.eval F V u) :=
    Submodule.span_le.2 fun ψ hψ => hu ψ hψ
  rw [hS, top_le_iff] at h1
  refine (forall_dual_apply_eq_zero_iff F u).1 fun ψ => ?_
  have h2 : ψ ∈ LinearMap.ker (Dual.eval F V u) := by rw [h1]; exact Submodule.mem_top
  exact h2

theorem span_eq_top_of_forall [FiniteDimensional F V] {S : Set (Dual F V)}
    (hS : ∀ u : V, (∀ ψ ∈ S, ψ u = 0) → u = 0) : Submodule.span F S = ⊤ := by
  have h1 : (Submodule.span F S).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    exact hS u fun ψ hψ => hu ψ (Submodule.subset_span hψ)
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span F S)
  rw [h1, finrank_bot, add_zero, ← Subspace.dual_finrank_eq] at h2
  exact Submodule.eq_top_of_finrank_eq h2

theorem exists_chain_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ (k : ℕ) (c : ℕ → α), c 0 = a ∧ c k = b ∧ ∀ i < k, r (c i) (c (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b' c' _ hbc ih =>
    obtain ⟨k, c, hc0, hck, hc⟩ := ih
    classical
    refine ⟨k + 1, fun i => if i ≤ k then c i else c', by simp [hc0], by simp, fun i hi => ?_⟩
    by_cases hik : i + 1 ≤ k
    · simp only [show i ≤ k by omega, hik, ite_true]
      exact hc i (by omega)
    · have hik' : i = k := by omega
      subst hik'
      simp only [le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false, hck]
      exact hbc

end SteinbergBQ.RankOne

open SteinbergBQ.RankOne

theorem rank_one_generator_chain_irreducibility_criterion {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (D : Finset (LinearMap.GeneralLinearGroup F V)) (hD : D.Nonempty)
    (_hrank : ∀ t ∈ D, finrank F (LinearMap.range ((t : V →ₗ[F] V) - 1)) = 1)
    (v : LinearMap.GeneralLinearGroup F V → V) (φ : LinearMap.GeneralLinearGroup F V → Dual F V)
    (hv : ∀ t ∈ D, v t ≠ 0) (hφ : ∀ t ∈ D, φ t ≠ 0)
    (hvφ : ∀ t ∈ D, ∀ x, ((t : V →ₗ[F] V) - 1) x = φ t x • v t) :
    (∀ U : Submodule F V, (∀ n ∈ Subgroup.closure (D : Set (LinearMap.GeneralLinearGroup F V)),
        ∀ u ∈ U, (n : V →ₗ[F] V) u ∈ U) → U = ⊥ ∨ U = ⊤) ↔
      (Submodule.span F (v '' D) = ⊤ ∧ Submodule.span F (φ '' D) = ⊤ ∧
        ∀ s ∈ D, ∀ t ∈ D, ∃ (k : ℕ) (c : ℕ → LinearMap.GeneralLinearGroup F V), c 0 = s ∧
          c k = t ∧ (∀ i ≤ k, c i ∈ D) ∧ ∀ i < k, φ (c i) (v (c (i + 1))) ≠ 0) := by
  classical
  have h : ∀ t ∈ (D : Set (LinearMap.GeneralLinearGroup F V)), ∀ x,
      (t : V →ₗ[F] V) x - x = φ t x • v t := fun t ht x => by
    rw [← hvφ t ht x, LinearMap.sub_apply, Module.End.one_apply]
  set edge : LinearMap.GeneralLinearGroup F V → LinearMap.GeneralLinearGroup F V → Prop :=
    fun a b => a ∈ D ∧ b ∈ D ∧ φ a (v b) ≠ 0 with hedge
  have hpath : ∀ s ∈ D, ∀ t ∈ D, Relation.ReflTransGen edge s t →
      ∃ (k : ℕ) (c : ℕ → LinearMap.GeneralLinearGroup F V), c 0 = s ∧ c k = t ∧
        (∀ i ≤ k, c i ∈ D) ∧ ∀ i < k, φ (c i) (v (c (i + 1))) ≠ 0 := by
    intro s hs t _ hst
    obtain ⟨k, c, hc0, hck, hc⟩ := exists_chain_of_reflTransGen hst
    refine ⟨k, c, hc0, hck, fun i hi => ?_, fun i hi => (hc i hi).2.2⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hc0]
      exact hs
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact (hc j (by omega)).2.1
  constructor
  · intro hirr
    obtain ⟨t₀, ht₀⟩ := hD
    have hspan : Submodule.span F (v '' D) = ⊤ := by
      have hmem : ∀ t ∈ (D : Set (LinearMap.GeneralLinearGroup F V)),
          v t ∈ Submodule.span F (v '' D) := fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
      rcases hirr (Submodule.span F (v '' D)) fun n hn => closure_preserves h
        (fun t ht => Or.inl (hmem t ht)) hn with h1 | h1
      · exfalso
        apply hv t₀ ht₀
        have h2 : v t₀ ∈ Submodule.span F (v '' D) := Submodule.subset_span ⟨t₀, ht₀, rfl⟩
        rw [h1] at h2
        exact (Submodule.mem_bot F).1 h2
      · exact h1
    refine ⟨hspan, ?_, fun s hs t ht => hpath s hs t ht ?_⟩
    ·
      apply span_eq_top_of_forall
      set K : Submodule F V := ⨅ t ∈ D, LinearMap.ker (φ t) with hK
      have hmemK : ∀ u, u ∈ K ↔ ∀ t ∈ D, φ t u = 0 := fun u => by
        simp only [hK, Submodule.mem_iInf, LinearMap.mem_ker]
      rcases hirr K fun n hn => closure_preserves h (fun t ht => Or.inr fun u hu =>
          (hmemK u).1 hu t ht) hn with h1 | h1
      · intro u hu
        have h2 : u ∈ K := (hmemK u).2 fun t ht => hu _ ⟨t, ht, rfl⟩
        rw [h1] at h2
        exact (Submodule.mem_bot F).1 h2
      · exfalso
        apply hφ t₀ ht₀
        ext x
        exact (hmemK x).1 (h1 ▸ Submodule.mem_top) t₀ ht₀
    ·
      set U : Submodule F V :=
        Submodule.span F (v '' {a | a ∈ D ∧ Relation.ReflTransGen edge a t}) with hU
      have hUinv : ∀ b ∈ (D : Set (LinearMap.GeneralLinearGroup F V)),
          v b ∈ U ∨ ∀ u ∈ U, φ b u = 0 := by
        intro b hb
        by_cases hbt : Relation.ReflTransGen edge b t
        · exact Or.inl (Submodule.subset_span ⟨b, ⟨hb, hbt⟩, rfl⟩)
        · refine Or.inr fun u hu => ?_
          have h1 : U ≤ LinearMap.ker (φ b) := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨a, ⟨ha, hat⟩, rfl⟩
            by_contra h2
            exact hbt (Relation.ReflTransGen.head ⟨hb, ha, h2⟩ hat)
          exact h1 hu
      rcases hirr U fun n hn => closure_preserves h hUinv hn with h1 | h1
      · exfalso
        apply hv t ht
        have h2 : v t ∈ U := Submodule.subset_span ⟨t, ⟨ht, Relation.ReflTransGen.refl⟩, rfl⟩
        rw [h1] at h2
        exact (Submodule.mem_bot F).1 h2
      ·
        by_contra hst
        have h2 : U ≤ LinearMap.ker (φ s) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨a, ⟨ha, hat⟩, rfl⟩
          by_contra h3
          exact hst (Relation.ReflTransGen.head ⟨hs, ha, h3⟩ hat)
        apply hφ s hs
        ext x
        exact h2 (h1 ▸ Submodule.mem_top)
  · rintro ⟨hspan, hspanφ, hconn⟩ U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨t, ht, htu⟩ : ∃ t ∈ D, φ t u ≠ 0 := by
      by_contra h1
      push Not at h1
      exact hu0 (eq_zero_of_span_eq_top hspanφ fun ψ ⟨t, ht, hψ⟩ => hψ ▸ h1 t ht)
    have hstep : ∀ a ∈ D, ∀ b ∈ D, φ a (v b) ≠ 0 → v b ∈ U → v a ∈ U := by
      intro a ha b _ hab hb
      have h1 : (a : V →ₗ[F] V) (v b) - v b ∈ U :=
        U.sub_mem (hU a (Subgroup.subset_closure ha) _ hb) hb
      rw [h a ha] at h1
      exact (U.smul_mem_iff hab).1 h1
    have hvt : v t ∈ U := by
      have h1 : (t : V →ₗ[F] V) u - u ∈ U :=
        U.sub_mem (hU t (Subgroup.subset_closure ht) _ huU) huU
      rw [h t ht] at h1
      exact (U.smul_mem_iff htu).1 h1
    have hall : ∀ s ∈ D, v s ∈ U := by
      intro s hs
      obtain ⟨k, c, hc0, hck, hcD, hc⟩ := hconn s hs t ht
      have h1 : ∀ j ≤ k, v (c (k - j)) ∈ U := by
        intro j hj
        induction j with
        | zero => rw [Nat.sub_zero, hck]; exact hvt
        | succ j ih =>
          have h2 := ih (by omega)
          have h3 : k - j = k - (j + 1) + 1 := by omega
          rw [h3] at h2
          exact hstep _ (hcD _ (by omega)) _ (hcD _ (by omega)) (hc _ (by omega)) h2
      have h2 := h1 k le_rfl
      rw [Nat.sub_self, hc0] at h2
      exact h2
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hall s hs

end CFSG.QuasithinUnique
