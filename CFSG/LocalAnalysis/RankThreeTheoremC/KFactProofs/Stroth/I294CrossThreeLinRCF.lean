module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace LinThree

open Module

section Triple

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def tri (s t : V) (k : ZMod 3) : V :=
  if k = 0 then s else if k = 1 then t else -s - t

theorem zmod3_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k
  decide

@[simp] theorem tri_zero (s t : V) : tri s t 0 = s := by simp [tri]

@[simp] theorem tri_one (s t : V) : tri s t 1 = t := by simp [tri]

@[simp] theorem tri_two (s t : V) : tri s t 2 = -s - t := by
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  simp [tri, h20, h21]

theorem tri_add_two (s t : V) (m : ZMod 3) :
    tri s t (m + 2) = -tri s t m - tri s t (m + 1) := by
  rcases zmod3_cases m with rfl | rfl | rfl
  · simp
  · have : (1 : ZMod 3) + 2 = 0 := by decide
    have h : (1 : ZMod 3) + 1 = 2 := by decide
    rw [this, h, tri_zero, tri_one, tri_two]
    abel
  · have h1 : (2 : ZMod 3) + 2 = 1 := by decide
    have h2 : (2 : ZMod 3) + 1 = 0 := by decide
    rw [h1, h2]
    simp

theorem tri_mem_span (s t : V) (k : ZMod 3) : tri s t k ∈ Submodule.span K {s, t} := by
  rcases zmod3_cases k with rfl | rfl | rfl
  · simpa using Submodule.subset_span (by simp)
  · simpa using Submodule.subset_span (by simp)
  · rw [tri_two]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))

theorem map_tri (T : V →ₗ[K] V) {s t : V} {c : ZMod 3} (hs : T s = tri s t c)
    (ht : T t = tri s t (c + 1)) (k : ZMod 3) : T (tri s t k) = tri s t (k + c) := by
  rcases zmod3_cases k with rfl | rfl | rfl
  · simpa using hs
  · rw [tri_one, ht, add_comm]
  · rw [tri_two, map_sub, map_neg, hs, ht, add_comm (2 : ZMod 3) c, tri_add_two]

@[expose] def GoodRel (g : Module.End K V) (s t : V) : Prop :=
  ∃ c : ZMod 3, g s = tri s t c ∧ g t = tri s t (c + 1)

theorem GoodRel.maps_span {g : Module.End K V} {s t : V} (h : GoodRel g s t) :
    ∀ x ∈ Submodule.span K {s, t}, g x ∈ Submodule.span K {s, t} := by
  obtain ⟨c, hs, ht⟩ := h
  intro x hx
  have hmap : (Submodule.span K {s, t}).map g ≤ Submodule.span K {s, t} := by
    rw [Submodule.map_span_le]
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm
    · rw [hm, hs]
      exact tri_mem_span _ _ _
    · rw [hm, ht]
      exact tri_mem_span _ _ _
  exact hmap ⟨x, hx, rfl⟩

end Triple

section GoodPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem pow_three_apply {g : Module.End K V} (hg3 : g ^ 3 = 1) (x : V) : g (g (g x)) = x := by
  have := congrArg (fun f : Module.End K V => f x) hg3
  simpa [pow_succ] using this

theorem eq_zero_of_norm_form {K : Type*} [Field K] (hroot : ∀ x : K, x ^ 2 + x + 1 ≠ 0) {α β : K}
    (h : α ^ 2 - α * β + β ^ 2 = 0) : α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    refine hroot (-(α / β)) ?_
    field_simp
    linear_combination h

theorem exists_goodPlane (g : Module.End K V) (hg3 : g ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    (hroot : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (S : Submodule K V) (hS : ∀ x ∈ S, g x ∈ S)
    (hdim : finrank K S + 2 ≤ finrank K V) :
    ∃ s t : V, GoodRel g s t ∧ ∀ α β : K, α • s + β • t ∈ S → α = 0 ∧ β = 0 := by
  have hg : ∀ x, g (g (g x)) = x := pow_three_apply hg3
  by_cases hω : ∃ v : V, g (g v) + g v + v = 0 ∧ v ∉ S
  · obtain ⟨v, hv, hvS⟩ := hω
    have hgg : g (g v) = -v - g v := eq_sub_of_add_eq (eq_neg_of_add_eq_zero_left hv)
    refine ⟨v, g v, ⟨1, ?_, ?_⟩, ?_⟩
    · simp
    · have h11 : (1 : ZMod 3) + 1 = 2 := by decide
      rw [h11, tri_two, hgg]
    · intro α β hαβ
      have hgx : g (α • v + β • g v) = (-β) • v + (α - β) • g v := by
        rw [map_add, map_smul, map_smul, hgg]
        module
      have hgxS : g (α • v + β • g v) ∈ S := hS _ hαβ
      have hΔ : (α ^ 2 - α * β + β ^ 2) • v =
          (α - β) • (α • v + β • g v) - β • g (α • v + β • g v) := by
        rw [hgx]
        module
      have hΔ0 : α ^ 2 - α * β + β ^ 2 = 0 := by
        by_contra hne
        apply hvS
        have hmem : (α ^ 2 - α * β + β ^ 2) • v ∈ S := by
          rw [hΔ]
          exact S.sub_mem (S.smul_mem _ hαβ) (S.smul_mem _ hgxS)
        have := S.smul_mem (α ^ 2 - α * β + β ^ 2)⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      exact eq_zero_of_norm_form hroot hΔ0
  · push Not at hω
    have hlift : ∀ q : V ⧸ S, ∃ u : V, g u = u ∧ Submodule.Quotient.mk u = q := by
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective S q
      set y : V := x + g x + g (g x) with hy
      set z : V := x + x - g x - g (g x) with hz
      have hgy : g y = y := by
        rw [hy, map_add, map_add, hg x]
        abel
      have hzS : z ∈ S := by
        apply hω
        have h1 : g z = g x + g x - g (g x) - x := by
          rw [hz, map_sub, map_sub, map_add, hg x]
        have h2 : g (g z) = g (g x) + g (g x) - x - g x := by
          rw [h1, map_sub, map_sub, map_add, hg x]
        rw [h2, h1, hz]
        abel
      refine ⟨(3 : K)⁻¹ • y, by rw [map_smul, hgy], ?_⟩
      have hxyz : x = (3 : K)⁻¹ • (y + z) := by
        have : y + z = (3 : K) • x := by
          rw [hy, hz]
          module
        rw [this, smul_smul, inv_mul_cancel₀ h3, one_smul]
      rw [Submodule.Quotient.eq]
      have hdiff : (3 : K)⁻¹ • y - x = -((3 : K)⁻¹ • z) := by
        calc (3 : K)⁻¹ • y - x = (3 : K)⁻¹ • y - (3 : K)⁻¹ • (y + z) := by rw [← hxyz]
          _ = -((3 : K)⁻¹ • z) := by module
      rw [hdiff]
      exact S.neg_mem (S.smul_mem _ hzS)
    have hrank : 1 < finrank K (V ⧸ S) := by
      have := Submodule.finrank_quotient_add_finrank S
      omega
    haveI : Nontrivial (V ⧸ S) := (Module.finrank_pos_iff (R := K) (M := V ⧸ S)).1 (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V ⧸ S)
    obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank hrank hx
    obtain ⟨u₁, hu₁, rfl⟩ := hlift x
    obtain ⟨u₂, hu₂, rfl⟩ := hlift y
    refine ⟨u₁, u₂, ⟨0, ?_, ?_⟩, ?_⟩
    · simpa using hu₁
    · simpa using hu₂
    · intro α β hαβ
      have hq : α • (Submodule.Quotient.mk u₁ : V ⧸ S) +
          β • (Submodule.Quotient.mk u₂ : V ⧸ S) = 0 := by
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          ← Submodule.Quotient.mk_add]
        exact (Submodule.Quotient.mk_eq_zero S).2 hαβ
      exact LinearIndependent.pair_iff.1 hxy α β hq

end GoodPlane

section Planes

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_span_pair_le (s t : V) : finrank K (Submodule.span K {s, t}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({s, t} : Finset V)
  have h2 : ({s, t} : Finset V).card ≤ 2 := Finset.card_le_two
  rw [Set.finrank, Finset.coe_pair] at h
  omega

theorem exists_three_planes (g : Module.End K V) (hg3 : g ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    (hroot : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (hdim : 6 ≤ finrank K V) :
    ∃ s t : Fin 3 → V, (∀ j, GoodRel g (s j) (t j)) ∧
      LinearIndependent K (fun x : Fin 3 × Fin 2 => ![s x.1, t x.1] x.2) := by
  obtain ⟨s₀, t₀, h₀, i₀⟩ := exists_goodPlane g hg3 h3 hroot ⊥
    (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])
    (by rw [finrank_bot]; omega)
  have hA : ∀ x ∈ Submodule.span K {s₀, t₀}, g x ∈ Submodule.span K {s₀, t₀} := h₀.maps_span
  obtain ⟨s₁, t₁, h₁, i₁⟩ := exists_goodPlane g hg3 h3 hroot (Submodule.span K {s₀, t₀}) hA
    (by have := finrank_span_pair_le (K := K) s₀ t₀; omega)
  have hB : ∀ x ∈ Submodule.span K {s₁, t₁}, g x ∈ Submodule.span K {s₁, t₁} := h₁.maps_span
  have hAB : ∀ x ∈ Submodule.span K {s₀, t₀} ⊔ Submodule.span K {s₁, t₁},
      g x ∈ Submodule.span K {s₀, t₀} ⊔ Submodule.span K {s₁, t₁} := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hA a ha) (hB b hb)
  obtain ⟨s₂, t₂, h₂, i₂⟩ := exists_goodPlane g hg3 h3 hroot
    (Submodule.span K {s₀, t₀} ⊔ Submodule.span K {s₁, t₁}) hAB
    (by
      have h1 := finrank_span_pair_le (K := K) s₀ t₀
      have h2 := finrank_span_pair_le (K := K) s₁ t₁
      have h12 := Submodule.finrank_add_le_finrank_add_finrank
        (Submodule.span K {s₀, t₀}) (Submodule.span K {s₁, t₁})
      omega)
  refine ⟨![s₀, s₁, s₂], ![t₀, t₁, t₂], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact h₀
    · exact h₁
    · exact h₂
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hc
    have mA0 : c (0, 0) • s₀ ∈ Submodule.span K {s₀, t₀} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have mA1 : c (0, 1) • t₀ ∈ Submodule.span K {s₀, t₀} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have mB0 : c (1, 0) • s₁ ∈ Submodule.span K {s₁, t₁} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have mB1 : c (1, 1) • t₁ ∈ Submodule.span K {s₁, t₁} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have h2 : c (2, 0) = 0 ∧ c (2, 1) = 0 := by
      apply i₂
      have : c (2, 0) • s₂ + c (2, 1) • t₂ =
          -((c (0, 0) • s₀ + c (0, 1) • t₀) + (c (1, 0) • s₁ + c (1, 1) • t₁)) := by
        rw [eq_neg_iff_add_eq_zero, ← hc]
        abel
      rw [this]
      exact Submodule.neg_mem _ (Submodule.add_mem_sup (Submodule.add_mem _ mA0 mA1)
        (Submodule.add_mem _ mB0 mB1))
    have h1' : c (1, 0) = 0 ∧ c (1, 1) = 0 := by
      apply i₁
      have : c (1, 0) • s₁ + c (1, 1) • t₁ = -(c (0, 0) • s₀ + c (0, 1) • t₀) := by
        rw [eq_neg_iff_add_eq_zero, ← hc, h2.1, h2.2]
        simp only [zero_smul, add_zero]
        abel
      rw [this]
      exact Submodule.neg_mem _ (Submodule.add_mem _ mA0 mA1)
    have h0 : c (0, 0) = 0 ∧ c (0, 1) = 0 := by
      apply i₀
      rw [Submodule.mem_bot]
      rw [h2.1, h2.2, h1'.1, h1'.2] at hc
      simpa using hc
    rintro ⟨j, e⟩
    fin_cases j <;> fin_cases e
    · exact h0.1
    · exact h0.2
    · exact h1'.1
    · exact h1'.2
    · exact h2.1
    · exact h2.2

theorem exists_invariant_complement (g : Module.End K V) (hg3 : g ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    (U : Submodule K V) (hU : ∀ x ∈ U, g x ∈ U) :
    ∃ W : Submodule K V, (∀ x ∈ W, g x ∈ W) ∧ IsCompl U W := by
  have hsq : Squarefree (Polynomial.X ^ 3 - 1 : Polynomial K) := by
    have h := Polynomial.separable_X_pow_sub_C (F := K) (n := 3) 1 (by exact_mod_cast h3)
      one_ne_zero
    rw [map_one] at h
    exact h.squarefree
  have hev : Polynomial.aeval g (Polynomial.X ^ 3 - 1 : Polynomial K) = 0 := by
    simp [hg3]
  have hss : g.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev
  obtain ⟨W, hW, hUW⟩ := Module.End.isSemisimple_iff.1 hss U hU
  exact ⟨W, hW, hUW⟩

theorem exists_adapted_basis (g : Module.End K V) (hg3 : g ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    (hroot : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (hdim : 6 ≤ finrank K V) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis ((Fin 3 × Fin 2) ⊕ ι) K V),
      (∀ j : Fin 3, GoodRel g (b (Sum.inl (j, 0))) (b (Sum.inl (j, 1)))) ∧
      ∀ k : ι, g (b (Sum.inr k)) ∈ Submodule.span K (Set.range fun k : ι => b (Sum.inr k)) := by
  obtain ⟨s, t, hgood, hli⟩ := exists_three_planes g hg3 h3 hroot hdim
  set six : Fin 3 × Fin 2 → V := fun x => ![s x.1, t x.1] x.2 with hsix
  set U : Submodule K V := Submodule.span K (Set.range six) with hU
  have hsU : ∀ j, s j ∈ U := fun j => Submodule.subset_span ⟨(j, 0), by simp [hsix]⟩
  have htU : ∀ j, t j ∈ U := fun j => Submodule.subset_span ⟨(j, 1), by simp [hsix]⟩
  have hspan_le : ∀ j, Submodule.span K {s j, t j} ≤ U := by
    intro j
    refine Submodule.span_le.2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hsU j
    · exact htU j
  have hUinv : ∀ x ∈ U, g x ∈ U := by
    have : U.map g ≤ U := by
      rw [hU, Submodule.map_span_le]
      rintro _ ⟨⟨j, e⟩, rfl⟩
      obtain ⟨c, hs, ht⟩ := hgood j
      fin_cases e
      · show g (s j) ∈ U
        rw [hs]
        exact hspan_le j (tri_mem_span _ _ _)
      · show g (t j) ∈ U
        rw [ht]
        exact hspan_le j (tri_mem_span _ _ _)
    exact fun x hx => this ⟨x, hx, rfl⟩
  obtain ⟨W, hWinv, hUW⟩ := exists_invariant_complement g hg3 h3 U hUinv
  let cW : Basis (Fin (finrank K W)) K W := Module.finBasis K W
  have hWspan : Submodule.span K (Set.range (W.subtype ∘ cW)) = W := by
    rw [Set.range_comp, Submodule.span_image, cW.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hcWli : LinearIndependent K (W.subtype ∘ cW) :=
    cW.linearIndependent.map' W.subtype W.ker_subtype
  have hdisj : Disjoint (Submodule.span K (Set.range six))
      (Submodule.span K (Set.range (W.subtype ∘ cW))) := by
    rw [hWspan]
    exact hUW.disjoint
  have hFli : LinearIndependent K (Sum.elim six (W.subtype ∘ cW)) :=
    LinearIndependent.sum_type hli hcWli hdisj
  have hFspan : ⊤ ≤ Submodule.span K (Set.range (Sum.elim six (W.subtype ∘ cW))) := by
    rw [Set.Sum.elim_range, Submodule.span_union, hWspan]
    exact hUW.sup_eq_top.ge
  let b : Basis ((Fin 3 × Fin 2) ⊕ Fin (finrank K W)) K V := Basis.mk hFli hFspan
  have hb_inl : ∀ x, b (Sum.inl x) = six x := fun x => by
    rw [Basis.mk_apply, Sum.elim_inl]
  have hb_inr : ∀ k, b (Sum.inr k) = (cW k : V) := fun k => by
    rw [Basis.mk_apply, Sum.elim_inr]
    rfl
  refine ⟨Fin (finrank K W), inferInstance, b, ?_, ?_⟩
  · intro j
    rw [hb_inl, hb_inl]
    simpa [hsix] using hgood j
  · intro k
    have hrange : (Set.range fun k : Fin (finrank K W) => b (Sum.inr k)) =
        Set.range (W.subtype ∘ cW) := by
      congr 1
      funext k
      rw [hb_inr]
      rfl
    rw [hrange, hWspan, hb_inr]
    exact hWinv _ (cW k).2

end Planes

end LinThree

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
