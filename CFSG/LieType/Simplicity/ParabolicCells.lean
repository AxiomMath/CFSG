module

public import CFSG.LieType.Chevalley.FixedCollection
public import CFSG.LieType.Chevalley.FixedNative

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem nrep_simple_eq
    (i : Fin τ.rank) : nrep τ K (simple τ i) = weylElement τ K i := by
  have h : (coxeterSystem τ).IsReduced [i] := by
    rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_singleton, CoxeterSystem.length_simple,
      List.length_singleton]
  have e := nrep_eq_prod τ K h
  rwa [CoxeterSystem.wordProd_singleton, List.map_singleton, List.prod_singleton] at e

variable [Finite K]

theorem exists_weylElement_mul_mul_nrep_eq
    {w : WeylGroup τ} {i : Fin τ.rank}
    (hlen : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1)
    {b : adjointGroup τ K} (hb : b ∈ (nativeData τ K).B) :
    ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
      weylElement τ K i * b * nrep τ K w = b₁ * nrep τ K (simple τ i * w) * b₂ := by
  have hm : (rootCombinatorics τ).pos
      ((weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩)⁻¹ • simpleRoot τ i) := by
    rw [weylHom_nrep]
    exact (length_simple_mul_eq_add_one_iff w i).1 hlen
  obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := RootGroupData.exists_simple_mul_of_pos (D := nativeData τ K) i
    ((nativeRootSubgroups τ K).simple_le_normalizer_Ui i)
    ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ hm hb
  refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
  have hn : nrep τ K (simple τ i * w) = weylElement τ K i * nrep τ K w := by
    rw [nrep_mul K (by rw [hlen, CoxeterSystem.length_simple, add_comm]), nrep_simple_eq]
  rw [hn]
  exact h

theorem exists_nrep_mul_mul_nrep_eq
    {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v')
    {b : adjointGroup τ K} (hb : b ∈ (nativeData τ K).B) :
    ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
      nrep τ K v * b * nrep τ K v' = b₁ * nrep τ K (v * v') * b₂ := by
  suffices key : ∀ l : ℕ, ∀ v : WeylGroup τ, (coxeterSystem τ).length v = l →
      (coxeterSystem τ).length (v * v') =
        (coxeterSystem τ).length v + (coxeterSystem τ).length v' →
      ∀ b ∈ (nativeData τ K).B, ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
        nrep τ K v * b * nrep τ K v' = b₁ * nrep τ K (v * v') * b₂ from
    key _ v rfl hlen b hb
  intro l
  induction l with
  | zero =>
    intro v hv _ b hb
    obtain rfl : v = 1 := (coxeterSystem τ).length_eq_zero_iff.1 hv
    exact ⟨b, hb, 1, one_mem _, by rw [nrep_one, one_mul, one_mul, mul_one]⟩
  | succ l ih =>
    intro v hv hlen b hb
    have hv1 : v ≠ 1 := by
      rintro rfl
      rw [(coxeterSystem τ).length_one] at hv
      omega
    obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_leftDescent_of_ne_one hv1
    obtain ⟨u, rfl⟩ : ∃ u, simple τ i * u = v := ⟨simple τ i * v,
      (coxeterSystem τ).simple_mul_simple_cancel_left i⟩
    have hi' : (coxeterSystem τ).length u + 1 = (coxeterSystem τ).length (simple τ i * u) := by
      have := (coxeterSystem τ).isLeftDescent_iff.1 hi
      rwa [(coxeterSystem τ).simple_mul_simple_cancel_left] at this
    have hvv' : simple τ i * u * v' = simple τ i * (u * v') := mul_assoc _ _ _
    have h1 := (coxeterSystem τ).length_mul_le u v'
    have h2 := (coxeterSystem τ).length_simple_mul (u * v') i
    rw [← hvv'] at h2
    have hlu : (coxeterSystem τ).length (u * v') =
        (coxeterSystem τ).length u + (coxeterSystem τ).length v' := by omega
    have hpos : (coxeterSystem τ).length (simple τ i * (u * v')) =
        (coxeterSystem τ).length (u * v') + 1 := by
      rw [← hvv']
      omega
    have hsu : (coxeterSystem τ).length (simple τ i * u) =
        (coxeterSystem τ).length (simple τ i) + (coxeterSystem τ).length u := by
      rw [(coxeterSystem τ).length_simple]
      omega
    obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := ih u (by omega) hlu b hb
    obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := exists_weylElement_mul_mul_nrep_eq hpos hb₁
    refine ⟨c₁, hc₁, c₂ * b₂, mul_mem hc₂ hb₂, ?_⟩
    rw [hvv', nrep_mul K hsu, nrep_simple_eq]
    calc weylElement τ K i * nrep τ K u * b * nrep τ K v'
        = weylElement τ K i * (nrep τ K u * b * nrep τ K v') := by group
      _ = weylElement τ K i * b₁ * nrep τ K (u * v') * b₂ := by rw [h]; group
      _ = c₁ * nrep τ K (simple τ i * (u * v')) * (c₂ * b₂) := by rw [hc]; group

theorem exists_mem_doubleCoset_of_mem_closure
    (J : Set (Fin τ.rank)) {g : adjointGroup τ K}
    (hg : g ∈ Subgroup.closure (((nativeData τ K).B : Set (adjointGroup τ K)) ∪
      weylElement τ K '' J)) :
    ∃ m : monomialGroup τ K, weylHom τ K m ∈ Subgroup.closure (simple τ '' J) ∧
      ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
        g = b₁ * (m : adjointGroup τ K) * b₂ := by
  have hB : ∀ b ∈ (nativeData τ K).B, ∀ g : adjointGroup τ K,
      (∃ m : monomialGroup τ K, weylHom τ K m ∈ Subgroup.closure (simple τ '' J) ∧
        ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
          g = b₁ * (m : adjointGroup τ K) * b₂) →
      ∃ m : monomialGroup τ K, weylHom τ K m ∈ Subgroup.closure (simple τ '' J) ∧
        ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
          b * g = b₁ * (m : adjointGroup τ K) * b₂ := by
    rintro b hb g ⟨m, hm, b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨m, hm, b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩
  have hn : ∀ j ∈ J, ∀ g : adjointGroup τ K,
      (∃ m : monomialGroup τ K, weylHom τ K m ∈ Subgroup.closure (simple τ '' J) ∧
        ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
          g = b₁ * (m : adjointGroup τ K) * b₂) →
      ∃ m : monomialGroup τ K, weylHom τ K m ∈ Subgroup.closure (simple τ '' J) ∧
        ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
          weylElement τ K j * g = b₁ * (m : adjointGroup τ K) * b₂ := by
    rintro j hj g ⟨m, hm, b₁, hb₁, b₂, hb₂, rfl⟩
    rcases RootGroupData.exists_simple_mul (D := nativeData τ K) j
        ((nativeRootSubgroups τ K).simple_le_normalizer_Ui j) ((nativeRootSubgroups τ K).rankOne j)
        m hb₁ with ⟨c₁, hc₁, c₂, hc₂, hc⟩ | ⟨c₁, hc₁, c₂, hc₂, hc⟩
    · have hc' : weylElement τ K j * b₁ * (m : adjointGroup τ K) =
          c₁ * (weylElement τ K j * (m : adjointGroup τ K)) * c₂ := hc
      refine ⟨⟨weylElement τ K j, weylElement_mem_monomialGroup j⟩ * m, ?_, c₁, hc₁, c₂ * b₂,
        mul_mem hc₂ hb₂, ?_⟩
      · rw [map_mul, weylHom_weylElement]
        exact mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hm
      · change weylElement τ K j * (b₁ * (m : adjointGroup τ K) * b₂) =
          c₁ * (weylElement τ K j * (m : adjointGroup τ K)) * (c₂ * b₂)
        rw [← mul_assoc, ← mul_assoc, hc']
        group
    · have hc' : weylElement τ K j * b₁ * (m : adjointGroup τ K) =
          c₁ * (m : adjointGroup τ K) * c₂ := hc
      refine ⟨m, hm, c₁, hc₁, c₂ * b₂, mul_mem hc₂ hb₂, ?_⟩
      rw [← mul_assoc, ← mul_assoc, hc']
      group
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, by rw [map_one]; exact one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨j, hj, rfl⟩
    · exact hB x hx y ih
    · exact hn j hj y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨j, hj, rfl⟩
    · exact hB x⁻¹ (inv_mem hx) y ih
    ·
      have hsq : (weylElement τ K j * weylElement τ K j)⁻¹ ∈ (nativeData τ K).B :=
        inv_mem ((nativeData τ K).H_le_B ((nativeData τ K).sq_mem_H j))
      obtain ⟨m, hm, b₁, hb₁, b₂, hb₂, h⟩ := hn j hj _ (hB _ hsq y ih)
      refine ⟨m, hm, b₁, hb₁, b₂, hb₂, ?_⟩
      rw [← h]
      group

end CFSG.LieType.Simplicity
