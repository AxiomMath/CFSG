module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality

variable {τ : Tag}

theorem mem_charStabilizer_prod {M M' : Type*} [CommGroup M] [CommGroup M']
    {φ : Multiplicative (Fin τ.rank → ℤ) →* M} {ψ : Multiplicative (Fin τ.rank → ℤ) →* M'}
    {w : WeylGroup τ} :
    w ∈ charStabilizer (φ.prod ψ) ↔ w ∈ charStabilizer φ ∧ w ∈ charStabilizer ψ := by
  simp only [mem_charStabilizer, MonoidHom.prod_apply, Prod.mk.injEq, forall_and]

theorem exists_triChar_pair {L : Type} [Field L] (a : Fin 2 → Fin τ.rank → Lˣ)
    (h3 : ∀ s i, a s i ^ 3 = 1) :
    ∃ φ : Fin 2 → Multiplicative (Fin τ.rank → ℤ) →* Z3,
      (∀ s w, w ∈ rootCharStabilizer (a s) ↔ w ∈ charStabilizer (φ s)) ∧
        familyKernel a = kernelRoots ((φ 0).prod (φ 1)) ∧
          kernelWeylGroup (familyChar a) = kernelWeylGroup ((φ 0).prod (φ 1)) := by
  choose φ hφ using fun s =>
    exists_triChar_ker_eq (rootCharHom3 (a s)) (rootCharHom3_pow_three (a s) (h3 s))
  have hker : ∀ x, familyChar a x = 1 ↔ ((φ 0).prod (φ 1)) x = 1 := fun x => by
    rw [MonoidHom.prod_apply, Prod.mk_eq_one, ← hφ 0, ← hφ 1]
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext s
      fin_cases s
      · exact h0
      · exact h1
  refine ⟨φ, fun s w => ?_, ?_, kernelWeylGroup_congr_ker hker⟩
  · rw [← charStabilizer_congr_ker (hφ s)]
    exact Iff.rfl
  · rw [← kernelRoots_familyChar, kernelRoots_congr_ker hker]

@[expose] def CyclicTriple (τ : Tag) (S : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ) : Prop :=
  ∃ γ : Fin 3 → Fin τ.rank → ℤ, (∀ j, IsRoot τ (γ j)) ∧
    (∀ j j', j ≠ j' → iform (γ j) (γ j') = 0) ∧ (∀ α, α ∈ S ↔ ∃ j, α = γ j ∨ α = -γ j) ∧
    ∀ j, w • γ j = γ (j + 1) ∨ w • γ j = -γ (j + 1)

section Certs

theorem closure_rootReflection_eq_map {S S' : Set (Fin τ.rank → ℤ)} {t : WeylGroup τ}
    (hS' : ∀ α ∈ S', IsRoot τ α) (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S') :
    Subgroup.closure (rootReflection '' S) =
      (Subgroup.closure (rootReflection '' S')).map (MulAut.conj t).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext r
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hβ := (hS α).1 hα
    refine ⟨rootReflection (t⁻¹ • α), ⟨_, hβ, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← rootReflection_smul_root t (hS' _ hβ), smul_inv_smul]
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    refine ⟨t • β, (hS _).2 (by rwa [inv_smul_smul]), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact rootReflection_smul_root t (hS' β hβ)

@[expose] def KernelBlocks.conj {S S' : Set (Fin τ.rank → ℤ)} (B : KernelBlocks τ S')
    (t : WeylGroup τ) (hS' : ∀ α ∈ S', IsRoot τ α) (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S') :
    KernelBlocks τ S where
  blk j := (fun α => t • α) '' B.blk j
  nonempty j := (B.nonempty j).image _
  sub j := by
    rintro _ ⟨α, hα, rfl⟩
    refine (hS (t • α)).2 ?_
    rw [inv_smul_smul]
    exact B.sub j hα
  cover α hα := by
    obtain ⟨j, hj⟩ := B.cover _ ((hS α).1 hα)
    exact ⟨j, t⁻¹ • α, hj, smul_inv_smul t α⟩
  neg j := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨-α, B.neg j α hα, smul_neg t α⟩
  disj j j' h := (Set.disjoint_image_iff (MulAction.injective t)).2 (B.disj j j' h)
  orth j j' h := by
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    exact (iform_smul t γ δ).trans (B.orth j j' h γ hγ δ hδ)
  trans j := by
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    obtain ⟨x, hx, hxγ⟩ := B.trans j γ hγ δ hδ
    refine ⟨t * x * t⁻¹, ?_, ?_⟩
    · rw [closure_rootReflection_eq_map hS' hS]
      exact Subgroup.mem_map.2 ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · show (t * x * t⁻¹) • t • γ = t • δ
      rw [mul_smul, mul_smul, inv_smul_smul, hxγ]
  perm x hx j := by
    have hSimg : S = (fun α => t • α) '' S' := by
      ext α
      rw [hS]
      constructor
      · intro h
        exact ⟨t⁻¹ • α, h, smul_inv_smul t α⟩
      · rintro ⟨β, hβ, rfl⟩
        rwa [inv_smul_smul]
    have hx' : (fun α => (t⁻¹ * x * t) • α) '' S' = S' := by
      have e : (fun α => (t⁻¹ * x * t) • α) '' S' =
          (fun α => t⁻¹ • α) '' ((fun α => x • α) '' ((fun α => t • α) '' S')) := by
        simp only [Set.image_image, mul_smul]
      rw [e, ← hSimg, hx, hSimg]
      simp only [Set.image_image, inv_smul_smul, Set.image_id']
    obtain ⟨j', hj'⟩ := B.perm _ hx' j
    refine ⟨j', ?_⟩
    show (fun α => x • α) '' ((fun α => t • α) '' B.blk j) = (fun α => t • α) '' B.blk j'
    rw [← hj']
    simp only [Set.image_image, mul_smul, smul_inv_smul]

theorem KernelBlocks.conj_blk {S S' : Set (Fin τ.rank → ℤ)} (B : KernelBlocks τ S')
    (t : WeylGroup τ) (hS' : ∀ α ∈ S', IsRoot τ α) (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S') (j : Fin 3) :
    (B.conj t hS' hS).blk j = (fun α => t • α) '' B.blk j :=
  rfl

theorem KernelBlocks.conj_cyclic {S S' : Set (Fin τ.rank → ℤ)} (B : KernelBlocks τ S')
    {t w' : WeylGroup τ} (hS' : ∀ α ∈ S', IsRoot τ α) (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S')
    (h : ∀ j : Fin 3, (fun α => w' • α) '' B.blk j = B.blk (j + 1)) (j : Fin 3) :
    (fun α => (t * w' * t⁻¹) • α) '' (B.conj t hS' hS).blk j =
      (B.conj t hS' hS).blk (j + 1) := by
  rw [KernelBlocks.conj_blk, KernelBlocks.conj_blk, ← h j]
  simp only [Set.image_image, mul_smul, inv_smul_smul]

theorem exists_kernelBlocks_conj {S S' : Set (Fin τ.rank → ℤ)} {t w' : WeylGroup τ}
    (hS' : ∀ α ∈ S', IsRoot τ α) (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S')
    (h : ∃ B : KernelBlocks τ S', ∀ j : Fin 3, (fun α => w' • α) '' B.blk j = B.blk (j + 1)) :
    ∃ B : KernelBlocks τ S, ∀ j : Fin 3,
      (fun α => (t * w' * t⁻¹) • α) '' B.blk j = B.blk (j + 1) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B.conj t hS' hS, B.conj_cyclic hS' hS hB⟩

private theorem iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  have h := iform_smul_left (-1) x y
  rwa [neg_one_smul, neg_one_mul] at h

private theorem iform_neg_right (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [iform_comm, iform_neg_left, iform_comm]

theorem CyclicTriple.conj {S S' : Set (Fin τ.rank → ℤ)} {w' t : WeylGroup τ}
    (h : CyclicTriple τ S' w') (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S') :
    CyclicTriple τ S (t * w' * t⁻¹) := by
  obtain ⟨γ, hroot, horth, hS', hw⟩ := h
  refine ⟨fun j => t • γ j, fun j => IsRoot.smul (hroot j) t, fun j j' hjj' => ?_, fun α => ?_,
    fun j => ?_⟩
  · rw [iform_smul]
    exact horth j j' hjj'
  · rw [hS, hS']
    refine exists_congr fun j => or_congr ?_ ?_
    · exact inv_smul_eq_iff
    · rw [inv_smul_eq_iff, smul_neg]
  · simp only [mul_smul, inv_smul_smul]
    rcases hw j with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (smul_neg t _)

theorem exists_kernelBlocks_of_cyclicTriple {S : Set (Fin τ.rank → ℤ)} {w : WeylGroup τ}
    (h : CyclicTriple τ S w) :
    ∃ B : KernelBlocks τ S, ∀ j : Fin 3, (fun α => w • α) '' B.blk j = B.blk (j + 1) := by
  obtain ⟨γ, hroot, horth, hS, hw⟩ := h
  have hpos : ∀ j, 0 < iform (γ j) (γ j) := fun j => iform_self_pos (hroot j).ne_zero
  have hne : ∀ j j', j ≠ j' → γ j ≠ γ j' ∧ γ j ≠ -γ j' := by
    intro j j' hjj'
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := horth j j' hjj'
      rw [e] at this
      exact (hpos j').ne' this
    · have := horth j j' hjj'
      rw [e, iform_neg_left] at this
      have := hpos j'
      omega
  have hmem : ∀ j, γ j ∈ S ∧ -γ j ∈ S := fun j =>
    ⟨(hS _).2 ⟨j, Or.inl rfl⟩, (hS _).2 ⟨j, Or.inr rfl⟩⟩
  have himg : ∀ (x : WeylGroup τ) j, (fun α => x • α) '' ({γ j, -γ j} : Set _) =
      {x • γ j, -(x • γ j)} := by
    intro x j
    simp only [Set.image_insert_eq, Set.image_singleton, smul_neg]
  refine ⟨{ blk := fun j => {γ j, -γ j}
            nonempty := fun j => ⟨γ j, Set.mem_insert _ _⟩
            sub := fun j α hα => ?_
            cover := fun α hα => ?_
            neg := fun j α hα => ?_
            disj := fun j j' hjj' => ?_
            orth := fun j j' hjj' α hα δ hδ => ?_
            trans := fun j α hα δ hδ => ?_
            perm := fun x hx j => ?_ }, fun j => ?_⟩
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl
    · exact (hmem j).1
    · exact (hmem j).2
  · obtain ⟨j, hj⟩ := (hS α).1 hα
    refine ⟨j, ?_⟩
    rcases hj with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
    rcases hα with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · refine Set.disjoint_left.2 fun α hα hα' => ?_
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hα'
    obtain ⟨h1, h2⟩ := hne j j' hjj'
    obtain ⟨h3, h4⟩ := hne j' j (Ne.symm hjj')
    rcases hα with rfl | rfl <;> rcases hα' with h | h
    · exact h1 h
    · exact h2 h
    · exact h4 h.symm
    · exact h1 (neg_injective h)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hδ
    have h0 := horth j j' hjj'
    rcases hα with rfl | rfl <;> rcases hδ with rfl | rfl <;>
      simp only [iform_neg_left, iform_neg_right, h0, neg_zero]
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hδ
    have hr : rootReflection (γ j) ∈ Subgroup.closure (rootReflection '' S) :=
      Subgroup.subset_closure ⟨γ j, (hmem j).1, rfl⟩
    rcases hα with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact ⟨1, one_mem _, one_smul _ _⟩
    · exact ⟨_, hr, rootReflection_smul_self (hroot j)⟩
    · exact ⟨_, hr, by rw [smul_neg, rootReflection_smul_self (hroot j), neg_neg]⟩
    · exact ⟨1, one_mem _, one_smul _ _⟩
  · have hxγ : x • γ j ∈ S := by
      rw [← hx]
      exact ⟨γ j, (hmem j).1, rfl⟩
    obtain ⟨j', hj'⟩ := (hS _).1 hxγ
    refine ⟨j', ?_⟩
    rw [himg]
    rcases hj' with h | h <;> rw [h]
    rw [neg_neg, Set.pair_comm]
  · show (fun α => w • α) '' ({γ j, -γ j} : Set _) = {γ (j + 1), -γ (j + 1)}
    rw [himg]
    rcases hw j with h | h <;> rw [h]
    rw [neg_neg, Set.pair_comm]

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
