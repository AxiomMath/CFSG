module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7FrameE6
public import CFSG.LieType.Chevalley.RationalToralSignDiagramE7

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint Matrix

section Certificate

variable {τ : Tag}

@[expose] def decompCheck (C : RootCertificate τ) (splus delta : List ℕ)
    (w : List (ℕ × ℕ × ℕ)) : Bool :=
  (splus.all fun k => delta.contains k || w.any fun t => t.1 == k) &&
    w.all fun t => splus.contains t.2.1 && splus.contains t.2.2 &&
      List.ofFn (C.root t.1) == List.ofFn (C.root t.2.1 + C.root t.2.2)

theorem mem_simpleUnion_iff_of_decompCheck
    {C : RootCertificate τ} (hC : C.check = true) {m : ℕ} {splus delta : List ℕ}
    {w : List (ℕ × ℕ × ℕ)} (hsp : splusCheck C m splus = true)
    (hd : deltaCheck C splus delta = true) (hw : decompCheck C splus delta w = true)
    {β : Fin τ.rank → ℤ} : β ∈ simpleUnion (signMaskChar τ m) ↔ ∃ d ∈ delta, C.root d = β := by
  constructor
  · intro hβ
    rw [simpleUnion_eq, Finset.mem_coe, mem_simpleRoots] at hβ
    obtain ⟨-, hpos, hns⟩ := hβ
    obtain ⟨k, hk, rfl⟩ := (mem_posRoots_iff hC hsp).1 hpos
    simp only [decompCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rcases hw1 k hk with hkd | ⟨t, ht, rfl⟩
    · exact ⟨k, hkd, rfl⟩
    · exfalso
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw2 t ht
      exact hns _ ((mem_posRoots_iff hC hsp).2 ⟨_, h1, rfl⟩) _
        ((mem_posRoots_iff hC hsp).2 ⟨_, h2, rfl⟩) (List.ofFn_injective h3)
  · rintro ⟨d, hd', rfl⟩
    exact root_mem_simpleUnion hC hsp hd hd'

end Certificate

section Classes

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem mk_eq_of_parent
    {r : ℕ} (v : Fin r → Fin τ.rank → ℤ) (hv : ∀ k, v k ∈ kernelRoots χ) (par : Fin r → Fin r)
    (hpar : ∀ k, par k = k ∨ iform (v k) (v (par k)) ≠ 0) (n : ℕ) (k : Fin r) :
    (⟦⟨v k, hv k⟩⟧ : KernelComponent χ) = ⟦⟨v (par^[n] k), hv _⟩⟧ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih (par k)]
    rcases hpar k with h | h
    · simp only [h]
    · exact mk_eq_of_iform_ne_zero (α := ⟨v k, hv k⟩) (β := ⟨v (par k), hv _⟩) h

theorem mk_ne_of_invariant
    (P : (Fin τ.rank → ℤ) → Prop)
    (hP : ∀ α β : kernelRoots χ, iform (α : Fin τ.rank → ℤ) β ≠ 0 → P α → P β)
    {α β : kernelRoots χ} (hα : P α) (hβ : ¬ P β) : (⟦α⟧ : KernelComponent χ) ≠ ⟦β⟧ := by
  intro h
  have hr : Relation.EqvGen (fun a b : kernelRoots χ =>
      (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0) α β :=
    Quotient.exact h
  have key : ∀ a b : kernelRoots χ, Relation.EqvGen (fun a b : kernelRoots χ =>
      (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0) a b →
        (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      rw [dotProduct_mulVec_eq_iform] at hxy
      refine ⟨hP x y hxy, hP y x ?_⟩
      rwa [iform_comm]
    | refl => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact hβ ((key α β hr).1 hα)

end Classes

@[expose] def e7Decomp0 : List (ℕ × ℕ × ℕ) :=
  [(8, 0, 2), (10, 1, 3), (12, 2, 3), (14, 3, 4), (16, 4, 5), (18, 5, 6), (21, 0, 12), (23, 1, 12),
    (24, 1, 14), (26, 2, 14), (28, 3, 16), (30, 4, 18), (33, 0, 23), (34, 0, 26), (37, 1, 26),
    (38, 1, 28), (40, 2, 28), (42, 3, 30), (46, 0, 37), (47, 0, 40), (50, 3, 37), (51, 1, 40),
    (52, 1, 42), (54, 2, 42), (58, 0, 50), (59, 0, 51), (60, 0, 54), (64, 3, 51), (65, 1, 54),
    (70, 2, 58), (71, 0, 64), (72, 0, 65), (75, 4, 64), (76, 3, 65), (80, 2, 71), (81, 0, 75),
    (82, 0, 76), (85, 4, 76), (89, 2, 81), (90, 2, 82), (91, 0, 85), (93, 5, 85), (97, 3, 89),
    (98, 2, 91), (99, 0, 93), (104, 1, 97), (105, 3, 98), (106, 2, 99), (110, 1, 105),
    (111, 3, 106), (114, 1, 111), (115, 4, 111), (118, 1, 115), (120, 3, 118), (122, 2, 120),
    (124, 0, 122)]

@[expose] def e7Decomp1 : List (ℕ × ℕ × ℕ) :=
  [(10, 1, 3), (12, 2, 3), (14, 3, 4), (16, 4, 5), (18, 5, 6), (23, 1, 12), (24, 1, 14),
    (26, 2, 14), (28, 3, 16), (30, 4, 18), (37, 1, 26), (38, 1, 28), (40, 2, 28), (42, 3, 30),
    (50, 3, 37), (51, 1, 40), (52, 1, 42), (54, 2, 42), (64, 3, 51), (65, 1, 54), (75, 4, 64),
    (76, 3, 65), (85, 4, 76), (93, 5, 85)]

@[expose] def e7Decomp2 : List (ℕ × ℕ × ℕ) :=
  [(8, 0, 2), (12, 2, 3), (14, 3, 4), (16, 4, 5), (18, 5, 6), (21, 0, 12), (26, 2, 14), (28, 3, 16),
    (30, 4, 18), (34, 0, 26), (40, 2, 28), (42, 3, 30), (47, 0, 40), (54, 2, 42), (60, 0, 54),
    (110, 6, 104), (114, 5, 110), (118, 4, 114), (120, 3, 118), (122, 2, 120), (124, 0, 122)]

@[expose] def e7Decomp3 : List (ℕ × ℕ × ℕ) :=
  [(12, 2, 3), (14, 3, 4), (16, 4, 5), (18, 5, 6), (26, 2, 14), (28, 3, 16), (30, 4, 18),
    (40, 2, 28), (42, 3, 30), (46, 4, 33), (54, 2, 42), (58, 3, 46), (59, 5, 46), (70, 2, 58),
    (71, 3, 59), (72, 6, 59), (80, 2, 71), (81, 4, 71), (82, 3, 72), (89, 2, 81), (90, 2, 82),
    (91, 4, 82), (97, 3, 89), (98, 2, 91), (99, 5, 91), (105, 3, 98), (106, 2, 99), (111, 3, 106),
    (115, 4, 111), (124, 33, 115)]


theorem e7_decomp0 : decompCheck e7Certificate e7Splus0 e7Delta0 e7Decomp0 = true := by
  decide +kernel

theorem e7_decomp1 : decompCheck e7Certificate e7Splus1 e7Delta1 e7Decomp1 = true := by
  decide +kernel

theorem e7_decomp2 : decompCheck e7Certificate e7Splus2 e7Delta2 e7Decomp2 = true := by
  decide +kernel

theorem e7_decomp3 : decompCheck e7Certificate e7Splus3 e7Delta3 e7Decomp3 = true := by
  decide +kernel

theorem simpleUnion_e7_zero :
    simpleUnion (signMaskChar .E7 0) = Set.range e7SimpleRoot := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus0 e7_delta0 e7_decomp0]
  have h1 : ∀ d ∈ e7Delta0, ∃ k, e7SimpleRoot k = e7Certificate.root d := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e7Delta0, e7Certificate.root d = e7SimpleRoot k := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨k, rfl⟩
    exact h2 k

theorem simpleUnion_e7_one :
    simpleUnion (signMaskChar .E7 1) = Set.range e7D6Root ∪ {e7Theta} := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus1 e7_delta1 e7_decomp1]
  have h1 : ∀ d ∈ e7Delta1, (∃ k, e7D6Root k = e7Certificate.root d) ∨
      e7Certificate.root d = e7Theta := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e7Delta1, e7Certificate.root d = e7D6Root k := by decide +kernel
  have h3 : ∃ d ∈ e7Delta1, e7Certificate.root d = e7Theta := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases h1 d hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨k, rfl⟩ | h)
    · exact h2 k
    · rw [Set.mem_singleton_iff] at h
      exact h ▸ h3

theorem simpleUnion_e7_two :
    simpleUnion (signMaskChar .E7 2) = Set.range e7A7Root := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus2 e7_delta2 e7_decomp2]
  have h1 : ∀ d ∈ e7Delta2, ∃ k, e7A7Root k = e7Certificate.root d := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e7Delta2, e7Certificate.root d = e7A7Root k := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨k, rfl⟩
    exact h2 k

theorem simpleUnion_e7_three :
    simpleUnion (signMaskChar .E7 3) = Set.range e7E6Root := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus3 e7_delta3 e7_decomp3]
  have h1 : ∀ d ∈ e7Delta3, ∃ k, e7E6Root k = e7Certificate.root d := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e7Delta3, e7Certificate.root d = e7E6Root k := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨k, rfl⟩
    exact h2 k

end CFSG.ComponentClassification.CatLeafProof
