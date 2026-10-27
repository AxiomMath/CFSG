module

public import CFSG.LieType.Chevalley.C2E6MinusSixVertices

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fix_append {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut) {F N : List (Fin 27 ⊕ Fin 45)}
    (hF : ∀ f ∈ F, σ (vertexOf f) = vertexOf f)
    (hN : ∀ a ∈ N, ∀ b, CType b = CType a → (∀ f ∈ F, CInc b f ↔ CInc a f) →
      (∀ f ∈ F, CNear b f ↔ CNear a f) → b = a) :
    ∀ f ∈ F ++ N, σ (vertexOf f) = vertexOf f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact hF f hf
  · exact fix_vertexOf_of_unique hσ hF (hN f hf)

@[expose] def rigidBase : List (Fin 27 ⊕ Fin 45) :=
  [.inl 0, .inl 2, .inr 0, .inr 1, .inr 3, .inr 4]

@[expose] def rigidRound₁ : List (Fin 27 ⊕ Fin 45) :=
  [.inl 1, .inl 3, .inl 4, .inl 11, .inl 12, .inl 17, .inl 18, .inl 23, .inr 2, .inr 6,
    .inr 10, .inr 11, .inr 16, .inr 27, .inr 28]

@[expose] def rigidRound₂ : List (Fin 27 ⊕ Fin 45) :=
  [.inl 5, .inl 6, .inl 7, .inl 8, .inl 9, .inl 10, .inl 13, .inl 14, .inl 15, .inl 16,
    .inl 19, .inl 20, .inl 21, .inl 22, .inl 24, .inl 25, .inl 26, .inr 5, .inr 7, .inr 8,
    .inr 9, .inr 12, .inr 17, .inr 18, .inr 19, .inr 20, .inr 21, .inr 22, .inr 23,
    .inr 24, .inr 25, .inr 26, .inr 29, .inr 30, .inr 31, .inr 32, .inr 33, .inr 34,
    .inr 35, .inr 36, .inr 37, .inr 38, .inr 39, .inr 40, .inr 41, .inr 42, .inr 43,
    .inr 44]

@[expose] def rigidRound₃ : List (Fin 27 ⊕ Fin 45) :=
  [.inr 13, .inr 14, .inr 15]

theorem rigid_round₁ : ∀ a ∈ rigidRound₁, ∀ b, CType b = CType a →
    (∀ f ∈ rigidBase, CInc b f ↔ CInc a f) → (∀ f ∈ rigidBase, CNear b f ↔ CNear a f) →
      b = a := by
  decide +kernel

theorem rigid_round₂ : ∀ a ∈ rigidRound₂, ∀ b, CType b = CType a →
    (∀ f ∈ rigidBase ++ rigidRound₁, CInc b f ↔ CInc a f) →
    (∀ f ∈ rigidBase ++ rigidRound₁, CNear b f ↔ CNear a f) → b = a := by
  decide +kernel

theorem rigid_round₃ : ∀ a ∈ rigidRound₃, ∀ b, CType b = CType a →
    (∀ f ∈ rigidBase ++ rigidRound₁ ++ rigidRound₂, CInc b f ↔ CInc a f) →
    (∀ f ∈ rigidBase ++ rigidRound₁ ++ rigidRound₂, CNear b f ↔ CNear a f) → b = a := by
  decide +kernel

theorem mem_rigid_all :
    ∀ a, a ∈ rigidBase ++ rigidRound₁ ++ rigidRound₂ ++ rigidRound₃ := by
  decide +kernel

theorem eq_one_of_fix_base {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut)
    (h : ∀ f ∈ rigidBase, σ (vertexOf f) = vertexOf f) : σ = 1 := by
  have h3 := fix_append hσ (fix_append hσ (fix_append hσ h rigid_round₁) rigid_round₂)
    rigid_round₃
  exact eq_one_of_forall_fix fun a => h3 a (mem_rigid_all a)

@[expose] def flagBase : List (Fin 27 ⊕ Fin 45) :=
  [.inl 0, .inl 2, .inr 0, .inr 1]

theorem flag_round : ∀ a ∈ ([.inr 2] : List (Fin 27 ⊕ Fin 45)), ∀ b, CType b = CType a →
    (∀ f ∈ flagBase, CInc b f ↔ CInc a f) → (∀ f ∈ flagBase, CNear b f ↔ CNear a f) →
      b = a := by
  decide +kernel

theorem fix_lnVertex_two {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut)
    (h : ∀ f ∈ flagBase, σ (vertexOf f) = vertexOf f) : σ (lnVertex 2) = lnVertex 2 :=
  fix_append hσ h flag_round (.inr 2) (by decide)

theorem ptOn_zero_iff : ∀ j : Fin 45, PtOn 0 j ↔ j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  decide +kernel

end CFSG.LieType.Chevalley.C2E6Overlap
