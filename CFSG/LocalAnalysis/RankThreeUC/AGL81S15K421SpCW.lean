module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpCWProof

@[expose] def RankTwoAt (p : ℕ) {X : Type} [Group X] (x : X) : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B) (_ : Finite A) (_ : Finite B) (φ : A × B →* X),
    Function.Injective φ ∧ φ.range ≤ Subgroup.centralizer ({x} : Set X) ∧
      p ∣ Nat.card A ∧ p ∣ Nat.card B

@[expose] def SimpleAt (p : ℕ) {X : Type} [Group X] (x : X) : Prop :=
  ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsSimpleGroup A) (ψ : A →* X),
    Function.Injective ψ ∧ ψ.range ≤ Subgroup.centralizer ({x} : Set X) ∧
      p ∣ Nat.card A ∧ Nat.card A ≠ p

@[expose] def RankOneAt (p : ℕ) {X : Type} [Group X] (x : X) : Prop :=
  ∃ (A : Type) (_ : Group A) (_ : Finite A) (ψ : A →* X),
    Function.Injective ψ ∧ ψ.range ≤ Subgroup.centralizer ({x} : Set X) ∧ p ∣ Nat.card A

theorem map_symm_le_centralizer {S X : Type} [Group S] [Group X] (ε : S ≃* X) (x : S)
    {H : Subgroup X} (hH : H ≤ Subgroup.centralizer ({ε x} : Set X)) :
    H.map ε.symm.toMonoidHom ≤ Subgroup.centralizer ({x} : Set S) := by
  rintro _ ⟨z, hz, rfl⟩
  have h1 := K421TransProof.centralizer_map_singleton ε.symm (ε x)
  rw [ε.symm_apply_apply] at h1
  rw [← h1]
  exact ⟨z, hH hz, rfl⟩

theorem RankTwoAt.conj {X : Type} [Group X] {p : ℕ} {x y n : X} (hn : n * x * n⁻¹ = y)
    (h : RankTwoAt p y) : RankTwoAt p x := by
  obtain ⟨A, B, _, _, _, _, φ, hφ, hle, hA, hB⟩ := h
  obtain ⟨ψ, hψ, hψle⟩ := K421TransProof.emb_conj φ hφ hn hle
  exact ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance, ψ, hψ, hψle, hA, hB⟩

theorem SimpleAt.conj {X : Type} [Group X] {p : ℕ} {x y n : X} (hn : n * x * n⁻¹ = y)
    (h : SimpleAt p y) : SimpleAt p x := by
  obtain ⟨A, _, _, _, ψ, hψ, hle, hA, hne⟩ := h
  obtain ⟨ψ', hψ', hψle⟩ := K421TransProof.emb_conj ψ hψ hn hle
  exact ⟨A, inferInstance, inferInstance, inferInstance, ψ', hψ', hψle, hA, hne⟩

theorem RankOneAt.conj {X : Type} [Group X] {p : ℕ} {x y n : X} (hn : n * x * n⁻¹ = y)
    (h : RankOneAt p y) : RankOneAt p x := by
  obtain ⟨A, _, _, ψ, hψ, hle, hA⟩ := h
  obtain ⟨ψ', hψ', hψle⟩ := K421TransProof.emb_conj ψ hψ hn hle
  exact ⟨A, inferInstance, inferInstance, ψ', hψ', hψle, hA⟩

theorem RankTwoAt.of_equiv {S X : Type} [Group S] [Group X] (ε : S ≃* X) {p : ℕ} {x : S}
    (h : RankTwoAt p (ε x)) : RankTwoAt p x := by
  obtain ⟨A, B, _, _, _, _, φ, hφ, hle, hA, hB⟩ := h
  refine ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    ε.symm.toMonoidHom.comp φ, ε.symm.injective.comp hφ, ?_, hA, hB⟩
  rintro _ ⟨a, rfl⟩
  exact map_symm_le_centralizer ε x hle ⟨φ a, ⟨a, rfl⟩, rfl⟩

theorem SimpleAt.of_equiv {S X : Type} [Group S] [Group X] (ε : S ≃* X) {p : ℕ} {x : S}
    (h : SimpleAt p (ε x)) : SimpleAt p x := by
  obtain ⟨A, _, _, _, ψ, hψ, hle, hA, hne⟩ := h
  refine ⟨A, inferInstance, inferInstance, inferInstance, ε.symm.toMonoidHom.comp ψ,
    ε.symm.injective.comp hψ, ?_, hA, hne⟩
  rintro _ ⟨a, rfl⟩
  exact map_symm_le_centralizer ε x hle ⟨ψ a, ⟨a, rfl⟩, rfl⟩

theorem RankOneAt.of_equiv {S X : Type} [Group S] [Group X] (ε : S ≃* X) {p : ℕ} {x : S}
    (h : RankOneAt p (ε x)) : RankOneAt p x := by
  obtain ⟨A, _, _, ψ, hψ, hle, hA⟩ := h
  refine ⟨A, inferInstance, inferInstance, ε.symm.toMonoidHom.comp ψ,
    ε.symm.injective.comp hψ, ?_, hA⟩
  rintro _ ⟨a, rfl⟩
  exact map_symm_le_centralizer ε x hle ⟨ψ a, ⟨a, rfl⟩, rfl⟩

theorem SimpleAt.not_isPSolvable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {x : X}
    (h : SimpleAt p x) : ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨A, _, _, _, ψ, hψ, hle, hA, hne⟩ := h
  exact K421GrpProof.not_isPSolvable_of_embedding inferInstance hA hne ψ hψ hle

theorem RankOneAt.one_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {x : X}
    (h : RankOneAt p x) : 1 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨A, _, _, ψ, hψ, hle, hA⟩ := h
  exact K421GrpProof.rank_ge_one_of_embedding hA ψ hψ hle

end K421SpCWProof

end CFSG.LocalAnalysis.RankThreeUC.S15
