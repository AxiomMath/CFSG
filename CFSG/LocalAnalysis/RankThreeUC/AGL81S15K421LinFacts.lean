module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinRep
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGL

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421FactsProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CenProof K421K4Proof K421CGProof
  K421RepProof

@[expose] def gRep (e : ℕ) (t : Fin 3) : GL (Fin e ⊕ Idx) (ZMod 2) :=
  (monoE (Fin e)).av (rep t)

theorem cen_t0 (e : ℕ) (he : e ≤ 1) :
    Nat.card (Subgroup.centralizer ({gRep e 0} : Set (GL (Fin e ⊕ Idx) (ZMod 2)))) =
      glc 2 (e + 4) * glc 4 1 ∧
    ∃ φ : GL (Fin (e + 4)) (ZMod 2) →* GL (Fin e ⊕ Idx) (ZMod 2), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({gRep e 0} : Set (GL (Fin e ⊕ Idx) (ZMod 2))) := by
  let κ : Fin e ⊕ Idx ≃ (Fin e ⊕ (Fin 2 × Fin 2)) ⊕ (Fin 1 × Fin 2) :=
    Equiv.ofBijective (kapFun0 e) (kapFun0_bijective e he)
  have hg : ∀ a b, (gRep e 0 : Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix ((Fin e ⊕ (Fin 2 × Fin 2)) ⊕ (Fin 1 × Fin 2))
        ((Fin e ⊕ (Fin 2 × Fin 2)) ⊕ (Fin 1 × Fin 2)) (ZMod 2)) (κ a) (κ b) := by
    intro a b
    rw [gmat_eq]
    exact congrFun (congrFun (hg_t0 e he) a) b
  have hι : Fintype.card (Fin e ⊕ (Fin 2 × Fin 2)) = e + 4 := by simp
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_of_data κ _ hg, card_GL, card_GL, hι]
    simp [card_K4]
  · obtain ⟨φ, hinj, hle⟩ := exists_embedding_left κ _ hg
    refine ⟨φ.comp (reindexGL (R := ZMod 2) (Fintype.equivFinOfCardEq hι).symm).toMonoidHom,
      hinj.comp (MulEquiv.injective _), ?_⟩
    rintro y ⟨x, rfl⟩
    exact hle ⟨_, rfl⟩

theorem cen_t1 (e : ℕ) (he : e ≤ 1) :
    Nat.card (Subgroup.centralizer ({gRep e 1} : Set (GL (Fin e ⊕ Idx) (ZMod 2)))) =
      glc 2 (e + 2) * glc 4 2 ∧
    ∃ φ : GL (Fin (e + 2)) (ZMod 2) →* GL (Fin e ⊕ Idx) (ZMod 2), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({gRep e 1} : Set (GL (Fin e ⊕ Idx) (ZMod 2))) := by
  let κ : Fin e ⊕ Idx ≃ (Fin e ⊕ (Fin 1 × Fin 2)) ⊕ (Fin 2 × Fin 2) :=
    Equiv.ofBijective (kapFun1 e) (kapFun1_bijective e he)
  have hg : ∀ a b, (gRep e 1 : Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix ((Fin e ⊕ (Fin 1 × Fin 2)) ⊕ (Fin 2 × Fin 2))
        ((Fin e ⊕ (Fin 1 × Fin 2)) ⊕ (Fin 2 × Fin 2)) (ZMod 2)) (κ a) (κ b) := by
    intro a b
    rw [gmat_eq]
    exact congrFun (congrFun (hg_t1 e he) a) b
  have hι : Fintype.card (Fin e ⊕ (Fin 1 × Fin 2)) = e + 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_of_data κ _ hg, card_GL, card_GL, hι]
    simp [card_K4]
  · obtain ⟨φ, hinj, hle⟩ := exists_embedding_left κ _ hg
    refine ⟨φ.comp (reindexGL (R := ZMod 2) (Fintype.equivFinOfCardEq hι).symm).toMonoidHom,
      hinj.comp (MulEquiv.injective _), ?_⟩
    rintro y ⟨x, rfl⟩
    exact hle ⟨_, rfl⟩

theorem cen_t2 (e : ℕ) (he : e ≤ 1) :
    Nat.card (Subgroup.centralizer ({gRep e 2} : Set (GL (Fin e ⊕ Idx) (ZMod 2)))) =
      glc 2 e * glc 4 3 ∧
    ∃ φ : GL (Fin 3) (ZMod 2) →* GL (Fin e ⊕ Idx) (ZMod 2), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({gRep e 2} : Set (GL (Fin e ⊕ Idx) (ZMod 2))) := by
  let κ : Fin e ⊕ Idx ≃ Fin e ⊕ (Fin 3 × Fin 2) := Equiv.refl _
  have hg : ∀ a b, (gRep e 2 : Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix (Fin e ⊕ (Fin 3 × Fin 2)) (Fin e ⊕ (Fin 3 × Fin 2))
        (ZMod 2)) (κ a) (κ b) := by
    intro a b
    rw [gmat_eq]
    exact congrFun (congrFun (hg_t2 e he) a) b
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_of_data κ _ hg, card_GL, card_GL]
    simp [card_K4]
  · obtain ⟨φ, hinj, hle⟩ := exists_embedding_right κ _ hg
    refine ⟨φ.comp embK3, hinj.comp embK3_injective, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hle ⟨_, rfl⟩

end K421FactsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
