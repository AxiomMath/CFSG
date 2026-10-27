module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinK4

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421CGProof

open Matrix K421CenProof K421K4Proof

section Reindex

variable {R : Type} [CommRing R] {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

@[expose] def reindexGL (κ : X ≃ Y) : GL X R ≃* GL Y R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R κ).toRingEquiv.toMulEquiv

theorem reindexGL_val (κ : X ≃ Y) (g : GL X R) :
    ((reindexGL κ g : GL Y R) : Matrix Y Y R) = Matrix.reindex κ κ (g : Matrix X X R) := rfl

end Reindex

@[expose] def glc (q n : ℕ) : ℕ := ∏ i : Fin n, (q ^ n - q ^ (i : ℕ))

theorem card_GL {F : Type} [Field F] [Fintype F] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Nat.card (GL ι F) = glc (Fintype.card F) (Fintype.card ι) := by
  rw [Nat.card_congr (reindexGL (R := F) (Fintype.equivFin ι)).toEquiv]
  exact Matrix.card_GL_field (Fintype.card ι)

theorem glc_two : glc 2 0 = 1 ∧ glc 2 1 = 1 ∧ glc 2 2 = 6 ∧ glc 2 3 = 168 ∧ glc 2 4 = 20160 ∧
    glc 2 5 = 9999360 := by
  unfold glc
  decide +kernel

theorem glc_four : glc 4 1 = 3 ∧ glc 4 2 = 180 ∧ glc 4 3 = 181440 := by
  unfold glc
  decide +kernel

variable {X : Type} [Fintype X] [DecidableEq X] {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]

theorem centralizer_data (κ : X ≃ ι ⊕ (β × Fin 2)) (g : GL X (ZMod 2))
    (hg : ∀ a b, (g : Matrix X X (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) (κ a) (κ b)) :
    ∃ φ : GL ι (ZMod 2) × GL β K4 →* GL X (ZMod 2), Function.Injective φ ∧
      φ.range = Subgroup.centralizer ({g} : Set (GL X (ZMod 2))) := by
  let e : GL X (ZMod 2) ≃* GL (ι ⊕ (β × Fin 2)) (ZMod 2) := reindexGL κ
  have hge : e g = gGL psi4 omega4 omega4_cube' := by
    apply Units.ext
    ext a b
    show Matrix.reindex κ κ (g : Matrix X X (ZMod 2)) a b = gmat psi4 omega4 a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hg]
    simp
  refine ⟨e.symm.toMonoidHom.comp (Phi psi4), ?_, ?_⟩
  · exact e.symm.injective.comp (Phi_injective psi4)
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      have hmem : Phi psi4 p ∈ Subgroup.centralizer ({gGL psi4 omega4 omega4_cube'} :
          Set (GL (ι ⊕ (β × Fin 2)) (ZMod 2))) := by
        rw [← range_Phi4]
        exact ⟨p, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hmem ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      show h * e.symm (Phi psi4 p) = e.symm (Phi psi4 p) * h
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hge]
      exact hmem _ rfl
    · intro hx
      have hex : e x ∈ Subgroup.centralizer ({gGL psi4 omega4 omega4_cube'} :
          Set (GL (ι ⊕ (β × Fin 2)) (ZMod 2))) := by
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have h1 := hx g rfl
        rw [← hge, ← map_mul, ← map_mul, h1]
      rw [← range_Phi4] at hex
      obtain ⟨p, hp⟩ := hex
      refine ⟨p, ?_⟩
      show e.symm (Phi psi4 p) = x
      rw [hp]
      exact e.symm_apply_apply x

theorem card_centralizer_of_data (κ : X ≃ ι ⊕ (β × Fin 2)) (g : GL X (ZMod 2))
    (hg : ∀ a b, (g : Matrix X X (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) (κ a) (κ b)) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL X (ZMod 2)))) =
      Nat.card (GL ι (ZMod 2)) * Nat.card (GL β K4) := by
  obtain ⟨φ, hinj, hr⟩ := centralizer_data κ g hg
  rw [← hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

theorem exists_embedding_left (κ : X ≃ ι ⊕ (β × Fin 2)) (g : GL X (ZMod 2))
    (hg : ∀ a b, (g : Matrix X X (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) (κ a) (κ b)) :
    ∃ φ : GL ι (ZMod 2) →* GL X (ZMod 2), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({g} : Set (GL X (ZMod 2))) := by
  obtain ⟨φ, hinj, hr⟩ := centralizer_data κ g hg
  refine ⟨φ.comp (MonoidHom.inl _ _), hinj.comp (fun a b h => congrArg Prod.fst h), ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← hr]
  exact ⟨(A, 1), rfl⟩

theorem exists_embedding_right (κ : X ≃ ι ⊕ (β × Fin 2)) (g : GL X (ZMod 2))
    (hg : ∀ a b, (g : Matrix X X (ZMod 2)) a b =
      (gmat psi4 omega4 : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) (κ a) (κ b)) :
    ∃ φ : GL β K4 →* GL X (ZMod 2), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({g} : Set (GL X (ZMod 2))) := by
  obtain ⟨φ, hinj, hr⟩ := centralizer_data κ g hg
  refine ⟨φ.comp (MonoidHom.inr _ _), hinj.comp (fun a b h => congrArg Prod.snd h), ?_⟩
  rintro _ ⟨B, rfl⟩
  rw [← hr]
  exact ⟨(1, B), rfl⟩

noncomputable def embK3 : GL (Fin 3) (ZMod 2) →* GL (Fin 3) K4 :=
  Units.map ((algebraMap (ZMod 2) K4).mapMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) →+*
    Matrix (Fin 3) (Fin 3) K4).toMonoidHom

theorem embK3_injective : Function.Injective embK3 :=
  Units.map_injective (Matrix.map_injective (algebraMap (ZMod 2) K4).injective)

end K421CGProof

end CFSG.LocalAnalysis.RankThreeUC.S15
