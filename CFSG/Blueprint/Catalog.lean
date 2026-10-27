module

public import CFSG.Blueprint.Chevalley
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Milestones.FAM_classical_model_membership
public import CFSG.Open.StatedAPI

public noncomputable section

namespace CFSG.Blueprint

open Chevalley Assembly.LowTwoRank

@[expose] def classicalTags : Finset StatedLieTag :=
  {.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus}

@[expose] def chevalleyExceptionalTags : Finset StatedLieTag :=
  {.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4}

@[expose] def reeTitsTags : Finset StatedLieTag :=
  {.twistedG2, .twistedF4, .Tits}

abbrev AdjointQuotient (τ : Tag) (K : Type) [Field K] : Type :=
  ↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)

abbrev DerivedCentralQuotient {M : Type} [Group M] (H : Subgroup M) : Type :=
  ↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆

@[expose] def twistedFixedGroup (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (ModGL t.tag K) :=
  adjointGroup t.tag K ⊓ MonoidHom.eqLocus (twistHom t K σ) (MonoidHom.id _)

@[expose] def UntwistedChevalleyModel (G : Type) [Group G] (τ : Tag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (G ≃* AdjointQuotient τ K)

@[expose] def TwistedChevalleyModel (G : Type) [Group G] (t : TwistTag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ t.order ∧
    ∃ σ : K →+* K, (∀ c, σ c = c ^ q) ∧
      Nonempty (G ≃* DerivedCentralQuotient (twistedFixedGroup t K σ))

@[expose] def ChevalleyExceptionalModel (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ) :
    Prop :=
  StatedLieAdmissible t 0 p f ∧
    match t with
    | .G2 => UntwistedChevalleyModel G .G2 (p ^ f)
    | .F4 => UntwistedChevalleyModel G .F4 (p ^ f)
    | .E6 => UntwistedChevalleyModel G .E6 (p ^ f)
    | .E7 => UntwistedChevalleyModel G .E7 (p ^ f)
    | .E8 => UntwistedChevalleyModel G .E8 (p ^ f)
    | .twistedE6 => TwistedChevalleyModel G .E6 (p ^ f)
    | .trialityD4 => TwistedChevalleyModel G .D4 (p ^ f)
    | _ => False

@[expose] def reeRelationGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K × ModGL τ K) :=
  Subgroup.closure {gh | ∃ (i : Fin τ.rank) (c : K),
    ((gh.1 : Module.End K (RootModule τ K)) = xOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = xOp τ K (ρ i) (c ^ e i)) ∨
      ((gh.1 : Module.End K (RootModule τ K)) = yOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = yOp τ K (ρ i) (c ^ e i))}

@[expose] def reeFixedGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ (reeRelationGroup τ K ρ e).comap ((MonoidHom.id _).prod (MonoidHom.id _))

@[expose] def reeG2Perm : Equiv.Perm (Fin Tag.G2.rank) :=
  (Equiv.swap 0 1 : Equiv.Perm (Fin 2))

@[expose] def reeF4Perm : Equiv.Perm (Fin Tag.F4.rank) :=
  (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))

@[expose] def reeG2Long : Finset (Fin Tag.G2.rank) :=
  ({0} : Finset (Fin 2))

@[expose] def reeF4Long : Finset (Fin Tag.F4.rank) :=
  ({0, 1} : Finset (Fin 4))

@[expose] def ReeTitsRelationModel (G : Type) [Group G] (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
    Nonempty (G ≃* DerivedCentralQuotient
      (reeFixedGroup τ K ρ fun i => if i ∈ L then p ^ a else p ^ (a + 1)))

@[expose] def ReeTitsModel (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ) : Prop :=
  StatedLieAdmissible t 0 p f ∧ ∃ a : ℕ, f = 2 * a + 1 ∧
    match t with
    | .twistedG2 => ReeTitsRelationModel G .G2 reeG2Perm reeG2Long p f a
    | .twistedF4 => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | .Tits => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | _ => False

section Suzuki

variable (a : ℕ) {K : Type} [Field K]

@[expose] def suzukiN (u v : K) : K :=
  u ^ (2 ^ (a + 1) + 2) + u * v + v ^ 2 ^ (a + 1)

@[expose] def suzukiS (u v : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
    u, 1, 0, 0;
    v, u ^ 2 ^ (a + 1), 1, 0;
    suzukiN a u v, u ^ (2 ^ (a + 1) + 1) + v, u, 1]

@[expose] def suzukiD (l : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)]

variable (K) in
@[expose] def suzukiW : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

variable (K) in
@[expose] def suzukiGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure {g | (∃ u v : K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v) ∨
    (∃ l : Kˣ, (g : Matrix (Fin 4) (Fin 4) K) = suzukiD a l) ∨
    (g : Matrix (Fin 4) (Fin 4) K) = suzukiW K}

end Suzuki

@[expose] def SuzukiModel (G : Type) [Group G] (p f : ℕ) : Prop :=
  p = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧ Nonempty (G ≃* suzukiGroup a K)

@[expose] def ExceptionalRep (G : Type) [Group G] : Prop :=
  (∃ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags ∧
      ChevalleyExceptionalModel G t p f) ∨
    (∃ (t : StatedLieTag) (p f : ℕ), t ∈ reeTitsTags ∧ ReeTitsModel G t p f) ∨
    ∃ p f : ℕ, SuzukiModel G p f

@[expose] def Catalog (G : Type) [Group G] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    Milestones.ClassicalRep G ∨ ExceptionalRep G ∨ NativeSporadic.SporadicRep G

@[expose] def LieModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t ∈ classicalTags ∧ StatedClassicalModel G t n p f) ∨
    (n = 0 ∧ t ∈ chevalleyExceptionalTags ∧ ChevalleyExceptionalModel G t p f) ∨
    (n = 0 ∧ t ∈ reeTitsTags ∧ ReeTitsModel G t p f) ∨
    (n = 0 ∧ t = .twistedB2 ∧ SuzukiModel G p f)

@[expose] def OddLieType (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible t n p f ∧
    LieModel X t n p f

@[expose] def EvenLieType (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 2 f ∧ LieModel X t n 2 f

theorem LieModel.admissible {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) : StatedLieAdmissible t n p f := by
  rcases h with ⟨-, h⟩ | ⟨rfl, -, h⟩ | ⟨rfl, -, h⟩ | ⟨rfl, rfl, h⟩
  · exact h.1
  · exact h.1
  · exact h.1
  · obtain ⟨rfl, a, ha, _, _, _, rfl, _⟩ := h
    exact ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩

theorem LieModel.statedClassicalModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (ht : t ∈ classicalTags) : StatedClassicalModel G t n p f := by
  rcases h with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, rfl, -⟩
  · exact h
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact absurd ht (by decide)

theorem LieModel.statedClassicalModel_of_ne_zero {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel G t n p f) : StatedClassicalModel G t n p f := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 hn

theorem LieModel.chevalleyExceptionalModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (ht : t ∈ chevalleyExceptionalTags) :
    ChevalleyExceptionalModel G t p f := by
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact h
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact absurd h (by revert ht; cases t <;> decide)

theorem LieModel.reeTitsModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (ht : t ∈ reeTitsTags) : n = 0 ∧ ReeTitsModel G t p f := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨hn, -, h⟩ | ⟨-, h, -⟩
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact ⟨hn, h⟩
  · exact absurd h (by revert ht; cases t <;> decide)

theorem LieModel.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel G t n p f) : LieModel G' t n p f := by
  rcases h with ⟨ht, h⟩ | ⟨hn, ht, hadm, h⟩ | ⟨hn, ht, hadm, a, ha, h⟩ |
      ⟨hn, ht, hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩
  · exact Or.inl ⟨ht, Open.StatedAPI.statedClassicalModel_of_mulEquiv e h⟩
  · refine Or.inr (Or.inl ⟨hn, ht, hadm, ?_⟩)
    cases t <;> first
      | exact h
      | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
         exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)
      | (obtain ⟨K, hK, hKf, hcard, σ, hσ, ⟨e'⟩⟩ := h
         exact ⟨K, hK, hKf, hcard, σ, hσ, ⟨e.symm.trans e'⟩⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨hn, ht, hadm, a, ha, ?_⟩))
    cases t <;> first
      | exact h
      | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
         exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hn, ht, hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.symm.trans e'⟩⟩))

theorem lieModel_catalog (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ)
    (h : LieModel G t n p f) : Catalog G := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact .inr (.inr (.inl ((Milestones.fam_classical_model_membership_alltags G).2 ⟨t, n, p, f, h⟩)))
  · exact .inr (.inr (.inr (.inl (.inl ⟨t, p, f, ht, h⟩))))
  · exact .inr (.inr (.inr (.inl (.inr (.inl ⟨t, p, f, ht, h⟩)))))
  · exact .inr (.inr (.inr (.inl (.inr (.inr ⟨p, f, h⟩)))))

end CFSG.Blueprint
