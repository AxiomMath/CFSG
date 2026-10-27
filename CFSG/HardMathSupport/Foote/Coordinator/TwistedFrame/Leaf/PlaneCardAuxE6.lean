module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxExch
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb adjEmb_range
  adjEmb_frobenius exists_finite_field_isAlgClosure rootSpan_commute_of_orth
  finite_fixed_subgroup_rational_perfect wordProd_smul_eq_wordMat_mulVec commutator_eq_top_iff)

open CFSG.RankThree.PartOne.TCX.E CFSG.RankThree.Classical2
open CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def e6v1word : List (Fin Tag.E6.rank) := [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

@[expose] noncomputable def e6v1 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6v1word

theorem e6v1_smul (u : Fin Tag.E6.rank → ℤ) : e6v1 • u = wordMat Tag.E6 e6v1word *ᵥ u := by
  rw [e6v1, wordProd_smul_eq_wordMat_mulVec]

@[expose] def UFrame.ofAn {τ : Tag} {ν : ℕ} {S : Set (Fin τ.rank → ℤ)} (E : AnEmbedding τ ν S)
    (L : Type) [Field L] : UFrame τ L ν S where
  ρ := E.ρ L
  r := E.r
  ε := fun i j => if hij : i ≠ j then (E.gen L i j hij).choose else 1
  inj := E.inj L
  isRoot := E.isRoot
  gen := fun i j hij t => by
    simp only [dif_pos hij]
    exact (E.gen L i j hij).choose_spec t
  range := E.range L

@[expose] def UFrame.cast {τ : Tag} {L : Type} [Field L] {ν : ℕ} {S S' : Set (Fin τ.rank → ℤ)}
    (E : UFrame τ L ν S) (h : S = S') : UFrame τ L ν S' where
  ρ := E.ρ
  r := E.r
  ε := E.ε
  inj := E.inj
  isRoot := E.isRoot
  gen := E.gen
  range := by rw [E.range, h]

theorem fixedRootGroup_perfect {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (h : CFSG.IsQuasisimple ↥(fixedRootGroup D S)) :
    ⁅fixedRootGroup D S, fixedRootGroup D S⁆ = fixedRootGroup D S :=
  (commutator_eq_top_iff _).1 (Group.isPerfect_def.1 h.1)

theorem e6_support_chain : ∀ m : Fin 72,
    (∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → e6RootVec m i = 0) →
      (∃ i j : Fin 3, i ≠ j ∧ chainRoot chain13 i j = e6RootVec m) ∨
        (∃ i j : Fin 3, i ≠ j ∧ chainRoot chain56 i j = e6RootVec m) := by
  decide +kernel

theorem e6_chain13_support : ∀ i j : Fin 3, i ≠ j → ∀ k : Fin Tag.E6.rank,
    k.val ∉ TwClass.e6Six.J₂ → chainRoot chain13 i j k = 0 := by
  decide +kernel

theorem e6_chain56_support : ∀ i j : Fin 3, i ≠ j → ∀ k : Fin Tag.E6.rank,
    k.val ∉ TwClass.e6Six.J₂ → chainRoot chain56 i j k = 0 := by
  decide +kernel

theorem e6_S₁_of_orth : ∀ m : Fin 72,
    (∀ k : Fin Tag.E6.rank, k.val ∈ TwClass.e6Six.J₂ →
      iform (e6RootVec m) (Pi.single k 1) = 0) →
      ∃ i j : Fin 3, i ≠ j ∧ wordMat Tag.E6 e6v1word *ᵥ chainRoot chain13 i j = e6RootVec m := by
  decide +kernel

theorem e6_S₁_orth : ∀ i j : Fin 3, i ≠ j → ∀ m : Fin 72,
    (∀ k : Fin Tag.E6.rank, k.val ∉ TwClass.e6Six.J₂ → e6RootVec m k = 0) →
      iform (wordMat Tag.E6 e6v1word *ᵥ chainRoot chain13 i j) (e6RootVec m) = 0 := by
  decide +kernel

theorem e6_w_exch₁ : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain13 i j = chainRoot chain56 i j := by
  decide +kernel

theorem e6_w_exch₂ : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain56 i j = chainRoot chain13 i j := by
  decide +kernel

theorem e6_orth_chains : ∀ i j i' j' : Fin 3, i ≠ j → i' ≠ j' →
    chainRoot chain13 i j ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ chainRoot chain56 i' j') = 0 := by
  decide +kernel

theorem e6_pi₁ : ∃ k : Fin 6, ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ (wordMat Tag.E6 e6v1word *ᵥ chainRoot chain13 i j) =
      wordMat Tag.E6 e6v1word *ᵥ chainRoot chain13 (perm3 k j) (perm3 k i) := by
  decide +kernel

theorem single_apply_eq_zero {k i : Fin Tag.E6.rank} (hk : k.val ∈ TwClass.e6Six.J₂)
    (hi : i.val ∉ TwClass.e6Six.J₂) : (Pi.single k (1 : ℤ) : Fin Tag.E6.rank → ℤ) i = 0 :=
  Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hk)) 1

theorem e6_S₁_eq :
    TwClass.e6Six.S₁ = {r | ∃ i j : Fin 3, i ≠ j ∧ r = e6v1 • chainRoot chain13 i j} := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    obtain ⟨i, j, hij, h⟩ := e6_S₁_of_orth m fun k hk =>
      hs (Pi.single k 1) ⟨isRoot_single _ k, fun i hi => single_apply_eq_zero hk hi⟩
    exact ⟨i, j, hij, by rw [e6v1_smul, h]⟩
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨IsRoot.smul ((a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩).1 e6v1, ?_⟩
    rintro α ⟨hα, hsupp⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    rw [e6v1_smul]
    exact e6_S₁_orth i j hij m hsupp

theorem e6_S₁_emb_eq :
    (fun γ => e6v1 • γ) '' parabolicRoots Tag.E6 support13 = TwClass.e6Six.S₁ := by
  rw [e6_S₁_eq]
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := (a2Std₁.roots γ).1 hγ
    exact ⟨i, j, hij, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨_, (a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩, rfl⟩

theorem e6Six_X₁ (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    Nat.card ↥(TwClass.e6Six.X₁ D) =
        Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1)) ∧
      Nat.card ↥(Subgroup.center ↥(TwClass.e6Six.X₁ D)) = Nat.gcd 3 (Nat.card K + 1) := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hk⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hk
  have hne : ((3 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).2
    omega
  let E₁ : UFrame TwClass.e6Six.tag D.L 3 TwClass.e6Six.S₁ :=
    (UFrame.ofAn (a2Std₁.embedding e6v1) D.L).cast e6_S₁_emb_eq
  obtain ⟨k₁, hπ₁⟩ := e6_pi₁
  set π₁ := perm3 k₁ with hπ₁def
  have hπ₁' : ∀ i j : Fin 3, i ≠ j → TwClass.e6Six.w • E₁.r i j = E₁.r (π₁ j) (π₁ i) := by
    intro i j hij
    show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • (e6v1 • chainRoot chain13 i j) =
      e6v1 • chainRoot chain13 (π₁ j) (π₁ i)
    rw [e6v1_smul, e6v1_smul, wordProd_smul_eq_wordMat_mulVec]
    exact hπ₁ i j hij
  obtain ⟨hfin₁, hcard₁, hq₁⟩ := UFrame.fixedRoot_unitary D (by norm_num) E₁ π₁ hπ₁' hℓ hf hk
  have hq₁' := hq₁ hne
  obtain ⟨e₁⟩ := frame_equiv_fixed D TwClass.e6Six.S₁ (hrat_perfect (Or.inl ⟨rfl, rfl⟩) D) hfin₁
    (fixedRootGroup_perfect D _ hq₁'.1)
  have h3 := card_unitarySet_three (Ω := D.L) (ℓ := ℓ) hf
  refine ⟨?_, ?_⟩
  · rw [show TwClass.e6Six.X₁ D = D.frame TwClass.e6Six.S₁ from rfl, Nat.card_congr e₁.toEquiv,
      hcard₁, h3, hk]
  · rw [show TwClass.e6Six.X₁ D = D.frame TwClass.e6Six.S₁ from rfl,
      natCard_center_eq_of_mulEquiv e₁, hq₁'.2, hk]

@[expose] def e6Sa : Set (Fin Tag.E6.rank → ℤ) := {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot chain13 i j}

@[expose] def e6Sb : Set (Fin Tag.E6.rank → ℤ) := {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot chain56 i j}

theorem e6_Sa_isRoot : ∀ α ∈ e6Sa, IsRoot Tag.E6 α := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact ((a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩).1

theorem e6_Sb_isRoot : ∀ α ∈ e6Sb, IsRoot Tag.E6 α := by
  rintro _ ⟨i, j, hij, rfl⟩
  exact ((a2Std₂.roots _).2 ⟨i, j, hij, rfl⟩).1

theorem e6_S₂_eq : TwClass.e6Six.S₂ = e6Sa ∪ e6Sb := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    rcases e6_support_chain m hs with ⟨i, j, hij, h⟩ | ⟨i, j, hij, h⟩
    · exact Or.inl ⟨i, j, hij, h.symm⟩
    · exact Or.inr ⟨i, j, hij, h.symm⟩
  · rintro (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact ⟨((a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩).1, fun k hk => e6_chain13_support i j hij k hk⟩
    · exact ⟨((a2Std₂.roots _).2 ⟨i, j, hij, rfl⟩).1, fun k hk => e6_chain56_support i j hij k hk⟩

theorem e6_Sa_emb_eq :
    (fun γ => (1 : WeylGroup Tag.E6) • γ) '' parabolicRoots Tag.E6 support13 = e6Sa := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := (a2Std₁.roots γ).1 hγ
    exact ⟨i, j, hij, one_smul _ _⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨_, (a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩, one_smul _ _⟩

theorem e6_hab : ∀ α ∈ e6Sa, (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • α ∈ e6Sb := by
  rintro _ ⟨i, j, hij, rfl⟩
  refine ⟨i, j, hij, ?_⟩
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact e6_w_exch₁ i j hij

theorem e6_hba : ∀ α ∈ e6Sb, (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • α ∈ e6Sa := by
  rintro _ ⟨i, j, hij, rfl⟩
  refine ⟨i, j, hij, ?_⟩
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact e6_w_exch₂ i j hij

theorem e6_hsq : ∀ i j : Fin 3, i ≠ j →
    (coxeterSystem Tag.E6).wordProd TwClass.wordE6 •
      ((coxeterSystem Tag.E6).wordProd TwClass.wordE6 • chainRoot chain13 i j) =
        chainRoot chain13 i j := by
  intro i j hij
  rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, e6_w_exch₁ i j hij]
  exact e6_w_exch₂ i j hij

theorem e6_hcomm (L : Type) [Field L] :
    ∀ x ∈ rootSpan Tag.E6 L e6Sa, ∀ y ∈ rootSpan Tag.E6 L e6Sb, x * y = y * x :=
  CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inl rfl)) e6_Sa_isRoot
    e6_Sb_isRoot (by
      rintro _ ⟨i, j, hij, rfl⟩ _ ⟨i', j', hij', rfl⟩
      exact e6_orth_chains i j i' j' hij hij')

theorem e6Six_X₂_dvd (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {k : ℕ} (hk : p ^ k ∣ Nat.card K ^ 6 * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1))) :
    p ^ k ∣ Nat.card ↥(TwClass.e6Six.X₂ D) := by
  classical
  let Ea : UFrame TwClass.e6Six.tag D.L 3 e6Sa :=
    (UFrame.ofAn (a2Std₁.embedding 1) D.L).cast e6_Sa_emb_eq
  have hsq : ∀ i j : Fin 3, i ≠ j → TwClass.e6Six.w • (TwClass.e6Six.w • Ea.r i j) = Ea.r i j := by
    intro i j hij
    show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 •
      ((coxeterSystem Tag.E6).wordProd TwClass.wordE6 •
        ((1 : WeylGroup Tag.E6) • chainRoot chain13 i j)) =
          (1 : WeylGroup Tag.E6) • chainRoot chain13 i j
    rw [one_smul]
    exact e6_hsq i j hij
  refine exchange_dvd D (S := TwClass.e6Six.S₂) (Sa := e6Sa) (Sb := e6Sb) Ea e6_Sa_isRoot
    e6_Sb_isRoot e6_hab e6_hba hsq ?_
    (e6_hcomm D.L) hp (by omega) (hrat_pgroup (Or.inl ⟨rfl, rfl⟩) D hp (by omega)) hk
  show rootSpan Tag.E6 D.L TwClass.e6Six.S₂ = _
  rw [e6_S₂_eq, rootSpan_union_eq]
  rfl

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
