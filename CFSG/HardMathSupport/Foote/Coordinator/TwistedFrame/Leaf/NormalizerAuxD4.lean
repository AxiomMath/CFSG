module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxF4
public import CFSG.RankThree.PartOne.TCX.E.D4Triality

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6 CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.TCX.E
open Matrix
open scoped MatrixGroups Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


set_option linter.unusedSectionVars false


@[expose] def d4ListA : List (Fin Tag.E8.rank → ℤ) :=
  [![0, -1, -1, -2, -1, 0, 0, 0], ![0, -1, -1, -1, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0, 0], ![0, -1, 0, -1, -1, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, -1, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0]]

@[expose] def d4ListB : List (Fin Tag.E8.rank → ℤ) :=
  [![-2, -3, -4, -6, -5, -4, -3, -2], ![-2, -3, -4, -6, -5, -4, -3, -1], ![-2, -3, -4, -6, -5, -4, -2, -1], ![-2, -2, -3, -4, -3, -2, -2, -1], ![-2, -2, -3, -4, -3, -2, -1, -1], ![-2, -2, -3, -4, -3, -2, -1, 0], ![0, -1, -1, -2, -2, -2, -2, -1], ![0, -1, -1, -2, -2, -2, -1, -1], ![0, -1, -1, -2, -2, -2, -1, 0], ![0, 0, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1, 0], ![2, 2, 3, 4, 3, 2, 1, 1], ![2, 2, 3, 4, 3, 2, 2, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 3, 2]]

@[expose] def d4WordV : List (Fin Tag.E8.rank) := [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]

theorem S₂_e8Twelve : TwClass.S₂ TwClass.e8Twelve = {r | r ∈ d4ListA} := by
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    have : ∀ m : Fin 240, (∀ i : Fin Tag.E8.rank, i.val ∉ ({1, 2, 3, 4} : Finset ℕ) →
        e8RootVec m i = 0) → e8RootVec m ∈ d4ListA := by decide +kernel
    exact this m hs
  · intro hr
    have : ∀ r ∈ d4ListA, (∃ m : Fin 240, e8RootVec m = r) ∧
        ∀ i : Fin Tag.E8.rank, i.val ∉ ({1, 2, 3, 4} : Finset ℕ) → r i = 0 := by decide +kernel
    obtain ⟨⟨m, rfl⟩, hs⟩ := this α hr
    exact ⟨isRoot_e8RootVec m, hs⟩

theorem S₁_e8Twelve : TwClass.S₁ TwClass.e8Twelve = {r | r ∈ d4ListB} := by
  ext β
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    rw [S₂_e8Twelve] at ho
    have : ∀ m : Fin 240, (∀ α ∈ d4ListA, iform (τ := Tag.E8) (e8RootVec m) α = 0) →
        e8RootVec m ∈ d4ListB := by decide +kernel
    exact this m fun α hα => ho α hα
  · intro hr
    refine ⟨?_, fun α hα => ?_⟩
    · have : ∀ r ∈ d4ListB, ∃ m : Fin 240, e8RootVec m = r := by decide +kernel
      obtain ⟨m, rfl⟩ := this β hr
      exact isRoot_e8RootVec m
    · rw [S₂_e8Twelve] at hα
      have : ∀ r ∈ d4ListB, ∀ α ∈ d4ListA, iform (τ := Tag.E8) r α = 0 := by decide +kernel
      exact this β hr α hα

theorem parabolicRoots_d4Nodes : parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
    TwClass.S₂ TwClass.e8Twelve := by
  have hiff : ∀ i : Fin Tag.E8.rank, i ∈ d4Nodes Tag.E8 ↔ i.val ∈ TwClass.J₂ TwClass.e8Twelve := by
    intro i
    simp only [d4Nodes, Set.mem_setOf_eq, TwClass.J₂, Finset.mem_insert, Finset.mem_singleton]
    omega
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).1 h)⟩
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).2 h)⟩

@[expose] noncomputable def d4V : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd d4WordV

theorem d4V_smul (u : Fin Tag.E8.rank → ℤ) : d4V • u = wordMat Tag.E8 d4WordV *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 d4WordV u

theorem d4_img : ∀ r ∈ d4ListA, wordMat Tag.E8 d4WordV *ᵥ r ∈ d4ListB := by decide +kernel

theorem d4_cover : ∀ r ∈ d4ListB, ∃ γ ∈ d4ListA, wordMat Tag.E8 d4WordV *ᵥ γ = r := by
  decide +kernel

theorem image_one_d4 : (fun γ => (1 : WeylGroup Tag.E8) • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
    TwClass.S₂ TwClass.e8Twelve := by
  simp only [one_smul, Set.image_id']
  exact parabolicRoots_d4Nodes

theorem image_d4V : (fun γ => d4V • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
    TwClass.S₁ TwClass.e8Twelve := by
  rw [parabolicRoots_d4Nodes, S₂_e8Twelve, S₁_e8Twelve]
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    show d4V • γ ∈ d4ListB
    rw [d4V_smul]
    exact d4_img γ hγ
  · intro hr
    obtain ⟨γ, hγ, h⟩ := d4_cover r hr
    exact ⟨γ, hγ, by show d4V • γ = r; rw [d4V_smul]; exact h⟩

theorem w_d4_one : ∀ α ∈ d4ListA, wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ α =
    permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by decide +kernel

theorem w_d4_conj : ∀ α ∈ d4ListA,
    wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ (wordMat Tag.E8 d4WordV *ᵥ α) =
      wordMat Tag.E8 d4WordV *ᵥ permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
  decide +kernel


theorem quasisimple_outer_solvable_d4_layer {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α)
    (P : Subgroup (ModGL Tag.E8 L))
    (hP : P = rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    CFSG.IsQuasisimple ↥P ∧ Group.IsSolvable (Outer ↥P) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := d4_transported_equiv_E8 hf v 1 2 4 (by decide) (by decide)
    (by decide) (by simp [Tag.rank]) (by simp [Tag.rank]) (by simp [Tag.rank]) n hn hcert P hP
  obtain ⟨r, hr, hσr⟩ : ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ c, σ.toRingHom c = c ^ ((ℓ ^ f) ^ r) := by
    rcases hσ with h | h
    · exact ⟨1, Or.inl rfl, fun c => by rw [pow_one]; exact h c⟩
    · exact ⟨2, Or.inr rfl, fun c => h c⟩
  obtain ⟨hs, hnc⟩ := isSimple_graphFixedRootGroup_triality Fact.out hf hK r hr σ.toRingHom hσr
  have hq : CFSG.IsQuasisimple (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    isQuasisimple_of_isSimpleGroup hs hnc
  have hOut : Group.IsSolvable (Outer (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    ⟨⟨3, (exceptional_fixed_root_group_Schreier TwistTag.D4 K σ).2 rfl⟩⟩
  haveI := hOut
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq,
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm⟩


theorem hcert_of_action {L : Type} [Field L] (v w : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hn : n ∈ monomialSubgroup Tag.E8 L) (hw : weylQuotientHom Tag.E8 L ⟨n, hn⟩ = w)
    (h : ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      w • (v • α) = v • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α) :
    ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
  refine ⟨1, one_mem _, fun α hα => ?_⟩
  rw [hw, one_smul, mul_smul, mul_smul, inv_smul_eq_iff]
  exact h α hα

section Class

variable {K : Type} [Field K] [Finite K]

private theorem d4_setup (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    ∃ (p m : ℕ) (_ : Fact p.Prime) (_ : CharP D.L p) (_ : IsAlgClosed D.L),
      1 ≤ m ∧ D.Fr = iterateFrobenius D.L p m := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  exact ⟨p, m, ⟨hpp⟩, inferInstance, inferInstance, m.pos,
    RingHom.ext fun c => by rw [iterateFrobenius_def, D.hFr, hcard']⟩

theorem e8Twelve_X₂ (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₂ TwClass.e8Twelve)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₂ TwClass.e8Twelve))) := by
  obtain ⟨p, m, hp, hch, hac, hm, hFr⟩ := d4_setup D
  have hnm : nW D ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L _
  have hw : weylQuotientHom Tag.E8 D.L ⟨nW D, hnm⟩ =
      (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hcert := hcert_of_action 1 _ (nW D) hnm hw (fun α hα => by
    rw [parabolicRoots_d4Nodes, S₂_e8Twelve] at hα
    rw [one_smul, one_smul, wordProd_smul_eq_wordMat_mulVec]
    exact w_d4_one α hα)
  have key := quasisimple_outer_solvable_d4_layer hm 1 (nW D) hnm hcert
    (fixedRoot D (TwClass.S₂ TwClass.e8Twelve)) (by
      rw [image_one_d4, ← hFr]
      rfl)
  exact quasisimple_outer_frame_of_fixedRoot D key

theorem e8Twelve_X₁ (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₁ TwClass.e8Twelve)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₁ TwClass.e8Twelve))) := by
  obtain ⟨p, m, hp, hch, hac, hm, hFr⟩ := d4_setup D
  have hnm : nW D ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L _
  have hw : weylQuotientHom Tag.E8 D.L ⟨nW D, hnm⟩ =
      (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hcert := hcert_of_action d4V _ (nW D) hnm hw (fun α hα => by
    rw [parabolicRoots_d4Nodes, S₂_e8Twelve] at hα
    rw [d4V_smul, d4V_smul, wordProd_smul_eq_wordMat_mulVec]
    exact w_d4_conj α hα)
  have key := quasisimple_outer_solvable_d4_layer hm d4V (nW D) hnm hcert
    (fixedRoot D (TwClass.S₁ TwClass.e8Twelve)) (by
      rw [image_d4V, ← hFr]
      rfl)
  exact quasisimple_outer_frame_of_fixedRoot D key

end Class

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
