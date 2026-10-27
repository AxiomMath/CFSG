module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxE8Ten
public import CFSG.RankThree.PartOne.TCX.E.D4Triality

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb adjEmb_range
  wordProd_smul_eq_wordMat_mulVec commutator_eq_top_iff e8RootVec isRoot_e8RootVec
  isRoot_iff_exists_e8RootVec d4Nodes)

open CFSG.RankThree.PartOne.TCX.E (d4_transported_equiv_E8)

open CFSG.RankThree.PartOne.KD4L (d4_layer_equiv_E8)

open CFSG.RankThree.Classical2
open CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem d4_group_facts {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K' : Type) [Field K']
    (hK : Nat.card K' = (ℓ ^ f) ^ 3) (σ : K' ≃+* K')
    (hσ : (∀ c, σ c = c ^ ℓ ^ f) ∨ ∀ c, σ c = c ^ (ℓ ^ f) ^ 2) :
    Finite ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) ∧
      Nat.card ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) =
        CFSG.Open.ordTrialityD4 (ℓ ^ f) ∧
      commutator ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) = ⊤ ∧
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) = ⊥ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨r, hr, hσ'⟩ : ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ c, σ.toRingHom c = c ^ ((ℓ ^ f) ^ r) := by
    rcases hσ with h | h
    · exact ⟨1, Or.inl rfl, fun c => by simpa using h c⟩
    · exact ⟨2, Or.inr rfl, fun c => h c⟩
  haveI : Finite K' := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite (Module.End K' (RootModule TwistTag.D4.tag K')) := Module.finite_of_finite K'
  haveI : Finite (ModGL TwistTag.D4.tag K') :=
    Finite.of_injective (Units.val : ModGL TwistTag.D4.tag K' →
      Module.End K' (RootModule TwistTag.D4.tag K')) Units.val_injective
  have hord := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K' hK r hr σ.toRingHom hσ').1
  haveI : Fintype K' := Fintype.ofFinite K'
  haveI : CharP K' ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K') ℓ :=
    charP_of_injective_algebraMap (algebraMap K' (AlgebraicClosure K')).injective ℓ
  have hsimple := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ hf K' hK
    (AlgebraicClosure K') r hr σ.toRingHom hσ' (iterateFrobenius (AlgebraicClosure K') ℓ f)
    (fun c => iterateFrobenius_def ℓ f c)
  obtain ⟨-, -, -, hS, x, y, hxy⟩ := hsimple
  have hcomm : commutator ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal
      (commutator ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom)) with h | h
    · exfalso
      apply hxy
      have h1 : ⁅x, y⁆ ∈ commutator ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · exact h
  have hcent : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom)) with h | h
    · exact h
    · exfalso
      apply hxy
      have hx : x ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) := by
        rw [h]
        exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.1 hx) y).symm
  refine ⟨inferInstance, ?_, hcomm, hcent⟩
  rw [hord]
  unfold CFSG.Open.ordTrialityD4
  ring

@[expose] def e8v1word : List (Fin Tag.E8.rank) :=
  [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4,
    5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]

@[expose] noncomputable def e8v1 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8v1word

theorem e8v1_smul (u : Fin Tag.E8.rank → ℤ) : e8v1 • u = wordMat Tag.E8 e8v1word *ᵥ u := by
  rw [e8v1, wordProd_smul_eq_wordMat_mulVec]

@[expose] def d4ListA : List (Fin Tag.E8.rank → ℤ) :=
  [![0, -1, -1, -2, -1, 0, 0, 0], ![0, -1, -1, -1, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0, 0], ![0, -1, 0, -1, -1, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, -1, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0]]

@[expose] def d4ListB : List (Fin Tag.E8.rank → ℤ) :=
  [![-2, -3, -4, -6, -5, -4, -3, -2], ![-2, -3, -4, -6, -5, -4, -3, -1], ![0, -1, -1, -2, -2, -2, -2, -1], ![-2, -3, -4, -6, -5, -4, -2, -1], ![0, -1, -1, -2, -2, -2, -1, -1], ![0, -1, -1, -2, -2, -2, -1, 0], ![-2, -2, -3, -4, -3, -2, -2, -1], ![0, 0, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 0, -1, 0], ![-2, -2, -3, -4, -3, -2, -1, -1], ![0, 0, 0, 0, 0, 0, 0, -1], ![-2, -2, -3, -4, -3, -2, -1, 0], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![2, 2, 3, 4, 3, 2, 2, 1], ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![0, 1, 1, 2, 2, 2, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem d4_support_sub : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, ¬(1 ≤ i.val ∧ i.val ≤ 4) → e8RootVec m i = 0) →
      e8RootVec m ∈ d4ListA := by
  decide +kernel

theorem d4_listA_support : ∀ r ∈ d4ListA, ∀ i : Fin Tag.E8.rank,
    ¬(1 ≤ i.val ∧ i.val ≤ 4) → r i = 0 := by
  decide +kernel

theorem d4_listA_roots : ∀ r ∈ d4ListA, ∃ m : Fin 240, e8RootVec m = r := by
  decide +kernel

theorem d4_orth_sub : ∀ m : Fin 240,
    (∀ k : Fin Tag.E8.rank, (1 ≤ k.val ∧ k.val ≤ 4) →
      iform (e8RootVec m) (Pi.single k 1) = 0) → e8RootVec m ∈ d4ListB := by
  decide +kernel

theorem d4_listB_roots : ∀ r ∈ d4ListB, ∃ m : Fin 240, e8RootVec m = r := by
  decide +kernel

theorem d4_listB_orth : ∀ β ∈ d4ListB, ∀ α ∈ d4ListA, iform β α = 0 := by
  decide +kernel

theorem d4_img : d4ListA.map (fun γ => wordMat Tag.E8 e8v1word *ᵥ γ) = d4ListB := by
  decide +kernel

theorem e8Twelve_act : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, ¬(1 ≤ i.val ∧ i.val ≤ 4) → e8RootVec m i = 0) →
      wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ e8RootVec m =
        permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) (e8RootVec m) := by
  decide +kernel

theorem e8Twelve_actB : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, ¬(1 ≤ i.val ∧ i.val ≤ 4) → e8RootVec m i = 0) →
      wordMat Tag.E8 (e8v1word.reverse ++ TwClass.wordE8Twelve ++ e8v1word) *ᵥ e8RootVec m =
        permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) (e8RootVec m) := by
  decide +kernel

theorem d4_S₂_eq : parabolicRoots Tag.E8 (d4Nodes Tag.E8) = {r | r ∈ d4ListA} := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    exact d4_support_sub m hs
  · intro hr
    obtain ⟨m, rfl⟩ := d4_listA_roots r hr
    exact ⟨isRoot_e8RootVec m, d4_listA_support _ hr⟩

theorem e8Twelve_S₂_eq : TwClass.e8Twelve.S₂ = parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  ext α
  constructor
  · rintro ⟨hα, hs⟩
    refine ⟨hα, fun i hi => hs i ?_⟩
    simp only [TwClass.J₂, Finset.mem_insert, Finset.mem_singleton]
    have : ¬(1 ≤ i.val ∧ i.val ≤ 4) := hi
    omega
  · rintro ⟨hα, hs⟩
    refine ⟨hα, fun i hi => hs i ?_⟩
    simp only [TwClass.J₂, Finset.mem_insert, Finset.mem_singleton] at hi
    show ¬(1 ≤ i.val ∧ i.val ≤ 4)
    omega

theorem e8Twelve_S₁_list : TwClass.e8Twelve.S₁ = {r | r ∈ d4ListB} := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    refine d4_orth_sub m fun k hk => hs (Pi.single k 1) ⟨isRoot_single _ k, fun i hi => ?_⟩
    refine single_apply_eq_zero_of_mem (J := TwClass.e8Twelve.J₂) ?_ hi
    simp only [TwClass.J₂, Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hr
    obtain ⟨m, rfl⟩ := d4_listB_roots r hr
    refine ⟨isRoot_e8RootVec m, fun α hα => ?_⟩
    have hα' : α ∈ d4ListA := by
      have h1 : α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8) := e8Twelve_S₂_eq ▸ hα
      rw [d4_S₂_eq] at h1
      exact h1
    exact d4_listB_orth _ hr α hα'

theorem e8Twelve_S₁_eq : TwClass.e8Twelve.S₁ =
    (fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  rw [e8Twelve_S₁_list, d4_S₂_eq]
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, e8v1_smul]
  rw [← d4_img, List.mem_map]

theorem frame_equiv_of_equiv {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ))
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K D.L).range)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (e : ↥(fixedRootGroup D S) ≃* G) : Nonempty (↥(D.frame S) ≃* G) := by
  haveI : Finite ↥(fixedRootGroup D S) := Finite.of_equiv G e.symm.toEquiv
  haveI : Group.IsPerfect ↥(fixedRootGroup D S) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨e'⟩ := frame_equiv_fixed D S hrat inferInstance (Subgroup.isPerfect_iff.1 inferInstance)
  exact ⟨e'.trans e⟩

theorem e8Twelve_frames_aux (K : Type) [Field K] [Finite K] (w : WeylGroup Tag.E8)
    (hw : w = (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve) (D : LangLevi Tag.E8 K w) :
    Nat.card ↥(D.frame ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))) =
        CFSG.Open.ordTrialityD4 (Nat.card K) ∧
      Nat.card ↥(D.frame (parabolicRoots Tag.E8 (d4Nodes Tag.E8))) =
        CFSG.Open.ordTrialityD4 (Nat.card K) ∧
      Nat.card ↥(Subgroup.center ↥(D.frame
        ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)))) = 1 := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hk⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hk
  have hFr : D.Fr = iterateFrobenius D.L ℓ f :=
    RingHom.ext fun c => by rw [D.hFr, hk, iterateFrobenius_def]
  set n : ModGL Tag.E8 D.L := canonicalRep (coxeterSystem Tag.E8) D.L w with hn
  have hnm : n ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hwn : weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hrat := hrat_perfect (Or.inr (Or.inr ⟨rfl, rfl⟩) : (Tag.E8 = Tag.E6 ∧ 1 = 3) ∨
    (Tag.E8 = Tag.E7 ∧ 1 = 2) ∨ (Tag.E8 = Tag.E8 ∧ 1 = 1)) D
  have hcard1 : Nat.card K = ℓ ^ f := hk
  have hP₂ : fixedRootGroup D (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) =
      rootSpan Tag.E8 D.L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius D.L ℓ f))) := by
    show rootSpan Tag.E8 D.L _ ⊓ twistedFixedPoints n (Units.map (entrywiseHom D.Fr)) = _
    rw [hFr]
  have hact₂ : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
    refine ⟨1, one_mem _, fun α hα => ?_⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
    rw [hwn, one_smul, hw, wordProd_smul_eq_wordMat_mulVec]
    exact e8Twelve_act m hα.2
  obtain ⟨K₂, _, _, σ₂, hK₂, hσ₂, ⟨e₂⟩⟩ := d4_layer_equiv_E8 (L := D.L) (ℓ := ℓ) (f := f) hf
    (1 : Fin Tag.E8.rank) 2 4 (by decide) (by decide) (by decide) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) n hnm hact₂
    (fixedRootGroup D (parabolicRoots Tag.E8 (d4Nodes Tag.E8))) hP₂
  obtain ⟨hfin₂, hcard₂, hcomm₂, hcent₂⟩ := d4_group_facts hℓ hf K₂ hK₂ σ₂ hσ₂
  haveI := hfin₂
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom) :=
    Group.isPerfect_def.2 hcomm₂
  obtain ⟨x₂⟩ := frame_equiv_of_equiv D _ hrat e₂
  have hP₁ : fixedRootGroup D ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) =
      rootSpan Tag.E8 D.L ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius D.L ℓ f))) := by
    show rootSpan Tag.E8 D.L _ ⊓ twistedFixedPoints n (Units.map (entrywiseHom D.Fr)) = _
    rw [hFr]
  have hcert₁ : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (e8v1⁻¹ * weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ * e8v1) • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
    refine ⟨1, one_mem _, fun α hα => ?_⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα.1
    have h : e8v1⁻¹ * weylQuotientHom Tag.E8 D.L ⟨n, hnm⟩ * e8v1 =
        (coxeterSystem Tag.E8).wordProd (e8v1word.reverse ++ TwClass.wordE8Twelve ++ e8v1word) := by
      rw [hwn, hw, e8v1, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
        CoxeterSystem.wordProd_reverse]
    rw [h, one_smul, wordProd_smul_eq_wordMat_mulVec]
    exact e8Twelve_actB m hα.2
  obtain ⟨K₁, _, _, σ₁, hK₁, hσ₁, ⟨e₁⟩⟩ := d4_transported_equiv_E8 (L := D.L) (ℓ := ℓ) (f := f) hf
    e8v1 (1 : Fin Tag.E8.rank) 2 4 (by decide) (by decide) (by decide) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) n hnm hcert₁
    (fixedRootGroup D ((fun γ => e8v1 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))) hP₁
  obtain ⟨hfin₁, hcard₁, hcomm₁, hcent₁⟩ := d4_group_facts hℓ hf K₁ hK₁ σ₁ hσ₁
  haveI := hfin₁
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K₁ σ₁.toRingHom) :=
    Group.isPerfect_def.2 hcomm₁
  obtain ⟨x₁⟩ := frame_equiv_of_equiv D _ hrat e₁
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr x₁.toEquiv, hcard₁, hcard1]
  · rw [Nat.card_congr x₂.toEquiv, hcard₂, hcard1]
  · rw [natCard_center_eq_of_mulEquiv x₁, hcent₁]
    exact Subgroup.card_bot

theorem e8Twelve_frames (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    Nat.card ↥(TwClass.e8Twelve.X₁ D) = CFSG.Open.ordTrialityD4 (Nat.card K) ∧
      Nat.card ↥(TwClass.e8Twelve.X₂ D) = CFSG.Open.ordTrialityD4 (Nat.card K) ∧
      Nat.card ↥(Subgroup.center ↥(TwClass.e8Twelve.X₁ D)) = 1 := by
  have h := e8Twelve_frames_aux K TwClass.e8Twelve.w rfl D
  rw [show TwClass.e8Twelve.X₁ D = D.frame TwClass.e8Twelve.S₁ from rfl, e8Twelve_S₁_eq,
    show TwClass.e8Twelve.X₂ D = D.frame TwClass.e8Twelve.S₂ from rfl, e8Twelve_S₂_eq]
  exact ⟨h.2.1.symm ▸ h.1, h.2.1, h.2.2⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
