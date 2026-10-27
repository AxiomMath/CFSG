module

public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Blueprint.Chevalley.TwistTag
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem


set_option linter.unusedSectionVars false

variable (t : TwistTag)

@[expose] def relCs :
    CoxeterSystem (coxeterMatrix (isFiniteType_cartan t.foldedTag)) (relWeylTwist t) :=
  (coxeterSystem t.foldedTag).map (foldedWeylEquiv t).symm

variable {t}

theorem relCs_simple (a : Fin t.foldedTag.rank) :
    (relCs t).simple a = ⟨t.orbitReflection a, t.orbitReflection_mem a⟩ := by
  rw [relCs, CoxeterSystem.map_simple, MulEquiv.symm_apply_eq]
  exact (foldedWeylEquiv_orbitReflection t a).symm

theorem relCs_wordProd (ω : List (Fin t.foldedTag.rank)) :
    foldedWeylEquiv t ((relCs t).wordProd ω) = (coxeterSystem t.foldedTag).wordProd ω := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons, map_mul, ih, relCs,
      CoxeterSystem.map_simple]
    simp

theorem relCs_length (w : relWeylTwist t) :
    (relCs t).length w = (coxeterSystem t.foldedTag).length (foldedWeylEquiv t w) := by
  have hword : ∀ ω : List (Fin t.foldedTag.rank), (relCs t).wordProd ω =
      (foldedWeylEquiv t).symm ((coxeterSystem t.foldedTag).wordProd ω) := by
    intro ω
    induction ω with
    | nil => simp [CoxeterSystem.wordProd_nil]
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons, ih, relCs,
        CoxeterSystem.map_simple, map_mul]
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, he⟩ := (coxeterSystem t.foldedTag).exists_isReduced (foldedWeylEquiv t w)
    have h1 : (relCs t).wordProd ω = w := by
      rw [hword, ← he]
      exact (foldedWeylEquiv t).symm_apply_apply w
    have h2 := (relCs t).length_wordProd_le ω
    rw [h1] at h2
    have h3 := hω.eq
    rw [← he] at h3
    omega
  · obtain ⟨ω, hω, he⟩ := (relCs t).exists_isReduced w
    have h1 : (coxeterSystem t.foldedTag).wordProd ω = foldedWeylEquiv t w := by
      have := hword ω
      rw [← he] at this
      rw [this]
      exact ((foldedWeylEquiv t).apply_symm_apply _).symm
    have h2 := (coxeterSystem t.foldedTag).length_wordProd_le ω
    rw [h1] at h2
    have h3 := hω.eq
    rw [← he] at h3
    omega

theorem relCs_length_eq (w : relWeylTwist t) : (relCs t).length w = t.orbitLength w :=
  (relCs_length w).trans (orbitLength_eq t w).symm

theorem relCs_length_simple_mul_iff (a : Fin t.foldedTag.rank) (w : relWeylTwist t) :
    (relCs t).length ((relCs t).simple a * w) = (relCs t).length w + 1 ↔
      ∀ i ∈ t.orbit a,
        0 < height ((w : WeylGroup t.tag)⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) := by
  have hsimp : (((relCs t).simple a * w : relWeylTwist t) : WeylGroup t.tag) =
      t.orbitReflection a * w := by
    rw [relCs_simple]
    rfl
  rw [relCs_length_eq, relCs_length_eq, hsimp]
  rcases forall_height_pos_or_forall_height_neg (inv_mem w.2) a with hpos | hneg
  · obtain ⟨h1, -⟩ := length_orbitReflection_mul_of_pos t w.2 hpos
    exact ⟨fun _ => hpos, fun _ => h1⟩
  · obtain ⟨h1, -⟩ := length_orbitReflection_mul_of_neg t w.2 hneg
    refine ⟨fun h => ?_, fun h => ?_⟩
    · omega
    · obtain ⟨i, hi⟩ := t.orbit_nonempty a
      have := h i hi
      have := hneg i hi
      omega

theorem length_orbitReflection_mul_of_relCs (a : Fin t.foldedTag.rank) (w : relWeylTwist t)
    (h : (relCs t).length ((relCs t).simple a * w) = (relCs t).length w + 1) :
    (coxeterSystem t.tag).length (t.orbitReflection a * w) =
      (coxeterSystem t.tag).length (w : WeylGroup t.tag) + (t.orbit a).card :=
  (length_orbitReflection_mul_of_pos t w.2 ((relCs_length_simple_mul_iff a w).1 h)).2

@[expose] def negOrbitRoots (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Set (Fin t.tag.rank → ℤ) :=
  (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)

@[expose] def negComplementRoots (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Set (Fin t.tag.rank → ℤ) :=
  {α | IsRoot t.tag α ∧ height α < 0} \
    negOrbitRoots t a

structure LongestData (t : TwistTag) where
  w : WeylGroup t.tag
  mem : w ∈ relWeylTwist t
  perm_symm : t.perm.symm = t.perm
  smul : ∀ α, w • α = -(permLattice t.perm α)

namespace LongestData

theorem permLattice_permLattice (D : LongestData t) (α : Fin t.tag.rank → ℤ) :
    permLattice t.perm (permLattice t.perm α) = α := by
  have h := permLattice_symm_permLattice t.perm α
  rwa [D.perm_symm] at h

theorem image_smul_eq_neg (D : LongestData t) {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, permLattice t.perm α ∈ S) :
    (fun α => D.w • α) '' S = (fun α => -α) '' S := by
  ext γ
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨_, hS α hα, (D.smul α).symm⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨permLattice t.perm β, hS β hβ, ?_⟩
    simp only [D.smul, permLattice_permLattice D]

theorem image_smul_posRoots (D : LongestData t) :
    (fun α => D.w • α) '' {α | IsRoot t.tag α ∧ 0 < height α} =
      {α | IsRoot t.tag α ∧ height α < 0} := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hα, hp⟩, rfl⟩
    show D.w • α ∈ _
    rw [D.smul]
    refine ⟨CFSG.LieType.Chevalley.IsRoot.neg (hα.permLattice t.cartan_perm), ?_⟩
    rw [height_neg, height_permLattice]
    omega
  · rintro ⟨hγ, hn⟩
    have hr : IsRoot t.tag (permLattice t.perm (-γ)) := (CFSG.LieType.Chevalley.IsRoot.neg hγ).permLattice t.cartan_perm
    refine ⟨permLattice t.perm (-γ), ⟨hr, ?_⟩, ?_⟩
    · rw [height_permLattice, height_neg]
      omega
    · simp only [D.smul, permLattice_neg, permLattice_permLattice D, neg_neg]

theorem image_smul_simpleOrbitRoots (D : LongestData t) (a : Fin t.foldedTag.rank) :
    (fun α => D.w • α) '' simpleOrbitRoots t a =
      negOrbitRoots t a := by
  rw [D.image_smul_eq_neg (simpleOrbitRoots_perm a), simpleOrbitRoots, Set.image_image,
    negOrbitRoots]

theorem image_smul_simpleComplementRoots (D : LongestData t) (a : Fin t.foldedTag.rank) :
    (fun α => D.w • α) '' simpleComplementRoots t a = negComplementRoots t a := by
  rw [simpleComplementRoots, negComplementRoots, ← D.image_smul_simpleOrbitRoots a,
    ← D.image_smul_posRoots]
  exact Set.image_sdiff (fun x y h => by simpa using h) _ _

end LongestData

@[expose] def e6W0Word : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0] : List (Fin 6))

theorem wordProd_smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem e6W0_single : ∀ i : Fin TwistTag.E6.tag.rank,
    e6W0Word.foldr (reflect TwistTag.E6.tag) (Pi.single i 1) =
      -Pi.single (TwistTag.E6.perm i) 1 := by
  decide +kernel

theorem e6W0_smul (α : Fin TwistTag.E6.tag.rank → ℤ) :
    (coxeterSystem TwistTag.E6.tag).wordProd e6W0Word • α =
      -(permLattice TwistTag.E6.perm α) := by
  have hf : ∀ i : Fin TwistTag.E6.tag.rank, ∀ c : ℤ,
      (coxeterSystem TwistTag.E6.tag).wordProd e6W0Word •
          (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ) =
        -(permLattice TwistTag.E6.perm (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ)) := by
    intro i c
    have e : (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have e' : permLattice TwistTag.E6.perm (c • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) =
        c • Pi.single (TwistTag.E6.perm i) 1 := by
      ext j
      simp [permLattice, Pi.single_apply, Equiv.symm_apply_eq]
    rw [e, smul_comm, wordProd_smul_foldr, e6W0_single, e', smul_neg]
  conv_lhs => rw [← Finset.univ_sum_single α]
  rw [Finset.smul_sum]
  simp only [hf, Finset.sum_neg_distrib]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single α]
  ext j
  simp [permLattice, Finset.sum_apply]

theorem e6_perm_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by decide +kernel

@[expose] def e6LongestData : LongestData TwistTag.E6 where
  w := (coxeterSystem TwistTag.E6.tag).wordProd e6W0Word
  mem := by
    refine (mem_relWeylTwist_iff_smul TwistTag.E6).2 fun v => ?_
    rw [e6W0_smul, e6W0_smul, permLattice_neg]
  perm_symm := e6_perm_symm
  smul := e6W0_smul

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
