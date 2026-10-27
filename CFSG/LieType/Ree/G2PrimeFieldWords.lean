module

public import CFSG.LieType.Ree.ConstWordCheck
public import CFSG.LieType.Ree.FixedPositiveBlocks
public import CFSG.LieType.Ree.FixedMonomialQuotient

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

section Aut

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

@[expose] def wordWeylElement
    (w : List ℕ) : adjointGroup t.tag K :=
  ((w.map fun i => weylElement t.tag K (t.tag.idx i)).reverse).prod

omit [Finite K] [CharP K t.prime] in
theorem coe_wordWeylElement
    (w : List ℕ) :
    ((wordWeylElement (t := t) (K := K) w : adjointGroup t.tag K) : ModGL t.tag K) =
      ((w.map fun i => weylElt t.tag K (t.tag.idx i) 1).reverse).prod := by
  rw [wordWeylElement, Subgroup.val_list_prod, List.map_reverse, List.map_map]
  rfl

theorem idx_perm (i : ℕ) : t.tag.idx ((t.perm (t.tag.idx i) : Fin t.tag.rank) : ℕ) =
    t.perm (t.tag.idx i) :=
  Fin.ext (Nat.mod_eq_of_lt (Fin.is_lt _))

theorem finiteReeAut_wordWeylElement
    (w : List ℕ) :
    t.finiteReeAut K a (wordWeylElement w) =
      wordWeylElement (w.map fun i => ((t.perm (t.tag.idx i) : Fin t.tag.rank) : ℕ)) := by
  rw [wordWeylElement, wordWeylElement, map_list_prod, List.map_reverse, List.map_map,
    List.map_map]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, finiteReeAut_weylElement, Function.comp_apply, idx_perm]

theorem finiteReeAut_pinnedX
    {α β : Fin t.tag.rank → ℤ} {j : Fin t.tag.rank} {w : List ℕ}
    (hα : pinnedData t.tag α = (j, w, 1))
    (hβ : pinnedData t.tag β =
      (t.perm j, w.map fun i => ((t.perm (t.tag.idx i) : Fin t.tag.rank) : ℕ), 1)) (c : K) :
    t.finiteReeAut K a ⟨pinnedX t.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
      ⟨pinnedX t.tag K β (c ^ t.relationExponent a j), pinnedX_mem_adjointGroup β _⟩ := by
  have hdec : ∀ (γ : Fin t.tag.rank → ℤ) (k : Fin t.tag.rank) (v : List ℕ),
      pinnedData t.tag γ = (k, v, 1) → ∀ d : K,
        (⟨pinnedX t.tag K γ d, pinnedX_mem_adjointGroup γ d⟩ : adjointGroup t.tag K) =
          wordWeylElement v * xElement k d * (wordWeylElement v)⁻¹ := by
    intro γ k v h d
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordWeylElement]
    rw [pinnedX, pinnedWeyl, h, one_smul]
    rfl
  rw [hdec α j w hα, hdec β _ _ hβ, map_mul, map_mul, map_inv, finiteReeAut_wordWeylElement,
    finiteReeAut_xElement]

end Aut

@[expose] def g2Root12 : Fin G2.tag.rank → ℤ := ![1, 2]

@[expose] def g2Root23 : Fin G2.tag.rank → ℤ := ![2, 3]

theorem pinnedData_g2Root12
    : pinnedData G2.tag g2Root12 = (⟨1, by decide⟩, [0, 1], 1) := by
  have h1 : ¬∃ j, g2Root12 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, g2Root12 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem pinnedData_g2Root23
    : pinnedData G2.tag g2Root23 = (⟨0, by decide⟩, [1, 0], 1) := by
  have h1 : ¬∃ j, g2Root23 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, g2Root23 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem g2_root_positions :
    G2.tag.rootCertificate.root 0 = Pi.single ⟨0, by decide⟩ 1 ∧
    G2.tag.rootCertificate.root 1 = Pi.single ⟨1, by decide⟩ 1 ∧
    G2.tag.rootCertificate.root 2 = -Pi.single ⟨0, by decide⟩ 1 ∧
    G2.tag.rootCertificate.root 5 = -Pi.single ⟨1, by decide⟩ 1 ∧
    G2.tag.rootCertificate.root 3 = g2Root13 ∧ G2.tag.rootCertificate.root 4 = g2Root11 ∧
    G2.tag.rootCertificate.root 7 = g2Root23 ∧ G2.tag.rootCertificate.root 8 = g2Root12 ∧
    G2.tag.rootCertificate.root 6 = -g2Root13 ∧ G2.tag.rootCertificate.root 9 = -g2Root11 ∧
    G2.tag.rootCertificate.root 10 = -g2Root23 ∧ G2.tag.rootCertificate.root 11 = -g2Root12 := by
  decide

@[expose] def g2WeylWord (i : Fin G2.tag.rank) : List (ℕ × ℤ) :=
  if i.val = 0 then [(0, 1), (2, -1), (0, 1)] else [(1, 1), (5, -1), (1, 1)]

@[expose] def g2WeylWordInv (i : Fin G2.tag.rank) : List (ℕ × ℤ) :=
  if i.val = 0 then [(0, -1), (2, 1), (0, -1)] else [(1, -1), (5, 1), (1, -1)]

@[expose] def g2LongWord : List (ℕ × ℤ) :=
  (G2.fixedOrbitWord ⟨0, by decide⟩).flatMap g2WeylWord

@[expose] def g2LongWordInv : List (ℕ × ℤ) :=
  (G2.fixedOrbitWord ⟨0, by decide⟩).reverse.flatMap g2WeylWordInv

@[expose] def g2UWord : Fin 3 → List (ℕ × ℤ) :=
  ![[(8, 1), (7, 1)], [(4, 1), (3, 1)], [(1, 1), (0, 1), (3, -1), (7, -1)]]

@[expose] def g2VWord : Fin 3 → List (ℕ × ℤ) :=
  ![[(11, 1), (10, 1)], [(9, 1), (6, 1)], [(5, -1), (2, -1), (6, -1), (10, -1)]]

theorem g2Check_v0 :
    constCheck G2.tag 3 (g2LongWord ++ g2UWord 0 ++ g2LongWordInv) (g2VWord 0) = true := by
  decide +kernel

theorem g2Check_v1 :
    constCheck G2.tag 3 (g2LongWord ++ g2UWord 1 ++ g2LongWordInv) (g2VWord 1) = true := by
  decide +kernel

theorem g2Check_v2 :
    constCheck G2.tag 3 (g2LongWord ++ g2UWord 2 ++ g2LongWordInv) (g2VWord 2) = true := by
  decide +kernel

theorem g2Check_torus :
    constCheck G2.tag 3 (g2WeylWordInv ⟨0, by decide⟩ ++ g2WeylWordInv ⟨0, by decide⟩ ++
      g2WeylWordInv ⟨1, by decide⟩ ++ g2WeylWordInv ⟨1, by decide⟩)
      (g2UWord 0 ++ g2VWord 0 ++ g2VWord 0 ++ g2VWord 1 ++ g2UWord 2 ++ g2VWord 1) = true := by
  decide +kernel

theorem g2Check_long :
    constCheck G2.tag 3 g2LongWord (g2UWord 1 ++ g2VWord 1 ++ g2UWord 1) = true := by
  decide +kernel

theorem g2Check_u2 :
    constCheck G2.tag 3 [(0, 1), (1, 1), (4, -1), (8, -1)] (g2UWord 2) = true := by
  decide +kernel

section Elements

variable (R : Type*) [CommRing R]

@[expose] def g2U₀
    : (Module.End R (RootModule G2.tag R))ˣ :=
  pinnedX G2.tag R g2Root12 1 * pinnedX G2.tag R g2Root23 1

@[expose] def g2U₁
    : (Module.End R (RootModule G2.tag R))ˣ :=
  pinnedX G2.tag R g2Root11 1 * pinnedX G2.tag R g2Root13 1

@[expose] def g2U₂
    : (Module.End R (RootModule G2.tag R))ˣ :=
  xUnit G2.tag R ⟨1, by decide⟩ 1 * xUnit G2.tag R ⟨0, by decide⟩ 1 *
    pinnedX G2.tag R g2Root13 (-1) * pinnedX G2.tag R g2Root23 (-1)

theorem g2U_eq_constPinned :
    g2U₀ R = constPinned G2.tag R (g2UWord 0) ∧ g2U₁ R = constPinned G2.tag R (g2UWord 1) ∧
      g2U₂ R = constPinned G2.tag R (g2UWord 2) := by
  obtain ⟨h0, h1, -, -, h3, h4, h7, h8, -⟩ := g2_root_positions
  refine ⟨?_, ?_, ?_⟩
  · simp only [g2UWord, constPinned, Matrix.cons_val_zero, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Int.cast_one, h7, h8, g2U₀]
  · simp only [g2UWord, constPinned, Matrix.cons_val_one, Matrix.cons_val_zero, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, Int.cast_one, h3, h4, g2U₁]
  · simp only [g2UWord, constPinned, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Int.cast_one,
      Int.cast_neg, h0, h1, h3, h7, g2U₂, pinnedX_single, mul_assoc]

theorem weylElt_eq_constPinned
    (i : Fin G2.tag.rank) :
    weylElt G2.tag R i 1 = constPinned G2.tag R (g2WeylWord i) := by
  obtain ⟨h0, h1, h2, h5, -⟩ := g2_root_positions
  rw [weylElt_eq_xUnit_mul]
  rcases i with ⟨_ | _ | i, hi⟩
  · simp [g2WeylWord, constPinned, h0, h2, pinnedX_single, pinnedX_neg_single, mul_assoc]
  · simp [g2WeylWord, constPinned, h1, h5, pinnedX_single, pinnedX_neg_single, mul_assoc]
  · exact absurd hi (by change ¬ (_ < 2); omega)

theorem weylElt_neg_one_eq_constPinned
    (i : Fin G2.tag.rank) :
    weylElt G2.tag R i (-1) = constPinned G2.tag R (g2WeylWordInv i) := by
  obtain ⟨h0, h1, h2, h5, -⟩ := g2_root_positions
  rw [weylElt_eq_xUnit_mul]
  rcases i with ⟨_ | _ | i, hi⟩
  · simp [g2WeylWordInv, constPinned, h0, h2, pinnedX_single, pinnedX_neg_single, mul_assoc]
  · simp [g2WeylWordInv, constPinned, h1, h5, pinnedX_single, pinnedX_neg_single, mul_assoc]
  · exact absurd hi (by change ¬ (_ < 2); omega)

end Elements

section Long

variable {K : Type} [Field K]

theorem longest_eq_fixedOrbitElement
    {w₀ : WeylGroup G2.tag}
    (h : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    w₀ = G2.fixedOrbitElement ⟨0, by decide⟩ := by
  have hneg : ReversesSigns G2.negOne := fun α _ hpos => by
    rw [negOne_smul, height_neg]
    omega
  exact (reversesSigns_of_forall_length_le h).eq hneg

theorem isReduced_g2Long :
    (coxeterSystem G2.tag).IsReduced (G2.fixedOrbitWord ⟨0, by decide⟩) := by
  have h := length_fixedOrbitElement (t := G2) ⟨0, by decide⟩
  rw [ncard_fixedOrbitRoots] at h
  exact h

theorem prod_weylElt_eq_constPinned
    (W : List (Fin G2.tag.rank)) :
    (W.map fun i => weylElt G2.tag K i 1).prod = constPinned G2.tag K (W.flatMap g2WeylWord) := by
  induction W with
  | nil => rfl
  | cons i W ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, constPinned_append, ih,
      weylElt_eq_constPinned]

theorem prod_weylElt_inv_eq_constPinned
    (W : List (Fin G2.tag.rank)) :
    ((W.map fun i => weylElt G2.tag K i 1).prod)⁻¹ =
      constPinned G2.tag K (W.reverse.flatMap g2WeylWordInv) := by
  induction W with
  | nil => rfl
  | cons i W ih =>
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, List.reverse_cons, List.flatMap_append,
      constPinned_append, weylElt_inv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      weylElt_neg_one_eq_constPinned]

theorem canonicalRep_longest
    {w₀ : WeylGroup G2.tag}
    (h : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    canonicalRep (coxeterSystem G2.tag) K w₀ = constPinned G2.tag K g2LongWord := by
  rw [longest_eq_fixedOrbitElement h, fixedOrbitElement, canonicalRep_wordProd isReduced_g2Long,
    prod_weylElt_eq_constPinned]
  rfl

theorem canonicalRep_longest_inv
    {w₀ : WeylGroup G2.tag}
    (h : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ = constPinned G2.tag K g2LongWordInv := by
  rw [longest_eq_fixedOrbitElement h, fixedOrbitElement, canonicalRep_wordProd isReduced_g2Long,
    prod_weylElt_inv_eq_constPinned]
  rfl

end Long

section Fixed

variable (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ)

omit [Finite K] in
theorem g2_three_eq_zero : ((3 : ℕ) : K) = 0 :=
  CharP.cast_eq_zero K G2.prime

theorem g2U₀_mem_reeGamma :
    g2U₀ K ∈ G2.reeGamma K a := by
  have hc : Commute (pinnedX G2.tag K g2Root12 1) (pinnedX G2.tag K g2Root23 1) := by
    have hr12 : RootOps.isRootB G2.tag g2Root12 = true := by decide +kernel
    have hr23 : RootOps.isRootB G2.tag g2Root23 = true := by decide +kernel
    have hnr : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
        RootOps.isRootB G2.tag (a • g2Root12 + b • g2Root23) = false := by
      decide +kernel
    exact commute_pinnedX_of_not_isRoot K (RootOps.isRootB_iff.1 hr12)
      (RootOps.isRootB_iff.1 hr23) (by decide) (by decide) (by decide)
      (forall_not_isRoot_of_check (k := ⟨0, by decide⟩) (l := ⟨0, by decide⟩) (by decide)
        (by decide) (by decide) (by decide) hnr) 1 1
  have h1 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root23) pinnedData_g2Root12
    (by rw [pinnedData_g2Root23]; rfl) 1
  have h2 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root12) pinnedData_g2Root23
    (by rw [pinnedData_g2Root12]; rfl) 1
  rw [one_pow] at h1 h2
  have h := mem_reeGamma_mul h1 h2 hc
  rw [g2U₀]
  exact h

theorem g2U₁_mem_reeGamma :
    g2U₁ K ∈ G2.reeGamma K a :=
  ((g2_fixedBlock K a).1).2

theorem g2U₂_mem_reeGamma :
    g2U₂ K ∈ G2.reeGamma K a := by
  have hneg : ∀ i : Fin G2.tag.rank, (-1 : K) ^ G2.relationExponent a i = -1 :=
    fun i => neg_one_pow_relationExponent a i
  set x2 : adjointGroup G2.tag K := xElement ⟨1, by decide⟩ 1
  set x1 : adjointGroup G2.tag K := xElement ⟨0, by decide⟩ 1
  set y13 : adjointGroup G2.tag K := ⟨pinnedX G2.tag K g2Root13 (-1), pinnedX_mem_adjointGroup _ _⟩
  set y23 : adjointGroup G2.tag K := ⟨pinnedX G2.tag K g2Root23 (-1), pinnedX_mem_adjointGroup _ _⟩
  have hu : g2U₂ K = ((x2 * x1 * y13 * y23 : adjointGroup G2.tag K) : ModGL G2.tag K) := rfl
  have hF : G2.finiteReeAut K a (x2 * x1 * y13 * y23) = x2 * x1 * y13 * y23 := by
    have e2 : G2.finiteReeAut K a x2 = xElement ⟨0, by decide⟩ 1 := by
      rw [finiteReeAut_xElement, one_pow]
      rfl
    have e1 : G2.finiteReeAut K a x1 = xElement ⟨1, by decide⟩ 1 := by
      rw [finiteReeAut_xElement, one_pow]
      rfl
    have e13 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root11) pinnedData_g2Root13
      (by rw [pinnedData_g2Root11]; rfl) (-1)
    have e23 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root12) pinnedData_g2Root23
      (by rw [pinnedData_g2Root12]; rfl) (-1)
    rw [hneg] at e13 e23
    rw [map_mul, map_mul, map_mul, e2, e1, e13, e23]
    refine Subtype.ext ?_
    have hchk := constPinned_eq_of_constCheck g2Check_u2 K (g2_three_eq_zero K)
    obtain ⟨h0, h1, -, -, h3, h4, h7, h8, -⟩ := g2_root_positions
    simp only [constPinned, g2UWord, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Int.cast_one,
      Int.cast_neg, h0, h1, h3, h4, h7, h8, pinnedX_single] at hchk
    simp only [Subgroup.coe_mul, x1, x2, y13, y23, xElement, mul_assoc]
    exact hchk
  rw [hu]
  exact mem_reeGamma.2 ⟨_, hF⟩

end Fixed

theorem g2Words_signs : (∀ i : Fin 3, ∀ f ∈ g2UWord i,
      RootOps.isRootB G2.tag (G2.tag.rootCertificate.root f.1) = true ∧
        0 < height (G2.tag.rootCertificate.root f.1)) ∧
    ∀ i : Fin 3, ∀ f ∈ g2VWord i,
      RootOps.isRootB G2.tag (G2.tag.rootCertificate.root f.1) = true ∧
        height (G2.tag.rootCertificate.root f.1) < 0 := by
  decide +kernel

theorem constPinned_mem_rootSpan
    {τ : Tag} {R : Type*} [CommRing R] {S : Set (Fin τ.rank → ℤ)}
    {fs : List (ℕ × ℤ)} (h : ∀ f ∈ fs, τ.rootCertificate.root f.1 ∈ S) :
    constPinned τ R fs ∈ rootSpan τ R S :=
  list_prod_mem fun x hx => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    exact (le_iSup₂_of_le _ (h f hf) le_rfl : rootSubgroup τ R _ ≤ rootSpan τ R S)
      (Subgroup.subset_closure ⟨_, rfl⟩)

theorem g2UWord_mem_posUnipotent
    (R : Type*) [CommRing R] (i : Fin 3) :
    constPinned G2.tag R (g2UWord i) ∈ posUnipotent G2.tag R :=
  constPinned_mem_rootSpan fun f hf =>
    ⟨RootOps.isRootB_iff.1 (g2Words_signs.1 i f hf).1, (g2Words_signs.1 i f hf).2⟩

theorem g2VWord_mem_negUnipotent
    (R : Type*) [CommRing R] (i : Fin 3) :
    constPinned G2.tag R (g2VWord i) ∈ negUnipotent G2.tag R :=
  constPinned_mem_rootSpan fun f hf =>
    ⟨RootOps.isRootB_iff.1 (g2Words_signs.2 i f hf).1, (g2Words_signs.2 i f hf).2⟩

theorem ree_G2_prime_field_words
    (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ)
    {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    (g2U₀ K ∈ G2.reeFixedPosUnipotent K a ∧ g2U₁ K ∈ G2.reeFixedPosUnipotent K a ∧
      g2U₂ K ∈ G2.reeFixedPosUnipotent K a) ∧
    (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a ∧
      canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a ∧
      canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₂ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a) ∧
    torusElt G2.tag K ⟨0, by decide⟩ (-1) * torusElt G2.tag K ⟨1, by decide⟩ (-1) =
      g2U₀ K * (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) * g2U₂ K *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) ∧
    canonicalRep (coxeterSystem G2.tag) K w₀ =
      g2U₁ K * (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) * g2U₁ K := by
  have h3 := g2_three_eq_zero K
  obtain ⟨hu0, hu1, hu2⟩ := g2U_eq_constPinned K
  have hn := canonicalRep_longest (K := K) hw₀
  have hni := canonicalRep_longest_inv (K := K) hw₀
  have hnΓ : canonicalRep (coxeterSystem G2.tag) K w₀ ∈ G2.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial G2 K a (longest_mem_relWeylRee hw₀)).2
  have hv : ∀ (i : Fin 3) (u : (Module.End K (RootModule G2.tag K))ˣ),
      u = constPinned G2.tag K (g2UWord i) →
      constCheck G2.tag 3 (g2LongWord ++ g2UWord i ++ g2LongWordInv) (g2VWord i) = true →
        canonicalRep (coxeterSystem G2.tag) K w₀ * u *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ = constPinned G2.tag K (g2VWord i) := by
    intro i u hu hc
    rw [hu, hni, hn, ← constPinned_append, ← constPinned_append]
    exact constPinned_eq_of_constCheck hc K h3
  have hv0 := hv 0 _ hu0 g2Check_v0
  have hv1 := hv 1 _ hu1 g2Check_v1
  have hv2 := hv 2 _ hu2 g2Check_v2
  have hneg : ∀ (i : Fin 3) (u : (Module.End K (RootModule G2.tag K))ˣ), u ∈ G2.reeGamma K a →
      canonicalRep (coxeterSystem G2.tag) K w₀ * u *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ = constPinned G2.tag K (g2VWord i) →
        canonicalRep (coxeterSystem G2.tag) K w₀ * u *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a :=
    fun i u huΓ h => Subgroup.mem_inf.2 ⟨h ▸ g2VWord_mem_negUnipotent K i,
      mul_mem (mul_mem hnΓ huΓ) (inv_mem hnΓ)⟩
  refine ⟨⟨Subgroup.mem_inf.2 ⟨hu0 ▸ g2UWord_mem_posUnipotent K 0, g2U₀_mem_reeGamma K a⟩,
      Subgroup.mem_inf.2 ⟨hu1 ▸ g2UWord_mem_posUnipotent K 1, g2U₁_mem_reeGamma K a⟩,
      Subgroup.mem_inf.2 ⟨hu2 ▸ g2UWord_mem_posUnipotent K 2, g2U₂_mem_reeGamma K a⟩⟩,
    ⟨hneg 0 _ (g2U₀_mem_reeGamma K a) hv0, hneg 1 _ (g2U₁_mem_reeGamma K a) hv1,
      hneg 2 _ (g2U₂_mem_reeGamma K a) hv2⟩, ?_, ?_⟩
  · rw [hv0, hv1, hu0, hu2]
    have hd : ∀ i : Fin G2.tag.rank, torusElt G2.tag K i (-1) =
        constPinned G2.tag K (g2WeylWordInv i ++ g2WeylWordInv i) := fun i => by
      rw [constPinned_append, ← weylElt_neg_one_eq_constPinned]
      rfl
    rw [hd, hd, ← constPinned_append, ← constPinned_append, ← constPinned_append,
      ← constPinned_append, ← constPinned_append, ← constPinned_append]
    simp only [List.append_assoc]
    have h := constPinned_eq_of_constCheck g2Check_torus K h3
    simp only [List.append_assoc] at h
    exact h
  · rw [hv1, hu1, hn, ← constPinned_append, ← constPinned_append]
    exact constPinned_eq_of_constCheck g2Check_long K h3

end ReeTag

end CFSG.LieType.Ree
