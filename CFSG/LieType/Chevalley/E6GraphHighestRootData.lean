module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.TwistPerfect

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphHighestRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

abbrev e6Idx (i : Fin 6) : Fin TwistTag.E6.tag.rank := i

@[expose] def sRoot : Fin TwistTag.E6.tag.rank → ℤ := (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)

@[expose] def a5Path : Fin 5 → Fin TwistTag.E6.tag.rank := fun l => e6Idx (![0, 2, 3, 4, 5] l)

@[expose] def a5Interval (i j : Fin 5) : Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ l ∈ Finset.Icc i j, Pi.single (a5Path l) 1

@[expose] def a5Roots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 ≤ p.2).image fun p => a5Interval p.1 p.2) ∪
    ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 ≤ p.2).image fun p => -a5Interval p.1 p.2)

theorem mem_a5Roots {β : Fin TwistTag.E6.tag.rank → ℤ} :
    β ∈ a5Roots ↔ ∃ i j : Fin 5, i ≤ j ∧ (β = a5Interval i j ∨ β = -a5Interval i j) := by
  simp only [a5Roots, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro (⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩)
    exacts [⟨i, j, h, Or.inl rfl⟩, ⟨i, j, h, Or.inr rfl⟩]
  · rintro ⟨i, j, h, rfl | rfl⟩
    exacts [Or.inl ⟨i, j, h, rfl⟩, Or.inr ⟨i, j, h, rfl⟩]

theorem filter_coord_zero :
    (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 0) = a5Roots := by
  decide +kernel

theorem card_a5Roots : a5Roots.card = 30 := by decide +kernel

@[expose] def degOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 1)

theorem card_degOneRoots : degOneRoots.card = 20 := by decide +kernel

theorem filter_coord_two :
    (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 2) = {e6HighestRoot} := by
  decide +kernel

theorem filter_pos_coord_pos :
    (rootFinset TwistTag.E6.tag).filter (fun β => 0 < height β ∧ 0 < β (e6Idx 1)) =
      insert e6HighestRoot degOneRoots := by
  decide +kernel

theorem add_eq_e6HighestRoot : ∀ β ∈ insert e6HighestRoot degOneRoots,
    ∀ β' ∈ insert e6HighestRoot degOneRoots, β + β' ∈ rootFinset TwistTag.E6.tag →
      β + β' = e6HighestRoot := by
  decide +kernel

theorem sub_e6HighestRoot_mem :
    ∀ β ∈ degOneRoots, β - e6HighestRoot ∈ rootFinset TwistTag.E6.tag := by
  decide +kernel

@[expose] def fixedDegOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  degOneRoots.filter (fun β => permLattice TwistTag.E6.perm β = β)

@[expose] def movedDegOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  degOneRoots.filter (fun β => permLattice TwistTag.E6.perm β ≠ β)

theorem card_fixedDegOneRoots : fixedDegOneRoots.card = 8 := by decide +kernel

theorem card_movedDegOneRoots : movedDegOneRoots.card = 12 := by decide +kernel

theorem card_image_pair : (movedDegOneRoots.image fun β =>
    ({β, permLattice TwistTag.E6.perm β} : Finset (Fin TwistTag.E6.tag.rank → ℤ))).card = 6 := by
  decide +kernel

theorem permLattice_mem_degOneRoots : ∀ β ∈ degOneRoots,
    permLattice TwistTag.E6.perm β ∈ degOneRoots := by
  decide +kernel

theorem iform_permLattice :
    ∀ β ∈ movedDegOneRoots, iform β (permLattice TwistTag.E6.perm β) = 0 := by
  decide +kernel

theorem sum_mul_symmetrizedCartan_e6HighestRoot : ∀ j : Fin TwistTag.E6.tag.rank,
    ∑ i, e6HighestRoot i * TwistTag.E6.tag.symmetrizedCartan i j =
      (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) j := by
  decide

theorem iform_e6HighestRoot (l : Fin TwistTag.E6.tag.rank → ℤ) :
    iform e6HighestRoot l = l (e6Idx 1) := by
  have h : iform e6HighestRoot l =
      ∑ j, (∑ i, e6HighestRoot i * TwistTag.E6.tag.symmetrizedCartan i j) * l j := by
    rw [iform, Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [h]
  simp only [sum_mul_symmetrizedCartan_e6HighestRoot, Pi.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[expose] def tailGen
    : Fin 3 → WeylGroup TwistTag.E6.tag :=
  ![simple TwistTag.E6.tag (e6Idx 3),
    simple TwistTag.E6.tag (e6Idx 0) * simple TwistTag.E6.tag (e6Idx 5),
    simple TwistTag.E6.tag (e6Idx 2) * simple TwistTag.E6.tag (e6Idx 4)]

@[expose] def tailAct (b : Fin 3) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  match b with
  | 0 => reflect TwistTag.E6.tag (e6Idx 3) v
  | 1 => reflect TwistTag.E6.tag (e6Idx 0) (reflect TwistTag.E6.tag (e6Idx 5) v)
  | 2 => reflect TwistTag.E6.tag (e6Idx 2) (reflect TwistTag.E6.tag (e6Idx 4) v)

theorem tailGen_smul
    (b : Fin 3) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    tailGen b • v = tailAct b v := by
  fin_cases b <;> simp [tailGen, tailAct, mul_smul]

theorem list_prod_tailGen_smul
    (bw : List (Fin 3)) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (bw.map tailGen).prod • v = bw.foldr tailAct v := by
  induction bw with
  | nil => simp
  | cons b bw ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, tailGen_smul, List.foldr_cons]

@[expose] def tailWeyl
    : Subgroup (WeylGroup TwistTag.E6.tag) :=
  Subgroup.closure (Set.range tailGen)

@[expose] def weylA
    : Subgroup (WeylGroup TwistTag.E6.tag) :=
  Subgroup.closure (simple TwistTag.E6.tag '' {i | i ≠ e6Idx 1})

theorem tailWeyl_le_weylA
    : tailWeyl ≤ weylA := by
  have hs : ∀ i : Fin 6, i ≠ 1 → simple TwistTag.E6.tag (e6Idx i) ∈ weylA := fun i hi =>
    Subgroup.subset_closure ⟨e6Idx i, fun h => hi h, rfl⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨b, rfl⟩
  fin_cases b
  · exact hs 3 (by decide)
  · exact mul_mem (hs 0 (by decide)) (hs 5 (by decide))
  · exact mul_mem (hs 2 (by decide)) (hs 4 (by decide))


@[expose] def fixedBlockWords : List (List (Fin 3)) :=
  [[], [0], [0, 2], [0, 2, 0], [0, 2, 1], [0, 2, 1, 0], [0, 2, 1, 0, 2], [0, 2, 1, 0, 2, 0]]

theorem exists_fixedBlockWord : ∀ β ∈ fixedDegOneRoots, ∃ bw ∈ fixedBlockWords,
    bw.reverse.foldr tailAct (Pi.single (e6Idx 1) 1) = β := by
  decide +kernel

theorem exists_tailWeyl_smul_single
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ fixedDegOneRoots) :
    ∃ w ∈ tailWeyl, w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) = β := by
  obtain ⟨bw, -, hbw⟩ := exists_fixedBlockWord β hβ
  refine ⟨(bw.reverse.map tailGen).prod, Subgroup.list_prod_mem _ fun g hg => ?_, ?_⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨b, rfl⟩
  · rw [list_prod_tailGen_smul, hbw]

theorem tailWeyl_transitive
    {β β' : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ fixedDegOneRoots)
    (hβ' : β' ∈ fixedDegOneRoots) : ∃ w ∈ tailWeyl, w • β = β' := by
  obtain ⟨w, hw, rfl⟩ := exists_tailWeyl_smul_single hβ
  obtain ⟨w', hw', rfl⟩ := exists_tailWeyl_smul_single hβ'
  refine ⟨w' * w⁻¹, mul_mem hw' (inv_mem hw), ?_⟩
  rw [mul_smul, inv_smul_smul]

section Words

variable {K : Type} [Field K]

theorem neg_one_units_of_two (h2 : (2 : K) = 0) : (-1 : Kˣ) = 1 :=
  Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination -h2)

theorem weylElt_mul_canonicalRep_of_two
    {τ : Tag} (h2 : (2 : K) = 0) (i : Fin τ.rank)
    (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [neg_one_units_of_two h2, torusElt_one, one_mul]

@[expose] def wordElt
    (K : Type) [Field K] (ω : List (Fin TwistTag.E6.tag.rank)) :
    ModGL TwistTag.E6.tag K :=
  (ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod

theorem wordElt_eq_canonicalRep
    (h2 : (2 : K) = 0) (ω : List (Fin TwistTag.E6.tag.rank)) :
    wordElt K ω = canonicalRep (coxeterSystem TwistTag.E6.tag) K
      ((coxeterSystem TwistTag.E6.tag).wordProd ω) := by
  induction ω with
  | nil => rw [wordElt, List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil, canonicalRep_one]
  | cons i ω ih =>
    rw [wordElt, List.map_cons, List.prod_cons, ← wordElt, ih, weylElt_mul_canonicalRep_of_two h2,
      CoxeterSystem.wordProd_cons]

theorem wordElt_conj_pinnedX
    (h2 : (2 : K) = 0) (ω : List (Fin TwistTag.E6.tag.rank))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    wordElt K ω * pinnedX TwistTag.E6.tag K β c * (wordElt K ω)⁻¹ =
      pinnedX TwistTag.E6.tag K ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) c := by
  rw [wordElt_eq_canonicalRep h2, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ hβ]

theorem wordElt_mem_adjointGroup
    (ω : List (Fin TwistTag.E6.tag.rank)) :
    wordElt K ω ∈ adjointGroup TwistTag.E6.tag K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem wordElt_mem_graphFixedRootGroup
    (h2 : (2 : K) = 0) {σ : K →+* K}
    {ω : List (Fin TwistTag.E6.tag.rank)}
    (hω : weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd ω) =
      (coxeterSystem TwistTag.E6.tag).wordProd ω) :
    wordElt K ω ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [wordElt_eq_canonicalRep h2]
  exact canonicalRep_mem_graphFixedRootGroup hω

theorem diagramMap_conj_wordElt
    (h2 : (2 : K) = 0) {ω : List (Fin TwistTag.E6.tag.rank)}
    (hω : weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd ω) =
      (coxeterSystem TwistTag.E6.tag).wordProd ω) :
    diagramMap TwistTag.E6 K * wordElt K ω * (diagramMap TwistTag.E6 K)⁻¹ = wordElt K ω := by
  rw [wordElt_eq_canonicalRep h2, ← twistHom_id_eq, twistHom_canonicalRep, hω]

end Words

@[expose] def fusionWord : List (Fin TwistTag.E6.tag.rank) :=
  ([1, 3, 0, 5, 2, 4, 3, 2, 4, 0, 5, 1] : List (Fin 6))

@[expose] def upWord : List (Fin TwistTag.E6.tag.rank) := ([1, 3, 2, 4, 3, 1] : List (Fin 6))

@[expose] def downWord : List (Fin TwistTag.E6.tag.rank) :=
  ([1, 3, 4, 2, 3, 5, 0, 4, 2, 3] : List (Fin 6))

theorem fusionWord_smul_e6HighestRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • e6HighestRoot =
      Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1 := by
  rw [wordProd_smul]
  decide

theorem fusionWord_smul_sRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • sRoot = Pi.single (e6Idx 3) 1 := by
  rw [wordProd_smul]
  decide

theorem upWord_smul_sRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse • sRoot = e6HighestRoot := by
  rw [wordProd_smul]
  decide

theorem downWord_smul_e6HighestRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd downWord.reverse • e6HighestRoot =
      Pi.single (e6Idx 1) 1 := by
  rw [wordProd_smul]
  decide

theorem weylTwist_fusionWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd fusionWord) =
      (coxeterSystem TwistTag.E6.tag).wordProd fusionWord :=
  weylTwist_wordProd_eq (by decide)

theorem weylTwist_upWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse) =
      (coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse :=
  weylTwist_wordProd_eq (by decide)

theorem weylTwist_downWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd downWord.reverse) =
      (coxeterSystem TwistTag.E6.tag).wordProd downWord.reverse :=
  weylTwist_wordProd_eq (by decide)


@[expose] def graphWords : List (List (Fin TwistTag.E6.tag.rank)) :=
  [fusionWord, upWord.reverse, downWord.reverse]

theorem weylTwist_graphWords :
    ∀ ω ∈ graphWords,
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd ω) =
      (coxeterSystem TwistTag.E6.tag).wordProd ω := by
  intro ω hω
  simp only [graphWords, List.mem_cons, List.not_mem_nil, or_false] at hω
  rcases hω with rfl | rfl | rfl
  exacts [weylTwist_fusionWord, weylTwist_upWord, weylTwist_downWord]

theorem two_eq_zero_of_card {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (2 : F) = 0 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hF, ← Nat.sub_add_cancel hn, pow_succ, Nat.mul_mod_left])
  exact two_eq_zero_of_ringChar hF2

theorem conj_commute {K : Type} [Field K] {G : Subgroup (ModGL TwistTag.E6.tag K)} (η : MulAut G)
    (hη : ∀ g : G, (η g : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K * g *
      (diagramMap TwistTag.E6 K)⁻¹) {x : ModGL TwistTag.E6.tag K} (hx : x ∈ G)
    (hPx : diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹ = x) :
    η ⟨x, hx⟩ = ⟨x, hx⟩ ∧ η * MulAut.conj ⟨x, hx⟩ = MulAut.conj ⟨x, hx⟩ * η := by
  have h1 : η ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext (by rw [hη]; exact hPx)
  refine ⟨h1, ?_⟩
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h1]



theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_highest_root_data
    (f : ℕ) (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 0) = a5Roots ∧
    a5Roots.card = 30 ∧
    (∀ β, β ∈ a5Roots ↔ ∃ i j : Fin 5, i ≤ j ∧ (β = a5Interval i j ∨ β = -a5Interval i j)) ∧
    (rootFinset TwistTag.E6.tag).filter (fun β => 0 < height β ∧ 0 < β (e6Idx 1)) =
      insert e6HighestRoot degOneRoots ∧
    degOneRoots.card = 20 ∧
    (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 2) = {e6HighestRoot} ∧
    (∀ β ∈ insert e6HighestRoot degOneRoots, ∀ β' ∈ insert e6HighestRoot degOneRoots,
      IsRoot TwistTag.E6.tag (β + β') → β + β' = e6HighestRoot) ∧
    (∀ β ∈ degOneRoots, IsRoot TwistTag.E6.tag (β - e6HighestRoot)) ∧
    fixedDegOneRoots.card = 8 ∧ movedDegOneRoots.card = 12 ∧
    (∀ β ∈ degOneRoots, permLattice TwistTag.E6.perm β ∈ degOneRoots) ∧
    (∀ β ∈ movedDegOneRoots, iform β (permLattice TwistTag.E6.perm β) = 0) ∧
    (movedDegOneRoots.image fun β =>
      ({β, permLattice TwistTag.E6.perm β} : Finset (Fin TwistTag.E6.tag.rank → ℤ))).card = 6 ∧
    tailWeyl ≤ weylA ∧
    (∀ β ∈ fixedDegOneRoots, ∀ β' ∈ fixedDegOneRoots, ∃ w ∈ tailWeyl, w • β = β') ∧
    (∀ l : Fin TwistTag.E6.tag.rank → ℤ, iform e6HighestRoot l = l (e6Idx 1)) ∧
    (∀ (E : Type) [Field E], (2 : E) = 0 → ∀ (ω : List (Fin TwistTag.E6.tag.rank))
      (β : Fin TwistTag.E6.tag.rank → ℤ), IsRoot TwistTag.E6.tag β → ∀ c : E,
        wordElt E ω * pinnedX TwistTag.E6.tag E β c * (wordElt E ω)⁻¹ =
          pinnedX TwistTag.E6.tag E ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) c) ∧
    (∀ (E : Type) [Field E], (2 : E) = 0 → ∀ β : Fin TwistTag.E6.tag.rank → ℤ,
      IsRoot TwistTag.E6.tag β → ∀ c : E,
        diagramMap TwistTag.E6 E * pinnedX TwistTag.E6.tag E β c * (diagramMap TwistTag.E6 E)⁻¹ =
          pinnedX TwistTag.E6.tag E (permLattice TwistTag.E6.perm β) c) ∧
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • e6HighestRoot =
      Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1 ∧
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • sRoot = Pi.single (e6Idx 3) 1 ∧
    (coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse • sRoot = e6HighestRoot ∧
    (coxeterSystem TwistTag.E6.tag).wordProd downWord.reverse • e6HighestRoot =
      Pi.single (e6Idx 1) 1 ∧
    (∀ ω ∈ graphWords, wordElt k ω ∈ adjointGroup TwistTag.E6.tag k ∧
      diagramMap TwistTag.E6 k * wordElt k ω * (diagramMap TwistTag.E6 k)⁻¹ = wordElt k ω ∧
      wordElt K ω ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      diagramMap TwistTag.E6 K * wordElt K ω * (diagramMap TwistTag.E6 K)⁻¹ = wordElt K ω) ∧
    (∃ η : MulAut (adjointGroup TwistTag.E6.tag k), (∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) ∧ orderOf η = 2) ∧
    (∃ η : MulAut (graphFixedRootGroup TwistTag.E6 K σ), (∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) ∧ orderOf η = 2) ∧
    (∀ η : MulAut (adjointGroup TwistTag.E6.tag k), (∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) →
      ∀ ω ∈ graphWords, ∀ h : wordElt k ω ∈ adjointGroup TwistTag.E6.tag k,
        η ⟨_, h⟩ = ⟨_, h⟩ ∧ η * MulAut.conj ⟨_, h⟩ = MulAut.conj ⟨_, h⟩ * η) ∧
    (∀ η : MulAut (graphFixedRootGroup TwistTag.E6 K σ), (∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) →
      ∀ ω ∈ graphWords, ∀ h : wordElt K ω ∈ graphFixedRootGroup TwistTag.E6 K σ,
        η ⟨_, h⟩ = ⟨_, h⟩ ∧ η * MulAut.conj ⟨_, h⟩ = MulAut.conj ⟨_, h⟩ * η) := by
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card (n := 2 * f) (by omega) (by rw [hK, ← pow_mul,
    mul_comm])
  have hcan := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨η₁, hη₁, hη₁2, -⟩ := hcan.1.1
  obtain ⟨η₂, hη₂, hη₂2, -⟩ := hcan.2.1
  refine ⟨filter_coord_zero, card_a5Roots, fun β => mem_a5Roots, filter_pos_coord_pos,
    card_degOneRoots, filter_coord_two, fun β hβ β' hβ' h => add_eq_e6HighestRoot β hβ β' hβ'
      (mem_rootFinset.2 h), fun β hβ => mem_rootFinset.1 (sub_e6HighestRoot_mem β hβ),
    card_fixedDegOneRoots, card_movedDegOneRoots, permLattice_mem_degOneRoots,
    iform_permLattice, card_image_pair, tailWeyl_le_weylA,
    fun β hβ β' hβ' => tailWeyl_transitive hβ hβ', iform_e6HighestRoot,
    fun E _ h2 ω β hβ c => wordElt_conj_pinnedX h2 ω hβ c,
    fun E _ h2 β hβ c => by rw [← twistHom_id_eq, twistHom_id_pinnedX h2 hβ],
    fusionWord_smul_e6HighestRoot,
    fusionWord_smul_sRoot, upWord_smul_sRoot, downWord_smul_e6HighestRoot,
    fun ω hω => ⟨wordElt_mem_adjointGroup ω,
      diagramMap_conj_wordElt hk2 (weylTwist_graphWords ω hω),
      wordElt_mem_graphFixedRootGroup hK2 (weylTwist_graphWords ω hω),
      diagramMap_conj_wordElt hK2 (weylTwist_graphWords ω hω)⟩,
    ⟨η₁, hη₁, hη₁2⟩, ⟨η₂, hη₂, hη₂2⟩,
    fun η hη ω hω h =>
      conj_commute η hη h (diagramMap_conj_wordElt hk2 (weylTwist_graphWords ω hω)),
    fun η hη ω hω h =>
      conj_commute η hη h (diagramMap_conj_wordElt hK2 (weylTwist_graphWords ω hω))⟩


end CFSG.LieType.Chevalley.E6GraphHighestRoot
