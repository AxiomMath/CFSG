module

public import CFSG.LieType.Multipliers.L34Model
public import CFSG.LieType.Multipliers.KernelStructure
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.Multipliers.L34

open Matrix Subgroup CFSG.Fischer CFSG.CosetTable
open scoped commutatorElement

abbrev Cover : Type := PG 2 coverWs

theorem coverRelators_subset :
    coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (coverPairs i))) ⊆
      wordSet coverWs := by
  rw [coverRelators_wordSet]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map_of_mem (List.mem_append_left _ hw)

theorem lift_genSL_coverWs
    : ∀ r ∈ wordSet coverWs, FreeGroup.lift genSL r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have h := coverWs_eq_one
  rw [List.all_eq_true] at h
  exact lift_genSL_eq_one (of_decide_eq_true (h w hw))

@[expose] noncomputable def pSL
    : Cover →* SL3 := PresentedGroup.toGroup lift_genSL_coverWs

noncomputable def piX : Cover →* PSL3 := toPSL.comp pSL

theorem pSL_mk
    (f : FreeGroup (Fin 2)) : pSL (PresentedGroup.mk _ f) = FreeGroup.lift genSL f :=
  rfl

theorem piX_mk
    (f : FreeGroup (Fin 2)) : piX (PresentedGroup.mk _ f) = FreeGroup.lift genX f := by
  rw [lift_genX]
  rfl

theorem pSL_surjective : Function.Surjective pSL := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_genSL, closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩

theorem piX_surjective : Function.Surjective piX :=
  toPSL_surjective.comp pSL_surjective

theorem finite_card_cover_le
    : Finite Cover ∧ Nat.card Cover ≤ 967680 := by
  obtain ⟨hfi, hle⟩ := restrict_card_le
  obtain ⟨hfin, hcard⟩ := card_le_of_genSub_index coverWs (subsetOf 2 [1])
    cover_index_walks.1 cover_index_walks.2.1
  exact ⟨hfin, hcard.trans (by omega)⟩

instance : Finite Cover := finite_card_cover_le.1

private theorem map_mem_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) {x : G}
    (hx : x ∈ commutator G) : f x ∈ commutator H := by
  have h := mem_map_of_mem f hx
  rw [map_commutator_eq] at h
  rw [_root_.commutator_def]
  exact commutator_mono le_top le_top h

theorem commutator_cover : commutator Cover = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
  rintro _ ⟨i, rfl⟩
  have h : (PresentedGroup.of i : Cover) =
      PresentedGroup.mk _ (FreeGroup.mk (commWords (coverPairs i))) :=
    PresentedGroup.mk_eq_mk_of_inv_mul_mem
      (coverRelators_subset (inv_of_mul_mem_coverRelators _ _ i))
  rw [SetLike.mem_coe, h]
  exact map_mem_commutator _ (mk_commWords_mem_commutator _)

theorem mk_mem_center
    {r : FreeGroup (Fin 2)} (hr : r ∈ wordSet rels) :
    PresentedGroup.mk (wordSet coverWs) r ∈ center Cover := by
  rw [← centralizer_univ, ← coe_top, ← PresentedGroup.closure_range_of, centralizer_closure,
    mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h := PresentedGroup.one_of_mem
    (coverRelators_subset (commutator_mem_coverRelators
      (fun i => FreeGroup.mk (commWords (coverPairs i))) i hr))
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem ker_piX_le_center : piX.ker ≤ center Cover := by
  intro x hx
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ x
  have hf : f ∈ normalClosure (wordSet rels) := by
    rw [← isPresentation_genX.ker_lift, MonoidHom.mem_ker, ← piX_mk]
    exact hx
  have hmap : (normalClosure (wordSet rels)).map (PresentedGroup.mk (wordSet coverWs)) ≤
      center Cover := by
    rw [map_normalClosure _ _ (PresentedGroup.mk_surjective _)]
    exact normalClosure_le_normal (by rintro _ ⟨r, hr, rfl⟩; exact mk_mem_center hr)
  exact hmap (mem_map_of_mem _ hf)

theorem ker_pSL_le_ker_piX : pSL.ker ≤ piX.ker := fun x hx => by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [piX, MonoidHom.comp_apply, hx, map_one]

noncomputable def zHat (w : List (Fin 2 × Bool)) : Cover :=
  PresentedGroup.mk _ (FreeGroup.mk w)

theorem zHat_pow
    (w : List (Fin 2 × Bool)) (k : ℕ) : zHat w ^ k = zHat (wpow w k) := by
  rw [zHat, zHat, mk_wpow, map_pow]

theorem zHat_append
    (u v : List (Fin 2 × Bool)) : zHat (u ++ v) = zHat u * zHat v := by
  rw [zHat, zHat, zHat, ← FreeGroup.mul_mk, map_mul]

theorem zHat_eq_one
    {w : List (Fin 2 × Bool)} (h : w ∈ coverWs) : zHat w = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem h)

theorem zHat_ne_one
    {u : List (Fin 2 × Bool)} {ℓ : ℕ} (hmem : (u, ℓ) ∈ walkWords) (hℓ : 1 < ℓ) :
    zHat u ≠ 1 := by
  intro h
  have hd := cover_index_walks.2.2 _ hmem
  change ℓ ∣ orderOf (zHat u) at hd
  rw [h, orderOf_one] at hd
  exact absurd (Nat.le_of_dvd one_pos hd) (by omega)

private theorem mem_extraWs {w : List (Fin 2 × Bool)} (h : w ∈ extraWs) : w ∈ coverWs :=
  List.mem_append_right _ h

theorem zOne_pow : zHat zOne ^ 4 = 1 := by
  rw [zHat_pow]
  exact zHat_eq_one (mem_extraWs (by simp [extraWs]))

theorem zTwo_pow : zHat zTwo ^ 4 = 1 := by
  rw [zHat_pow]
  exact zHat_eq_one (mem_extraWs (by simp [extraWs]))

theorem zThree_pow : zHat zThree ^ 3 = 1 := by
  rw [zHat_pow]
  exact zHat_eq_one (mem_extraWs (by simp [extraWs]))

theorem zOne_sq_ne_one : zHat zOne ^ 2 ≠ 1 := by
  rw [zHat_pow]
  exact zHat_ne_one (ℓ := 2) (by simp only [walkWords, List.mem_cons, true_or]) (by norm_num)

theorem zTwo_sq_ne_one : zHat zTwo ^ 2 ≠ 1 := by
  rw [zHat_pow]
  exact zHat_ne_one (ℓ := 2) (by simp only [walkWords, List.mem_cons, true_or, or_true])
    (by norm_num)

theorem zOne_sq_mul_zTwo_sq_ne_one
    : zHat zOne ^ 2 * zHat zTwo ^ 2 ≠ 1 := by
  rw [zHat_pow, zHat_pow, ← zHat_append]
  exact zHat_ne_one (ℓ := 2) (by simp only [walkWords, List.mem_cons, true_or, or_true])
    (by norm_num)

theorem zThree_ne_one : zHat zThree ≠ 1 :=
  zHat_ne_one (ℓ := 3) (by simp only [walkWords, List.mem_cons, true_or, or_true])
    (by norm_num)

theorem zOne_mem : zHat zOne ∈ pSL.ker := by
  rw [MonoidHom.mem_ker, zHat, pSL_mk]
  exact lift_genSL_eq_one zOne_eq_one

theorem zTwo_mem : zHat zTwo ∈ pSL.ker := by
  rw [MonoidHom.mem_ker, zHat, pSL_mk]
  exact lift_genSL_eq_one zTwo_eq_one

theorem zThree_mem : zHat zThree ∈ piX.ker := by
  rw [MonoidHom.mem_ker, zHat, piX_mk, lift_genX, MonoidHom.comp_apply]
  exact toPSL_eq_one (lift_genSL_mem_center zThree_isScalar)

private theorem commute_of_mem
    {x y : Cover} (hx : x ∈ piX.ker) : Commute x y :=
  (mem_center_iff.mp (ker_piX_le_center hx) y).symm

private theorem card_ker_le
    {Q : Type} [Group Q] (f : Cover →* Q) (hf : Function.Surjective f)
    {m : ℕ} (hm : 967680 ≤ m * Nat.card Q) : Nat.card f.ker ≤ m := by
  have h := f.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  have hQ : 0 < Nat.card Q := Nat.card_pos_iff.mpr ⟨⟨1⟩, Finite.of_surjective f hf⟩
  have := finite_card_cover_le.2
  by_contra hlt
  push Not at hlt
  nlinarith

theorem nonempty_ker_piX_mulEquiv :
    Nonempty (piX.ker ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
      Multiplicative (ZMod 4)) :=
  nonempty_mulEquiv_zmod_three_four_four piX.ker
    (card_ker_le piX piX_surjective (by nlinarith [card_PSL3_ge]))
    (ker_pSL_le_ker_piX zOne_mem) (ker_pSL_le_ker_piX zTwo_mem) zThree_mem
    (commute_of_mem (ker_pSL_le_ker_piX zOne_mem))
    (commute_of_mem zThree_mem) (commute_of_mem zThree_mem) zOne_pow zTwo_pow zThree_pow
    zOne_sq_ne_one zTwo_sq_ne_one zOne_sq_mul_zTwo_sq_ne_one zThree_ne_one

theorem nonempty_ker_pSL_mulEquiv :
    Nonempty (pSL.ker ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
  nonempty_mulEquiv_zmod_four_four pSL.ker
    (card_ker_le pSL pSL_surjective (by rw [card_SL3]))
    zOne_mem zTwo_mem (commute_of_mem (ker_pSL_le_ker_piX zOne_mem)) zOne_pow zTwo_pow
    zOne_sq_ne_one zTwo_sq_ne_one zOne_sq_mul_zTwo_sq_ne_one

private theorem ker_comp_mulEquiv {G Q Q' : Type*} [Group G] [Group Q] [Group Q'] (f : G →* Q)
    (e : Q ≃* Q') : (e.toMonoidHom.comp f).ker = f.ker := by
  ext x
  simp

theorem exists_cover_SL_three_four :
    ∃ (E : Type) (_ : Group E) (_ : Finite E)
      (p : E →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)),
      commutator E = ⊤ ∧ Function.Surjective p ∧ p.ker ≤ center E ∧
        Nonempty (p.ker ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  set e := slEquiv (Fin 3) F4.equivGaloisField
  refine ⟨Cover, inferInstance, inferInstance, e.toMonoidHom.comp pSL, commutator_cover,
    e.surjective.comp pSL_surjective, ?_, ?_⟩
  · rw [ker_comp_mulEquiv]
    exact ker_pSL_le_ker_piX.trans ker_piX_le_center
  · rw [ker_comp_mulEquiv]
    exact nonempty_ker_pSL_mulEquiv

theorem nonempty_mulEquiv_PSL3 {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2)
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) :
    Nonempty (PSL3 ≃* X) := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card F4 = Fintype.card K := by
    rw [F4.card, ← Nat.card_eq_fintype_card, hK]
    norm_num
  exact ⟨((pslEquiv (Fin 3) (FiniteField.ringEquivOfCardEq hc)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)).trans e.symm⟩

theorem exists_cover_of_mulEquiv
    {X : Type} [Group X] (ψ : PSL3 ≃* X) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (f : E →* X),
      commutator E = ⊤ ∧ Function.Surjective f ∧ f.ker ≤ center E ∧
        Nonempty (f.ker ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
          Multiplicative (ZMod 4)) := by
  refine ⟨Cover, inferInstance, inferInstance, ψ.toMonoidHom.comp piX, commutator_cover,
    ψ.surjective.comp piX_surjective, ?_, ?_⟩
  · rw [ker_comp_mulEquiv]
    exact ker_piX_le_center
  · rw [ker_comp_mulEquiv]
    exact nonempty_ker_piX_mulEquiv

theorem exists_cover_of_lieModel (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (f : E →* X),
      commutator E = ⊤ ∧ Function.Surjective f ∧ f.ker ≤ center E ∧
        Nonempty (f.ker ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
          Multiplicative (ZMod 4)) := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨ψ⟩ := nonempty_mulEquiv_PSL3 hK e
    exact exists_cover_of_mulEquiv ψ
  all_goals exact absurd h0 (by norm_num)

theorem exists_cover_of_models_lieModel (X : Type) [Group X]
    (h : CFSG.Models.LieModel X .PSL 3 2 2) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (f : E →* X),
      commutator E = ⊤ ∧ Function.Surjective f ∧ f.ker ≤ center E ∧
        Nonempty (f.ker ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
          Multiplicative (ZMod 4)) := by
  obtain ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩⟩ := h
  · obtain ⟨ψ⟩ := nonempty_mulEquiv_PSL3 hK e
    exact exists_cover_of_mulEquiv ψ
  · exact absurd h0 (by norm_num)

theorem four_four_cover_existence :
    (∃ (E : Type) (_ : Group E) (_ : Finite E)
      (p : E →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)),
      commutator E = ⊤ ∧ Function.Surjective p ∧ p.ker ≤ center E ∧
        Nonempty (p.ker ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
    ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSL 3 2 2 →
      ∃ (E : Type) (_ : Group E) (_ : Finite E) (f : E →* X),
        commutator E = ⊤ ∧ Function.Surjective f ∧ f.ker ≤ center E ∧
          Nonempty (f.ker ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 4) ×
            Multiplicative (ZMod 4)) :=
  ⟨exists_cover_SL_three_four, exists_cover_of_lieModel⟩

end CFSG.LieType.Multipliers.L34
