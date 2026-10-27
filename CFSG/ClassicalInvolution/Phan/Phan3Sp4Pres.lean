module

public import CFSG.ClassicalInvolution.Phan.Phan3Sp4Data
public import CFSG.ClassicalInvolution.Phan.Phan3SL3Pres
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdaptModel
public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.Assembly.LowTwoRank CFSG.CosetTable CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z (c2Mat c2Root c2Mat_two c2Mat_three c2Mat_five c2Mat_six
  closure_xp_xm xpS xmS evalCube spMap spMap_injective spMap_surjective spMap_longBlock
  spMap_shortBlock)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt elt_add elt_zero mat mat_injective mat_elt E)
open TauCeti.GLSymplecticFin (RootSubgroupIndex eq_top_of_adjacent_of_long differenceShortRootUnit
  positiveLongRootTransvectionUnit negativeLongRootTransvectionUnit differenceShortRootHom_apply
  positiveLongRootTransvectionHom_apply negativeLongRootTransvectionHom_apply)
open scoped MatrixGroups

@[expose] noncomputable def sp4Gen : Fin 4 → StatedSp 2 (ZMod 3) :=
  fun i => c2Mat (![2, 3, 5, 6] i)

@[expose] noncomputable def sp4N (i : Fin 4) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  1 + (1 : ZMod 3) • E (ZMod 3) (c2Root (![2, 3, 5, 6] i))

theorem mat_sp4Gen (i : Fin 4) : mat 2 (ZMod 3) (sp4Gen i) = sp4N i :=
  mat_elt (c2Root (![2, 3, 5, 6] i)) 1

theorem map_wordVal_cube {G M : Type*} [Group G] [Monoid M] (ρ : G →* M) {m : ℕ} (g : Fin m → G)
    (hg : ∀ i, g i * g i * g i = 1) (w : List (Fin m × Bool)) :
    ρ (wordVal g w) = evalCube (fun i => ρ (g i)) w := by
  induction w with
  | nil => simp [wordVal, evalCube]
  | cons p w ih =>
    simp only [wordVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp only [evalCube, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := p
    cases b
    · have h : (g i)⁻¹ = g i * g i :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hg i)
      simp [letterVal, h]
    · simp [letterVal]

theorem sp4Gen_cube (i : Fin 4) : sp4Gen i * sp4Gen i * sp4Gen i = 1 := by
  apply mat_injective (n := 2) (F := ZMod 3)
  rw [map_mul, map_mul, map_one, mat_sp4Gen]
  revert i
  decide +kernel

theorem wordVal_sp4Gen_rels : ∀ r ∈ sp4Rels, wordVal sp4Gen r = 1 := by
  intro r hr
  apply mat_injective (n := 2) (F := ZMod 3)
  rw [map_wordVal_cube (mat 2 (ZMod 3)) sp4Gen sp4Gen_cube, map_one]
  have h : (fun i => mat 2 (ZMod 3) (sp4Gen i)) = sp4N := funext mat_sp4Gen
  rw [h]
  revert r
  decide +kernel

private theorem elt_mem_of_one_sp4 {n : ℕ} (H : Subgroup (StatedSp n (ZMod 3)))
    (r : RootSubgroupIndex n) (h : elt r (1 : ZMod 3) ∈ H) (c : ZMod 3) : elt r c ∈ H := by
  have hnat : ∀ k : ℕ, elt r (k : ZMod 3) ∈ H := by
    intro k
    induction k with
    | zero => simp [elt_zero]
    | succ k ih => rw [Nat.cast_succ, elt_add]; exact H.mul_mem ih h
  rw [← ZMod.natCast_zmod_val c]
  exact hnat _

private theorem equivStatedSp_difference_sp4 {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (differenceShortRootUnit hij c) = elt (.difference i j hij) c := by
  rw [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]

private theorem equivStatedSp_positiveLong_sp4 {n : ℕ} (i : Fin n) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (positiveLongRootTransvectionUnit i c) = elt (.positiveLong i) c := by
  rw [elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
    toAdd_ofAdd]

private theorem equivStatedSp_negativeLong_sp4 {n : ℕ} (i : Fin n) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (negativeLongRootTransvectionUnit i c) = elt (.negativeLong i) c := by
  rw [elt, RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
    toAdd_ofAdd]

theorem sp4_closure_eq_top : Subgroup.closure (Set.range sp4Gen) = ⊤ := by
  set H := Subgroup.closure (Set.range sp4Gen) with hH
  have hgen : ∀ k : Fin 4, elt (c2Root (![2, 3, 5, 6] k)) (1 : ZMod 3) ∈ H := fun k =>
    Subgroup.subset_closure ⟨k, rfl⟩
  have hT : H.comap (equivStatedSp 2 (ZMod 3)).toMonoidHom = ⊤ := by
    refine eq_top_of_adjacent_of_long _ 1 ?_ ?_ ?_
    · intro i j hij c hadj
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_difference_sp4]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact elt_mem_of_one_sp4 H _ (hgen 2) c
      · exact elt_mem_of_one_sp4 H _ (hgen 3) c
      · exact absurd rfl hij
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_positiveLong_sp4]
      exact elt_mem_of_one_sp4 H _ (hgen 0) c
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_negativeLong_sp4]
      exact elt_mem_of_one_sp4 H _ (hgen 1) c
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp 2 (ZMod 3)).surjective x
  have hy : y ∈ H.comap (equivStatedSp 2 (ZMod 3)).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

theorem card_statedSp_two_zmod_three : Nat.card (StatedSp 2 (ZMod 3)) = 51840 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three

theorem sp4_lift_of_card (h : Finite (PG 4 sp4Rels) ∧ Nat.card (PG 4 sp4Rels) ≤ 51840)
    {X : Type} [Group X] (x : Fin 4 → X) (hx : ∀ r ∈ sp4Rels, wordVal x r = 1) :
    ∃ θ : StatedSp 2 (ZMod 3) →* X, ∀ i, θ (sp4Gen i) = x i := by
  obtain ⟨hfin, hle⟩ := h
  let p : PG 4 sp4Rels →* StatedSp 2 (ZMod 3) := PresentedGroup.toGroup (f := sp4Gen) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_sp4Gen_rels w hw)
  have hp : ∀ i, p (PresentedGroup.of i) = sp4Gen i := fun i => PresentedGroup.toGroup.of _
  have hsurj : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← sp4_closure_eq_top, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hp i⟩
  have hbij : Function.Bijective p := by
    have := hfin
    refine hsurj.bijective_of_nat_card_le ?_
    rw [card_statedSp_two_zmod_three]
    exact hle
  let e : PG 4 sp4Rels ≃* StatedSp 2 (ZMod 3) := MulEquiv.ofBijective p hbij
  let q : PG 4 sp4Rels →* X := PresentedGroup.toGroup (f := x) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact hx w hw)
  refine ⟨q.comp e.symm.toMonoidHom, fun i => ?_⟩
  have : e.symm (sp4Gen i) = PresentedGroup.of i := by
    rw [← hp i]
    exact e.symm_apply_apply (PresentedGroup.of i)
  show q (e.symm (sp4Gen i)) = x i
  rw [this]
  exact PresentedGroup.toGroup.of _

theorem isQuasisimple_sp4_zmod : IsQuasisimple (StatedSp 2 (ZMod 3)) :=
  CFSG.LieType.Universal.Symplectic.isQuasisimple 2 (ZMod 3) (by norm_num)
    (Or.inr (Or.inl ⟨by simp, le_rfl⟩))

theorem sp4Gen_not_comm : ∀ m : Fin 4,
    sp4Gen m * sp4Gen (![1, 0, 3, 2] m) ≠ sp4Gen (![1, 0, 3, 2] m) * sp4Gen m := by
  have key : ∀ m : Fin 4, sp4N m * sp4N (![1, 0, 3, 2] m) ≠ sp4N (![1, 0, 3, 2] m) * sp4N m := by
    decide +kernel
  intro m h
  apply key m
  have h' := congrArg (mat 2 (ZMod 3)) h
  rwa [map_mul, map_mul, mat_sp4Gen, mat_sp4Gen] at h'

theorem sp4Gen_not_central (m : Fin 4) : sp4Gen m ∉ Subgroup.center (StatedSp 2 (ZMod 3)) := by
  intro hc
  exact sp4Gen_not_comm m (Subgroup.mem_center_iff.mp hc (sp4Gen (![1, 0, 3, 2] m))).symm

theorem sp4_ker_le_center {X : Type} [Group X] (θ : StatedSp 2 (ZMod 3) →* X) (m : Fin 4)
    (h1 : θ (sp4Gen m) ≠ 1) : θ.ker ≤ Subgroup.center (StatedSp 2 (ZMod 3)) := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple isQuasisimple_sp4_zmod
    θ.ker with h | h
  · exact h
  · exact absurd (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top (sp4Gen m))) h1

theorem sp4_hom_eq_one_of_gen {X : Type} [Group X] (θ : StatedSp 2 (ZMod 3) →* X) (m : Fin 4)
    (h : θ (sp4Gen m) = 1) : θ = 1 := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple isQuasisimple_sp4_zmod
    θ.ker with h1 | h1
  · exact absurd (h1 (MonoidHom.mem_ker.mpr h)) (sp4Gen_not_central m)
  · exact MonoidHom.ext fun x => MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top x)

section Pair

private theorem slMap_surjective_sp4 {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (m : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map e.toRingHom : SL(m, K) →* SL(m, K')) := by
  intro b
  refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom b, ?_⟩
  apply Subtype.ext
  ext i j
  simp

private theorem range_comp_of_surjective_sp4 {A B C : Type*} [Group A] [Group B] [Group C]
    (g : B →* C) {f : A →* B} (hf : Function.Surjective f) : (g.comp f).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, Subgroup.map_top]

theorem range_longBlock_eq_closure :
    (longBlock (ZMod 3) 2 1).range = Subgroup.closure {sp4Gen 0, sp4Gen 1} := by
  rw [MonoidHom.range_eq_map, ← closure_xp_xm, MonoidHom.map_closure, Set.image_pair,
    ← c2Mat_two, ← c2Mat_three]
  rfl

theorem range_shortBlock_eq_closure :
    (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range =
      Subgroup.closure {sp4Gen 2, sp4Gen 3} := by
  rw [MonoidHom.range_eq_map, ← closure_xp_xm, MonoidHom.map_closure, Set.image_pair,
    ← c2Mat_five, ← c2Mat_six]
  rfl

variable {F : Type} [Field F]

theorem symplecticBlockPair_of_hom (hF : Nat.card F = 3) {X : Type} [Group X]
    (θ : StatedSp 2 (ZMod 3) →* X) (hker : θ.ker ≤ Subgroup.center (StatedSp 2 (ZMod 3)))
    {U V : Subgroup X} (hU : Subgroup.closure {θ (sp4Gen 0), θ (sp4Gen 1)} = U)
    (hV : Subgroup.closure {θ (sp4Gen 2), θ (sp4Gen 3)} = V) :
    ∃ W, SymplecticBlockPair F W U V := by
  let e : ZMod 3 ≃+* F := zmodEquiv hF
  let φ : StatedSp 2 F →* StatedSp 2 (ZMod 3) := spMap e.symm.toRingHom
  let θF : StatedSp 2 F →* X := θ.comp φ
  have hφinj : Function.Injective φ := spMap_injective _
  have hkerF : θF.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : φ x ∈ θ.ker := hx
    have h2 := Subgroup.mem_center_iff.mp (hker h1) (φ y)
    apply hφinj
    rw [map_mul, map_mul]
    exact h2
  have hconj : ∀ H : Subgroup (StatedSp 2 F),
      H.map (MulAut.conj (1 : StatedSp 2 F)⁻¹).toMonoidHom = H := by
    intro H
    ext x
    simp
  have cL : θF.comp (longBlock F 2 1) =
      (θ.comp (longBlock (ZMod 3) 2 1)).comp
        (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(2, F) →* SL(2, ZMod 3)) := by
    ext A
    exact congrArg θ (spMap_longBlock e.symm.toRingHom 1 A)
  have cS : θF.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (θ.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))).comp
        (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(2, F) →* SL(2, ZMod 3)) := by
    ext A
    exact congrArg θ (spMap_shortBlock e.symm.toRingHom zero_ne_one A)
  refine ⟨θF.range, θF, 1, rfl, hkerF, ?_, ?_, ?_⟩
  · have := injective_comp_conj_longBlock (le_refl 2) θF hkerF ((1 : StatedSp 2 F)⁻¹) 1
    rwa [MonoidHom.comp_assoc] at this
  · rw [hconj, ← MonoidHom.range_comp, cL,
      range_comp_of_surjective_sp4 _ (slMap_surjective_sp4 e.symm 2), MonoidHom.range_comp,
      range_longBlock_eq_closure, MonoidHom.map_closure, Set.image_pair]
    exact hU
  · rw [hconj, ← MonoidHom.range_comp, cS,
      range_comp_of_surjective_sp4 _ (slMap_surjective_sp4 e.symm 2), MonoidHom.range_comp,
      range_shortBlock_eq_closure, MonoidHom.map_closure, Set.image_pair]
    exact hV

end Pair

end CFSG.ClassicalInvolution.Phan.Q3G
