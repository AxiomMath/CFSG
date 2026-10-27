module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVLeviFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)
open scoped Matrix

local instance e7ClassVF3WedgeNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def vWedgePairs : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

@[expose] def vWedgeBase : Fin Tag.E7.rank → ℤ := ![0, 1, 0, 1, 1, 1, 1]

@[expose] def vWedgeRoot (k l : Fin 6) : Fin Tag.E7.rank → ℤ :=
  vWedgeBase + e7A5Root 0 k + e7A5Root 1 l

@[expose] def vWedgeRoots : List (Fin Tag.E7.rank → ℤ) :=
  vWedgePairs.map fun p => vWedgeRoot p.1 p.2

@[expose] def IsVWedge (β : Fin Tag.E7.rank → ℤ) : Prop := β 1 = 1 ∧ β 6 = 1

instance (β : Fin Tag.E7.rank → ℤ) : Decidable (IsVWedge β) := by
  unfold IsVWedge
  infer_instance

theorem vWedgeRoots_check : vWedgeRoots.Nodup ∧
    (∀ β ∈ vWedgeRoots, isRootB .E7 β = true ∧ 0 < height β ∧ IsVWedge β) ∧
    (∀ k l : Fin 6, vWedgeRoot k l = vWedgeRoot l k) ∧
    (∀ k l : Fin 6, k < l ↔ (k, l) ∈ vWedgePairs) := by
  decide +kernel

theorem vWedgeRoots_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    IsVWedge (Tag.E7.rootCertificate.root k) → Tag.E7.rootCertificate.root k ∈ vWedgeRoots := by
  decide +kernel

theorem vWedgeRoot_sub_check : ∀ p ∈ vWedgePairs, ∀ i j : Fin 6, i ≠ j →
    (p.1 = j ∧ p.2 ≠ i → vWedgeRoot p.1 p.2 - e7A5Root i j = vWedgeRoot i p.2) ∧
    (p.2 = j ∧ p.1 ≠ i → vWedgeRoot p.1 p.2 - e7A5Root i j = vWedgeRoot p.1 i) ∧
    (¬(p.1 = j ∧ p.2 ≠ i) → ¬(p.2 = j ∧ p.1 ≠ i) →
      vWedgeRoot p.1 p.2 - e7A5Root i j ∉ vWedgeRoots) := by
  decide +kernel

theorem vWedgePairs_filter_check : ∀ p ∈ vWedgePairs,
    vWedgePairs.filter (fun q => vWedgeRoot q.1 q.2 = vWedgeRoot p.1 p.2) = [p] := by
  decide +kernel

theorem vGamma_e7A5_check : ∀ i j : Fin 6, i ≠ j →
    isRootB .E7 (e7A5Root i j + vγ) = false ∧ e7A5Root i j ≠ -vγ := by
  decide +kernel

theorem vWedgeFrame_check :
    (∀ p ∈ vWedgePairs, (vWedgeRoot p.1 p.2 ∈ [vθ, vφ, vψ] ↔ (p.1 : ℕ) + p.2 = 5)) ∧
      vWedgeRoots.filter (· ∈ [vθ, vφ, vψ]) = [vθ, vφ, vψ] := by
  decide +kernel

theorem vWedgeRoots_nodup : vWedgeRoots.Nodup := vWedgeRoots_check.1

theorem mem_vWedgePairs_iff {k l : Fin 6} : (k, l) ∈ vWedgePairs ↔ k < l :=
  (vWedgeRoots_check.2.2.2 k l).symm

theorem lt_of_mem_vWedgePairs {p : Fin 6 × Fin 6} (hp : p ∈ vWedgePairs) : p.1 < p.2 :=
  mem_vWedgePairs_iff.1 hp

theorem vWedgeRoot_comm (k l : Fin 6) : vWedgeRoot k l = vWedgeRoot l k :=
  vWedgeRoots_check.2.2.1 k l

theorem vWedgeRoot_mem_vWedgeRoots {a b : Fin 6} (hab : a ≠ b) : vWedgeRoot a b ∈ vWedgeRoots := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact List.mem_map_of_mem (f := fun p : Fin 6 × Fin 6 => vWedgeRoot p.1 p.2)
      (mem_vWedgePairs_iff.2 h)
  · rw [vWedgeRoot_comm]
    exact List.mem_map_of_mem (f := fun p : Fin 6 × Fin 6 => vWedgeRoot p.1 p.2)
      (mem_vWedgePairs_iff.2 h)

theorem vLevel_of_mem_vWedgeRoots {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vWedgeRoots) :
    vLevel β = 2 := by
  obtain ⟨h1, h6⟩ := (vWedgeRoots_check.2.1 β hβ).2.2
  simp only [vLevel, h1, h6]
  rfl


theorem isRoot_of_mem_vWedgeRoots {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vWedgeRoots) :
    IsRoot .E7 β :=
  isRootB_iff.1 (vWedgeRoots_check.2.1 β hβ).1

theorem pos_of_mem_vWedgeRoots {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vWedgeRoots) :
    IsRoot .E7 β ∧ 0 < height β :=
  ⟨isRoot_of_mem_vWedgeRoots hβ, (vWedgeRoots_check.2.1 β hβ).2.1⟩

theorem mem_vPsi_of_mem_vWedgeRoots {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vWedgeRoots) :
    β ∈ vPsi :=
  mem_vPsi_of_level (isRoot_of_mem_vWedgeRoots hβ) (vLevel_of_mem_vWedgeRoots hβ).ge

theorem mem_vWedgeRoots_of_isRoot {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot .E7 β)
    (h : IsVWedge β) : β ∈ vWedgeRoots := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβ
  exact vWedgeRoots_complete_check k hk h

variable {K : Type} [Field K]


@[expose] noncomputable def vWedgeCoeff (A : Matrix (Fin 6) (Fin 6) K)
    (β : Fin Tag.E7.rank → ℤ) : K :=
  ((vWedgePairs.filter fun q => vWedgeRoot q.1 q.2 = β).map fun q => A q.1 q.2).sum

theorem vWedgeCoeff_vWedgeRoot (A : Matrix (Fin 6) (Fin 6) K) {p : Fin 6 × Fin 6}
    (hp : p ∈ vWedgePairs) : vWedgeCoeff A (vWedgeRoot p.1 p.2) = A p.1 p.2 := by
  rw [vWedgeCoeff, vWedgePairs_filter_check p hp]
  simp

theorem vWedgeCoeff_vWedgeRoot_of_ne {A : Matrix (Fin 6) (Fin 6) K} (hA : Aᵀ = A) {a b : Fin 6}
    (hab : a ≠ b) : vWedgeCoeff A (vWedgeRoot a b) = A a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact vWedgeCoeff_vWedgeRoot A (p := (a, b)) (mem_vWedgePairs_iff.2 h)
  · rw [vWedgeRoot_comm, vWedgeCoeff_vWedgeRoot A (p := (b, a)) (mem_vWedgePairs_iff.2 h)]
    show A b a = A a b
    conv_rhs => rw [← hA]
    rfl

variable (K) in
@[expose] noncomputable def vWedgeElt (A : Matrix (Fin 6) (Fin 6) K) : ModGL .E7 K :=
  rootProd .E7 K vWedgeRoots (vWedgeCoeff A)

theorem eq_of_vWedgeElt_eq {A A' : Matrix (Fin 6) (Fin 6) K} (h : vWedgeElt K A = vWedgeElt K A')
    {p : Fin 6 × Fin 6} (hp : p ∈ vWedgePairs) : A p.1 p.2 = A' p.1 p.2 := by
  have := E6Pilot.rootProd_injective vWedgeRoots_nodup (fun _ hρ => pos_of_mem_vWedgeRoots hρ) h
    (vWedgeRoot p.1 p.2) (List.mem_map_of_mem (f := fun q : Fin 6 × Fin 6 => vWedgeRoot q.1 q.2) hp)
  rwa [vWedgeCoeff_vWedgeRoot _ hp, vWedgeCoeff_vWedgeRoot _ hp] at this

theorem eq_of_forall_vWedgePairs {A A' : Matrix (Fin 6) (Fin 6) K} (hA : Aᵀ = A)
    (hA0 : ∀ k, A k k = 0) (hA' : A'ᵀ = A') (hA0' : ∀ k, A' k k = 0)
    (h : ∀ p ∈ vWedgePairs, A p.1 p.2 = A' p.1 p.2) : A = A' := by
  have s : ∀ M : Matrix (Fin 6) (Fin 6) K, Mᵀ = M → ∀ a b, M a b = M b a := fun M hM a b => by
    rw [← Matrix.transpose_apply M b a, hM]
  ext k l
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exact h (k, l) (mem_vWedgePairs_iff.2 hkl)
  · rw [hA0, hA0']
  · rw [s A hA k l, s A' hA' k l]
    exact h (l, k) (mem_vWedgePairs_iff.2 hkl)

theorem vWedgeRoots_comm : RootCommFamily .E7 K vWedgeRoots :=
  vPsi_comm.of_sublist fun _ hβ => mem_vPsi_of_mem_vWedgeRoots hβ

theorem conj_hyp_vWedgeRoots {i j : Fin 6} (hij : i ≠ j) :
    ∀ β ∈ vWedgeRoots, e7A5Root i j ≠ -β ∧
      (IsRoot .E7 (e7A5Root i j + β) → e7A5Root i j + β ∈ vWedgeRoots) := by
  intro β hβ
  have h0 := vLevel_e7A5Root hij
  have h2 := vLevel_of_mem_vWedgeRoots hβ
  obtain ⟨n1, n6⟩ := e7A5Root_nodes_check i j
  obtain ⟨b1, b6⟩ := (vWedgeRoots_check.2.1 β hβ).2.2
  refine ⟨fun h => ?_, fun hr => mem_vWedgeRoots_of_isRoot hr ⟨?_, ?_⟩⟩
  · rw [h, vLevel_neg] at h0
    omega
  · rw [Pi.add_apply, n1, b1, zero_add]
  · rw [Pi.add_apply, n6, b6, zero_add]

theorem ne_sub_of_mem_vWedgeRoots {i j : Fin 6} (hij : i ≠ j) {γ : Fin Tag.E7.rank → ℤ}
    (hγ : γ ∈ vWedgeRoots) : e7A5Root i j ≠ γ - e7A5Root i j := fun h => by
  have e := congrArg vLevel h
  have h0 := vLevel_e7A5Root hij
  have h2 := vLevel_of_mem_vWedgeRoots hγ
  rw [sub_eq_add_neg, vLevel_add, vLevel_neg] at e
  omega

theorem conj_vWedgeElt_pinnedX_e7A5Root [CharP K 2] {i j : Fin 6} (hij : i ≠ j) (c : K)
    {A : Matrix (Fin 6) (Fin 6) K} (hA : Aᵀ = A) (hA0 : ∀ k, A k k = 0) :
    pinnedX .E7 K (e7A5Root i j) c * vWedgeElt K A * (pinnedX .E7 K (e7A5Root i j) c)⁻¹ =
      vWedgeElt K (Matrix.transvection j i c * A * Matrix.transvection i j c) := by
  rw [vWedgeElt, E6Pilot.conj_rootProd (Or.inr (Or.inr (Or.inl rfl))) CharTwo.two_eq_zero
    vWedgeRoots_nodup (fun _ hβ => isRoot_of_mem_vWedgeRoots hβ) vWedgeRoots_comm
    (isRoot_e7A5Root hij) (conj_hyp_vWedgeRoots hij) c, vWedgeElt]
  refine E6Pilot.rootProd_congr fun β hβ => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hβ
  have hlt := lt_of_mem_vWedgePairs hp
  rw [E6Pilot.conjCoeff_apply vWedgeRoots_nodup (fun _ hβ => isRoot_of_mem_vWedgeRoots hβ) _ c _
    hβ, vWedgeCoeff_vWedgeRoot _ hp, vWedgeCoeff_vWedgeRoot _ hp]
  obtain ⟨h1, h2, h3⟩ := vWedgeRoot_sub_check p hp i j hij
  obtain ⟨k, l⟩ := p
  simp only at hlt h1 h2 h3 ⊢
  by_cases hk : k = j
  · subst hk
    have hl : l ≠ k := (ne_of_lt hlt).symm
    rw [Matrix.mul_transvection_apply_of_ne (hb := hl), Matrix.transvection_mul_apply_same]
    by_cases hli : l = i
    · subst hli
      rw [ite_eq_right fun h => h3 (fun h' => h'.2 rfl) (fun h' => hl h'.1) h.1, hA0, mul_zero]
    · rw [h1 ⟨rfl, hli⟩, ite_eq_left ⟨vWedgeRoot_mem_vWedgeRoots (Ne.symm hli),
        by rw [← h1 ⟨rfl, hli⟩]; exact ne_sub_of_mem_vWedgeRoots hij hβ⟩,
        vWedgeCoeff_vWedgeRoot_of_ne hA (fun h => hli h.symm)]
  · by_cases hl : l = j
    · subst hl
      rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_of_ne (ha := hk),
        Matrix.transvection_mul_apply_of_ne (ha := hk)]
      by_cases hki : k = i
      · subst hki
        rw [ite_eq_right fun h => h3 (fun h' => hk h'.1) (fun h' => h'.2 rfl) h.1, hA0, mul_zero]
      · rw [h2 ⟨rfl, hki⟩, ite_eq_left ⟨vWedgeRoot_mem_vWedgeRoots hki,
          by rw [← h2 ⟨rfl, hki⟩]; exact ne_sub_of_mem_vWedgeRoots hij hβ⟩,
          vWedgeCoeff_vWedgeRoot_of_ne hA hki]
    · rw [Matrix.mul_transvection_apply_of_ne (hb := hl),
        Matrix.transvection_mul_apply_of_ne (ha := hk),
        ite_eq_right fun h => h3 (fun h' => hk h'.1) (fun h' => hl h'.1) h.1, add_zero]

@[expose] noncomputable def vWedgeAct (g : Matrix.SpecialLinearGroup (Fin 6) K)
    (A : Matrix (Fin 6) (Fin 6) K) : Matrix (Fin 6) (Fin 6) K :=
  ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * A *
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

theorem vWedgeAct_one (A : Matrix (Fin 6) (Fin 6) K) : vWedgeAct 1 A = A := by
  simp [vWedgeAct]

theorem vWedgeAct_mul (g h : Matrix.SpecialLinearGroup (Fin 6) K) (A : Matrix (Fin 6) (Fin 6) K) :
    vWedgeAct (g * h) A = vWedgeAct g (vWedgeAct h A) := by
  simp only [vWedgeAct, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem vWedgeAct_add_transpose (g : Matrix.SpecialLinearGroup (Fin 6) K)
    (B : Matrix (Fin 6) (Fin 6) K) : vWedgeAct g (B + Bᵀ) = vWedgeAct g B + (vWedgeAct g B)ᵀ := by
  simp only [vWedgeAct, Matrix.add_mul, Matrix.mul_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem vWedgeAct_vWedgeAct_inv (g : Matrix.SpecialLinearGroup (Fin 6) K)
    (B : Matrix (Fin 6) (Fin 6) K) : vWedgeAct g (vWedgeAct g⁻¹ B) = B := by
  rw [← vWedgeAct_mul, mul_inv_cancel, vWedgeAct_one]

theorem vWedge_transpose_transvection (i j : Fin 6) (c : K) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp [Matrix.transvection, Matrix.transpose_add]

theorem vWedge_add_transpose_symm (B : Matrix (Fin 6) (Fin 6) K) : (B + Bᵀ)ᵀ = B + Bᵀ := by
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem vWedge_add_transpose_diag [CharP K 2] (B : Matrix (Fin 6) (Fin 6) K) (k : Fin 6) :
    (B + Bᵀ) k k = 0 := by
  rw [Matrix.add_apply, Matrix.transpose_apply, CharTwo.add_self_eq_zero]

theorem conj_vWedgeElt_slToAdjointE7 [Finite K] [CharP K 2]
    (g : Matrix.SpecialLinearGroup (Fin 6) K) (B : Matrix (Fin 6) (Fin 6) K) :
    ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K) * vWedgeElt K (B + Bᵀ) *
        ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ =
      vWedgeElt K (vWedgeAct g B + (vWedgeAct g B)ᵀ) := by
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 6) K → Matrix.SpecialLinearGroup (Fin 6) K)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing B with
  | mem x hx =>
    obtain ⟨⟨i, j, hij, c⟩, rfl⟩ := hx
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, slToAdjointE7_transvection,
      coe_e7A5Elt, ← vWedgeAct_add_transpose]
    have hinv : ((Matrix.SpecialLinearGroup.transvection hij c)⁻¹ :
        Matrix.SpecialLinearGroup (Fin 6) K) = Matrix.SpecialLinearGroup.transvection hij c := by
      rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
    have hT : ((Matrix.SpecialLinearGroup.transvection hij c :
        Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          Matrix.transvection i j c := rfl
    rw [vWedgeAct, hinv, hT, vWedge_transpose_transvection]
    exact conj_vWedgeElt_pinnedX_e7A5Root hij c (vWedge_add_transpose_symm B)
      (vWedge_add_transpose_diag B)
  | one =>
    rw [map_one, OneMemClass.coe_one, one_mul, inv_one, mul_one, vWedgeAct_one]
  | mul x y _ _ ihx ihy =>
    rw [map_mul, Subgroup.coe_mul, mul_inv_rev, vWedgeAct_mul]
    calc ((slToAdjointE7 K x : adjointGroup .E7 K) : ModGL .E7 K) *
          ((slToAdjointE7 K y : adjointGroup .E7 K) : ModGL .E7 K) * vWedgeElt K (B + Bᵀ) *
          (((slToAdjointE7 K y : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ *
            ((slToAdjointE7 K x : adjointGroup .E7 K) : ModGL .E7 K)⁻¹)
        = ((slToAdjointE7 K x : adjointGroup .E7 K) : ModGL .E7 K) *
          (((slToAdjointE7 K y : adjointGroup .E7 K) : ModGL .E7 K) * vWedgeElt K (B + Bᵀ) *
            ((slToAdjointE7 K y : adjointGroup .E7 K) : ModGL .E7 K)⁻¹) *
          ((slToAdjointE7 K x : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ := by group
      _ = _ := by rw [ihy, ihx]
  | inv x _ ihx =>
    have h := ihx (vWedgeAct x⁻¹ B)
    rw [vWedgeAct_vWedgeAct_inv] at h
    rw [map_inv, Subgroup.coe_inv, inv_inv, ← h]
    group

variable (K) in
@[expose] def vFormUpper : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun k l => if (k : ℕ) + l = 5 ∧ k < l then 1 else 0

variable (K) in
@[expose] def vForm : Matrix (Fin 6) (Fin 6) K := vFormUpper K + (vFormUpper K)ᵀ

theorem vForm_vWedgePairs {p : Fin 6 × Fin 6} (hp : p ∈ vWedgePairs) :
    vForm K p.1 p.2 = if (p.1 : ℕ) + p.2 = 5 then 1 else 0 := by
  have hlt := lt_of_mem_vWedgePairs hp
  simp only [vForm, vFormUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [ite_eq_right (c := (p.2 : ℕ) + p.1 = 5 ∧ p.2 < p.1) (fun h => (lt_asymm hlt h.2).elim),
    add_zero]
  exact if_congr (and_iff_left hlt) rfl rfl

theorem e7SpIdx_symm_check : e7SpIdx.symm 0 = .inl 0 ∧ e7SpIdx.symm 1 = .inl 1 ∧
    e7SpIdx.symm 2 = .inl 2 ∧ e7SpIdx.symm 3 = .inr 2 ∧ e7SpIdx.symm 4 = .inr 1 ∧
    e7SpIdx.symm 5 = .inr 0 := by
  decide

theorem reindex_blueprintGram_eq_vForm [CharP K 2] :
    Matrix.reindexAlgEquiv K K e7SpIdx
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = vForm K := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := e7SpIdx_symm_check
  ext k l
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, vForm,
    vFormUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  fin_cases k <;> fin_cases l <;> simp [h0, h1, h2, h3, h4, h5, CharTwo.neg_eq]

theorem vWedgeElt_vForm : vWedgeElt K (vForm K) = rootProd .E7 K [vθ, vφ, vψ] fun _ => 1 := by
  have e : ∀ β ∈ vWedgeRoots, vWedgeCoeff (vForm K) β =
      if β ∈ [vθ, vφ, vψ] then (fun _ => (1 : K)) β else 0 := by
    intro β hβ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hβ
    rw [vWedgeCoeff_vWedgeRoot _ hp, vForm_vWedgePairs hp]
    exact if_congr (vWedgeFrame_check.1 p hp).symm rfl rfl
  rw [vWedgeElt, E6Pilot.rootProd_congr e, E6Pilot.rootProd_ite_mem, vWedgeFrame_check.2]

theorem vAS_eq_mul_vWedgeElt : vAS K = pinnedX .E7 K vγ 1 * vWedgeElt K (vForm K) := by
  rw [vWedgeElt_vForm]
  have hc : Commute (pinnedX .E7 K vψ (1 : K)) (pinnedX .E7 K vφ 1) :=
    vPsi_comm vψ (mem_vPsi_of_mem_vFrame (mem_vFrame.2 (Or.inr (Or.inr (Or.inl rfl))))) vφ
      (mem_vPsi_of_mem_vFrame (mem_vFrame.2 (Or.inr (Or.inr (Or.inr rfl))))) 1 1
  simp only [vAS, rootProd, vFrame_eq, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [hc.eq]

section Finite

variable [Finite K] [CharP K 2]

theorem commute_slToAdjointE7_pinnedX_vγ (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    Commute ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K) (pinnedX .E7 K vγ 1) := by
  have hγ : IsRoot .E7 vγ :=
    isRoot_of_mem_vPsi (mem_vPsi_of_mem_vFrame (mem_vFrame.2 (Or.inl rfl)))
  have htop : (centralizer ({pinnedX .E7 K vγ 1} : Set (ModGL .E7 K))).comap
      ((adjointGroup .E7 K).subtype.comp (slToAdjointE7 K)) = ⊤ := by
    rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [SetLike.mem_coe, mem_comap, MonoidHom.comp_apply,
      Matrix.TransvectionStruct.toSpecialLinearGroup_mk, slToAdjointE7_transvection,
      Subgroup.subtype_apply, coe_e7A5Elt, mem_centralizer_singleton_iff]
    obtain ⟨h1, h2⟩ := vGamma_e7A5_check i j hij
    refine (CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_e7A5Root hij) hγ h2 ?_ c 1).eq
    rw [← isRootB_iff, h1]
    exact Bool.false_ne_true
  have hg : g ∈ (centralizer ({pinnedX .E7 K vγ 1} : Set (ModGL .E7 K))).comap
      ((adjointGroup .E7 K).subtype.comp (slToAdjointE7 K)) := htop ▸ mem_top g
  exact mem_centralizer_singleton_iff.1 hg

theorem exists_spToSL_eq {g : Matrix.SpecialLinearGroup (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K)ᵀ * vForm K * g = vForm K) :
    ∃ A : StatedSp 3 K, spToSL K A = g := by
  set N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    Matrix.reindexAlgEquiv K K e7SpIdx.symm (g : Matrix (Fin 6) (Fin 6) K) with hN
  have hdet : N.det = 1 := by
    rw [hN, Matrix.det_reindexAlgEquiv]
    exact g.2
  set S : Matrix.SpecialLinearGroup (Fin 3 ⊕ Fin 3) K := ⟨N, hdet⟩
  have hNg : Matrix.reindexAlgEquiv K K e7SpIdx N = g := by
    rw [hN, ← Matrix.symm_reindexAlgEquiv, AlgEquiv.apply_symm_apply]
  have hcond : ((Matrix.SpecialLinearGroup.toGL S : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      ((Matrix.SpecialLinearGroup.toGL S : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
    apply (Matrix.reindexAlgEquiv K K e7SpIdx).injective
    rw [map_mul, map_mul, reindex_blueprintGram_eq_vForm]
    have hT : Matrix.reindexAlgEquiv K K e7SpIdx Nᵀ =
        (Matrix.reindexAlgEquiv K K e7SpIdx N)ᵀ := rfl
    show Matrix.reindexAlgEquiv K K e7SpIdx Nᵀ * vForm K * Matrix.reindexAlgEquiv K K e7SpIdx N =
      vForm K
    rw [hT, hNg, hg]
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL S, Subgroup.subset_closure hcond⟩, ?_⟩
  apply Subtype.ext
  rw [coe_spToSL]
  exact hNg

theorem mem_range_spToAdjointE7_of_commute (g : Matrix.SpecialLinearGroup (Fin 6) K)
    (hg : Commute ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K) (vAS K)) :
    slToAdjointE7 K g ∈ (spToAdjointE7 K).range := by
  have h1 := conj_vWedgeElt_slToAdjointE7 g (vFormUpper K)
  have hγ := commute_slToAdjointE7_pinnedX_vγ (K := K) g
  set x := ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K) with hx
  have hv : x * vAS K * x⁻¹ = vAS K := by rw [hg.eq, mul_inv_cancel_right]
  rw [vAS_eq_mul_vWedgeElt] at hv
  have hW : vWedgeElt K (vWedgeAct g (vFormUpper K) + (vWedgeAct g (vFormUpper K))ᵀ) =
      vWedgeElt K (vForm K) := by
    rw [← h1]
    have e : x * (pinnedX .E7 K vγ 1 * vWedgeElt K (vForm K)) * x⁻¹ =
        pinnedX .E7 K vγ 1 * (x * vWedgeElt K (vForm K) * x⁻¹) := by
      rw [← mul_assoc x, hγ.eq]
      group
    rw [e] at hv
    exact mul_left_cancel hv
  have hX : vWedgeAct g (vForm K) = vForm K := by
    rw [vForm, vWedgeAct_add_transpose]
    exact eq_of_forall_vWedgePairs (vWedge_add_transpose_symm _) (vWedge_add_transpose_diag _)
      (vWedge_add_transpose_symm _) (vWedge_add_transpose_diag _) fun p hp =>
        eq_of_vWedgeElt_eq hW hp
  have hgi : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (g : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hgΩ : (g : Matrix (Fin 6) (Fin 6) K)ᵀ * vForm K * g = vForm K := by
    calc (g : Matrix (Fin 6) (Fin 6) K)ᵀ * vForm K * g
        = (g : Matrix (Fin 6) (Fin 6) K)ᵀ * vWedgeAct g (vForm K) * g := by rw [hX]
      _ = (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            (g : Matrix (Fin 6) (Fin 6) K))ᵀ * vForm K *
          (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            (g : Matrix (Fin 6) (Fin 6) K)) := by
          simp only [vWedgeAct, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = vForm K := by rw [hgi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨A, hA⟩ := exists_spToSL_eq hgΩ
  exact ⟨A, by rw [spToAdjointE7, MonoidHom.comp_apply, hA]⟩

theorem rootSpan_inf_centralizer_le_range_spToAdjointE7 :
    rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊓ centralizer ({vAS K} : Set (ModGL .E7 K)) ≤
      (spToAdjointE7 K).range.map (adjointGroup .E7 K).subtype := by
  intro x hx
  obtain ⟨hxA, hxv⟩ := mem_inf.1 hx
  have hxC : x ∈ adjointGroup .E7 K := EPilot.rootSpan_le_adjointGroup' _ hxA
  have hmem : (⟨x, hxC⟩ : adjointGroup .E7 K) ∈ (slToAdjointE7 K).range := by
    rw [range_slToAdjointE7]
    exact mem_subgroupOf.2 hxA
  obtain ⟨g, hg⟩ := hmem
  have hcomm : Commute ((slToAdjointE7 K g : adjointGroup .E7 K) : ModGL .E7 K) (vAS K) := by
    rw [hg]
    exact mem_centralizer_singleton_iff.1 hxv
  obtain ⟨A, hA⟩ := mem_range_spToAdjointE7_of_commute g hcomm
  exact ⟨spToAdjointE7 K A, ⟨A, rfl⟩, by rw [hA, hg]; rfl⟩

theorem rootSpan_inf_centralizer_eq_range_spToAdjointE7 :
    rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊓ centralizer ({vAS K} : Set (ModGL .E7 K)) =
      (spToAdjointE7 K).range.map (adjointGroup .E7 K).subtype := by
  refine le_antisymm rootSpan_inf_centralizer_le_range_spToAdjointE7 (le_inf ?_ ?_)
  · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
    have h : spToAdjointE7 K A ∈ (slToAdjointE7 K).range := ⟨spToSL K A, rfl⟩
    rw [range_slToAdjointE7] at h
    exact mem_subgroupOf.1 h
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := congrArg Subtype.val
      (mem_centralizer_singleton_iff.1 (range_spToAdjointE7_le_centralizer hx))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four] at h1
    exact mem_centralizer_singleton_iff.2 h1

end Finite

end CFSG.SeitzReduction.E7Pilot
