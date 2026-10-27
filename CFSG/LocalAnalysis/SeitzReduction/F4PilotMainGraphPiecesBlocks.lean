module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockEmbed
  blockMatrix blockMatrix_apply coe_blockEmbed blockEmbed_injective range_blockEmbed
  reindexSpecialLinear commute_blockSpecialLinear_of_disjoint blockSpecialLinear_mono)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups commutatorElement

section Card

variable {n : ℕ} {F : Type*} [Field F]

theorem natCard_blockSpecialLinear [Finite F] {I : Finset (Fin n)} (hI : 1 ≤ I.card) :
    Nat.card (blockSpecialLinear (K := F) I) = ordSL I.card (Nat.card F) := by
  rw [← range_blockEmbed,
    ← Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (K := F) I)).toEquiv,
    Nat.card_congr (reindexSpecialLinear (K := F) I.equivFin).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hI]
  rfl

theorem blockSpecialLinear_inf_eq_bot_of_disjoint {I₁ I₂ : Finset (Fin n)} (h : Disjoint I₁ I₂) :
    blockSpecialLinear (K := F) I₁ ⊓ blockSpecialLinear I₂ = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨h₁, h₂⟩ := mem_inf.1 hg
  refine (mem_bot).2 (Subtype.ext (Matrix.ext fun i j => ?_))
  by_cases hi : i ∈ I₁ ∧ j ∈ I₁
  · exact h₂ i j (Or.inl (Finset.disjoint_left.1 h hi.1))
  · exact h₁ i j (not_and_or.1 hi)

theorem natCard_sup_blockSpecialLinear_of_disjoint [Finite F] {I₁ I₂ : Finset (Fin n)}
    (h : Disjoint I₁ I₂) :
    Nat.card (blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ : Subgroup _) =
      Nat.card (blockSpecialLinear (K := F) I₁) * Nat.card (blockSpecialLinear (K := F) I₂) := by
  set H₁ := blockSpecialLinear (K := F) I₁
  set H₂ := blockSpecialLinear (K := F) I₂
  have hcomm : ∀ (a : H₁) (b : H₂), Commute (H₁.subtype a) (H₂.subtype b) :=
    fun a b => commute_blockSpecialLinear_of_disjoint h a.2 b.2
  set φ := MonoidHom.noncommCoprod H₁.subtype H₂.subtype hcomm
  have hinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).2 ⟨H₁.subtype_injective, H₂.subtype_injective,
      by
        rw [range_subtype, range_subtype, disjoint_iff]
        exact blockSpecialLinear_inf_eq_bot_of_disjoint h⟩
  have hrange : φ.range = H₁ ⊔ H₂ := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

end Card

section Diagonal

variable {n : ℕ} {F : Type*} [Field F]

theorem mul_apply_of_offDiag_eq_zero {d x : Matrix (Fin n) (Fin n) F}
    (hd : ∀ i j, i ≠ j → d i j = 0) (i j : Fin n) :
    (d * x) i j = d i i * x i j ∧ (x * d) i j = x i j * d j j := by
  refine ⟨?_, ?_⟩
  · rw [mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hd i k (Ne.symm hki), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
  · rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by rw [hd k j hkj, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]

theorem diag_ne_zero_of_offDiag_eq_zero {d : SpecialLinearGroup (Fin n) F}
    (hd : ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0) (i : Fin n) :
    (d : Matrix (Fin n) (Fin n) F) i i ≠ 0 := by
  intro h0
  have := det_eq_zero_of_row_eq_zero (A := (d : Matrix (Fin n) (Fin n) F)) i fun j => by
    by_cases hij : i = j
    · rw [← hij, h0]
    · exact hd i j hij
  rw [d.2] at this
  exact one_ne_zero this

theorem blockSpecialLinear_le_centralizer_of_const {I : Finset (Fin n)}
    {D : Set (SpecialLinearGroup (Fin n) F)}
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    (hconst : ∀ d ∈ D, ∀ i ∈ I, ∀ j ∈ I,
      (d : Matrix (Fin n) (Fin n) F) i i = (d : Matrix (Fin n) (Fin n) F) j j) :
    blockSpecialLinear (K := F) I ≤ centralizer D := by
  intro x hx
  rw [mem_centralizer_iff]
  intro d hd
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  rw [(mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).1,
    (mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).2]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hconst d hd i hij.1 j hij.2, mul_comm]
  · rw [(mem_blockSpecialLinear.mp hx) i j (by tauto)]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, mul_zero, zero_mul]

end Diagonal


section TwoBlocks

variable {n : ℕ} {F : Type*} [Field F] {I₁ I₂ : Finset (Fin n)}

@[expose] def TwoBlockDiag (I₁ I₂ : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, i ≠ j → ¬ (i ∈ I₁ ∧ j ∈ I₁) → ¬ (i ∈ I₂ ∧ j ∈ I₂) → x i j = 0

theorem TwoBlockDiag.symm {x : Matrix (Fin n) (Fin n) F} (hx : TwoBlockDiag I₁ I₂ x) :
    TwoBlockDiag I₂ I₁ x :=
  fun i j hij h₂ h₁ => hx i j hij h₁ h₂

theorem TwoBlockDiag.mul (h : Disjoint I₁ I₂) {x y : Matrix (Fin n) (Fin n) F}
    (hx : TwoBlockDiag I₁ I₂ x) (hy : TwoBlockDiag I₁ I₂ y) : TwoBlockDiag I₁ I₂ (x * y) := by
  intro i j hij h₁ h₂
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hxk : x i k = 0
  · rw [hxk, zero_mul]
  have hk : i = k ∨ (i ∈ I₁ ∧ k ∈ I₁) ∨ (i ∈ I₂ ∧ k ∈ I₂) := by
    by_contra hc
    push Not at hc
    exact hxk (hx i k hc.1 (fun h' => hc.2.1 h'.1 h'.2) (fun h' => hc.2.2 h'.1 h'.2))
  rcases hk with rfl | ⟨hi, hk⟩ | ⟨hi, hk⟩
  · rw [hy i j hij h₁ h₂, mul_zero]
  · have hkj : k ≠ j := by
      rintro rfl
      exact h₁ ⟨hi, hk⟩
    rw [hy k j hkj (fun h' => h₁ ⟨hi, h'.2⟩) (fun h' => Finset.disjoint_left.1 h hk h'.1),
      mul_zero]
  · have hkj : k ≠ j := by
      rintro rfl
      exact h₂ ⟨hi, hk⟩
    rw [hy k j hkj (fun h' => Finset.disjoint_left.1 h h'.1 hk) (fun h' => h₂ ⟨hi, h'.2⟩),
      mul_zero]

theorem TwoBlockDiag.mul_apply_self {x : Matrix (Fin n) (Fin n) F} (hx : TwoBlockDiag I₁ I₂ x)
    (y : Matrix (Fin n) (Fin n) F) {j : Fin n} (hj₁ : j ∉ I₁) (hj₂ : j ∉ I₂) :
    (x * y) j j = x j j * y j j := by
  rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by
      rw [hx j k (Ne.symm hkj) (fun h' => hj₁ h'.1) (fun h' => hj₂ h'.1), zero_mul])
    (fun h' => absurd (Finset.mem_univ j) h')]

theorem TwoBlockDiag.submatrix_mul (h : Disjoint I₁ I₂) {x : Matrix (Fin n) (Fin n) F}
    (hx : TwoBlockDiag I₁ I₂ x) (y : Matrix (Fin n) (Fin n) F) :
    (x * y).submatrix (Subtype.val : I₁ → Fin n) (Subtype.val : I₁ → Fin n) =
      x.submatrix (Subtype.val : I₁ → Fin n) (Subtype.val : I₁ → Fin n) *
        y.submatrix (Subtype.val : I₁ → Fin n) (Subtype.val : I₁ → Fin n) := by
  ext a b
  simp only [submatrix_apply, mul_apply]
  rw [Finset.sum_coe_sort I₁ (fun k => x a k * y k b)]
  refine (Finset.sum_subset (Finset.subset_univ I₁) fun k _ hk => ?_).symm
  have hak : (a : Fin n) ≠ k := fun h' => hk (h' ▸ a.2)
  rw [hx a k hak (fun h' => hk h'.2) (fun h' => Finset.disjoint_left.1 h a.2 h'.1), zero_mul]

theorem TwoBlockDiag.det_submatrix_mul (h : Disjoint I₁ I₂) {x : Matrix (Fin n) (Fin n) F}
    (hx : TwoBlockDiag I₁ I₂ x) (y : Matrix (Fin n) (Fin n) F) :
    ((x * y).submatrix (Subtype.val : I₁ → Fin n) Subtype.val).det =
      (x.submatrix (Subtype.val : I₁ → Fin n) Subtype.val).det *
        (y.submatrix (Subtype.val : I₁ → Fin n) Subtype.val).det := by
  rw [TwoBlockDiag.submatrix_mul h hx y, det_mul]

theorem TwoBlockDiag.det_submatrix_mul_inv (h : Disjoint I₁ I₂)
    {x x' : Matrix (Fin n) (Fin n) F} (hx : TwoBlockDiag I₁ I₂ x) (hxx' : x * x' = 1) :
    (x.submatrix (Subtype.val : I₁ → Fin n) Subtype.val).det *
      (x'.submatrix (Subtype.val : I₁ → Fin n) Subtype.val).det = 1 := by
  rw [← TwoBlockDiag.det_submatrix_mul h hx x', hxx', submatrix_one _ Subtype.val_injective,
    det_one]


theorem commutatorElement_mem_sup_of_twoBlockDiag (h : Disjoint I₁ I₂)
    {x y : SpecialLinearGroup (Fin n) F}
    (hx : TwoBlockDiag I₁ I₂ (x : Matrix (Fin n) (Fin n) F))
    (hy : TwoBlockDiag I₁ I₂ (y : Matrix (Fin n) (Fin n) F))
    (hx' : TwoBlockDiag I₁ I₂ ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hy' : TwoBlockDiag I₁ I₂ ((y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    ⁅x, y⁆ ∈ blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ := by
  set X : Matrix (Fin n) (Fin n) F :=
    ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Y : Matrix (Fin n) (Fin n) F :=
    ((y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set X' : Matrix (Fin n) (Fin n) F :=
    ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Y' : Matrix (Fin n) (Fin n) F :=
    ((y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hXX' : X * X' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hYY' : Y * Y' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  set M : Matrix (Fin n) (Fin n) F := X * Y * X' * Y' with hMdef
  have hgM : ((⁅x, y⁆ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
    rw [commutatorElement_def]
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rfl
  have hXY := TwoBlockDiag.mul h hx hy
  have hXYX := TwoBlockDiag.mul h hXY hx'
  have hM : TwoBlockDiag I₁ I₂ M := TwoBlockDiag.mul h hXYX hy'
  have hdiag : ∀ j, j ∉ I₁ → j ∉ I₂ → M j j = 1 := by
    intro j hj₁ hj₂
    have h1 : X j j * X' j j = 1 := by
      rw [← TwoBlockDiag.mul_apply_self hx X' hj₁ hj₂, hXX', one_apply_eq]
    have h2 : Y j j * Y' j j = 1 := by
      rw [← TwoBlockDiag.mul_apply_self hy Y' hj₁ hj₂, hYY', one_apply_eq]
    rw [hMdef, TwoBlockDiag.mul_apply_self hXYX Y' hj₁ hj₂,
      TwoBlockDiag.mul_apply_self hXY X' hj₁ hj₂, TwoBlockDiag.mul_apply_self hx Y hj₁ hj₂]
    linear_combination Y j j * Y' j j * h1 + h2
  have hdet : ∀ {J₁ J₂ : Finset (Fin n)}, Disjoint J₁ J₂ → TwoBlockDiag J₁ J₂ X →
      TwoBlockDiag J₁ J₂ Y → TwoBlockDiag J₁ J₂ X' →
      (M.submatrix (Subtype.val : J₁ → Fin n) Subtype.val).det = 1 := by
    intro J₁ J₂ hJ bX bY bX'
    have bXY := TwoBlockDiag.mul hJ bX bY
    have bXYX := TwoBlockDiag.mul hJ bXY bX'
    rw [hMdef, TwoBlockDiag.det_submatrix_mul hJ bXYX, TwoBlockDiag.det_submatrix_mul hJ bXY,
      TwoBlockDiag.det_submatrix_mul hJ bX]
    have h1 := TwoBlockDiag.det_submatrix_mul_inv hJ bX hXX'
    have h2 := TwoBlockDiag.det_submatrix_mul_inv hJ bY hYY'
    linear_combination (Y.submatrix (Subtype.val : J₁ → Fin n) Subtype.val).det *
        (Y'.submatrix (Subtype.val : J₁ → Fin n) Subtype.val).det * h1 + h2
  have hdet₁ := hdet h hx hy hx'
  have hdet₂ := hdet h.symm (TwoBlockDiag.symm hx) (TwoBlockDiag.symm hy) (TwoBlockDiag.symm hx')
  set g₁ : SpecialLinearGroup I₁ F := ⟨M.submatrix Subtype.val Subtype.val, hdet₁⟩
  set g₂ : SpecialLinearGroup I₂ F := ⟨M.submatrix Subtype.val Subtype.val, hdet₂⟩
  have ha₁ : blockEmbed I₁ g₁ ∈ blockSpecialLinear (K := F) I₁ := by
    rw [← range_blockEmbed]
    exact ⟨g₁, rfl⟩
  have ha₂ : blockEmbed I₂ g₂ ∈ blockSpecialLinear (K := F) I₂ := by
    rw [← range_blockEmbed]
    exact ⟨g₂, rfl⟩
  have hsub := CFSG.SeitzReduction.LinearPilot.sub_one_mul_sub_one_eq_zero h ha₁ ha₂
  have heq : ⁅x, y⁆ = blockEmbed I₁ g₁ * blockEmbed I₂ g₂ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change ((⁅x, y⁆ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
    rw [hgM]
    set a₁ : Matrix (Fin n) (Fin n) F := ((blockEmbed I₁ g₁ : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) with ha₁def
    set a₂ : Matrix (Fin n) (Fin n) F := ((blockEmbed I₂ g₂ : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) with ha₂def
    have hprod : a₁ * a₂ = a₁ + a₂ - 1 := by
      calc a₁ * a₂ = (a₁ - 1) * (a₂ - 1) + a₁ + a₂ - 1 := by noncomm_ring
        _ = a₁ + a₂ - 1 := by rw [hsub, zero_add]
    rw [hprod]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, ha₁def, ha₂def, coe_blockEmbed,
      blockMatrix_apply]
    by_cases hi₁ : i ∈ I₁ ∧ j ∈ I₁
    · have hi₂ : ¬ (i ∈ I₂ ∧ j ∈ I₂) := fun h' => Finset.disjoint_left.1 h hi₁.1 h'.1
      rw [dite_eq_left hi₁, dite_eq_right hi₂]
      simp [g₁]
    · by_cases hi₂ : i ∈ I₂ ∧ j ∈ I₂
      · rw [dite_eq_right hi₁, dite_eq_left hi₂]
        simp [g₂]
      · rw [dite_eq_right hi₁, dite_eq_right hi₂]
        by_cases hij : i = j
        · subst hij
          rw [hdiag i (fun h' => hi₁ ⟨h', h'⟩) (fun h' => hi₂ ⟨h', h'⟩), one_apply_eq]
          ring
        · rw [hM i j hij hi₁ hi₂, one_apply_ne hij]
          ring
  rw [heq]
  exact mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂)

theorem perfectCore_centralizer_eq_sup_of_two_blocks [Finite F] (h : Disjoint I₁ I₂)
    (D : Set (SpecialLinearGroup (Fin n) F))
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    (hconst₁ : ∀ d ∈ D, ∀ i ∈ I₁, ∀ j ∈ I₁,
      (d : Matrix (Fin n) (Fin n) F) i i = (d : Matrix (Fin n) (Fin n) F) j j)
    (hconst₂ : ∀ d ∈ D, ∀ i ∈ I₂, ∀ j ∈ I₂,
      (d : Matrix (Fin n) (Fin n) F) i i = (d : Matrix (Fin n) (Fin n) F) j j)
    (hsep : ∀ i j, i ≠ j → ¬ (i ∈ I₁ ∧ j ∈ I₁) → ¬ (i ∈ I₂ ∧ j ∈ I₂) →
      ∃ d ∈ D, (d : Matrix (Fin n) (Fin n) F) i i ≠ (d : Matrix (Fin n) (Fin n) F) j j)
    (hperf₁ : ⁅blockSpecialLinear (K := F) I₁, blockSpecialLinear (K := F) I₁⁆ =
      blockSpecialLinear I₁)
    (hperf₂ : ⁅blockSpecialLinear (K := F) I₂, blockSpecialLinear (K := F) I₂⁆ =
      blockSpecialLinear I₂) :
    perfectCore (centralizer D) = blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ := by
  set C := centralizer D
  have hbd : ∀ x ∈ C, TwoBlockDiag I₁ I₂ (x : Matrix (Fin n) (Fin n) F) := by
    intro x hx i j hij h₁ h₂
    obtain ⟨d, hd, hne⟩ := hsep i j hij h₁ h₂
    have hc := mem_centralizer_iff.mp hx d hd
    have e := congrFun (congrFun (congrArg
      (fun A : SpecialLinearGroup (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hc) i) j
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e
    rw [(mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).1,
      (mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).2] at e
    have h0 : ((d : Matrix (Fin n) (Fin n) F) i i - (d : Matrix (Fin n) (Fin n) F) j j) *
        (x : Matrix (Fin n) (Fin n) F) i j = 0 := by linear_combination e
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hPC : ⁅C, C⁆ ≤ blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ := by
    rw [commutator_le]
    intro x hx y hy
    exact commutatorElement_mem_sup_of_twoBlockDiag h (hbd x hx) (hbd y hy)
      (hbd x⁻¹ (C.inv_mem hx)) (hbd y⁻¹ (C.inv_mem hy))
  have hsupC : blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ ≤ C :=
    sup_le (blockSpecialLinear_le_centralizer_of_const hdiag hconst₁)
      (blockSpecialLinear_le_centralizer_of_const hdiag hconst₂)
  have hperf : ⁅blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂,
      blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂⁆ =
        blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ := by
    refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le ?_ ?_)
    · calc blockSpecialLinear (K := F) I₁ = ⁅blockSpecialLinear (K := F) I₁,
            blockSpecialLinear (K := F) I₁⁆ := hperf₁.symm
        _ ≤ _ := commutator_mono le_sup_left le_sup_left
    · calc blockSpecialLinear (K := F) I₂ = ⁅blockSpecialLinear (K := F) I₂,
            blockSpecialLinear (K := F) I₂⁆ := hperf₂.symm
        _ ≤ _ := commutator_mono le_sup_right le_sup_right
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect hsupC hperf)
  calc perfectCore C = ⁅perfectCore C, perfectCore C⁆ := (CFSG.Quasithin.perfectCore_perfect C).symm
    _ ≤ ⁅C, C⁆ := commutator_mono (CFSG.Quasithin.perfectCore_le C)
        (CFSG.Quasithin.perfectCore_le C)
    _ ≤ _ := hPC

end TwoBlocks


section Rigidity

variable {n : ℕ} {F : Type*} [Field F]

theorem exists_scalar_of_commutator_mem_center {x d : SpecialLinearGroup (Fin n) F}
    (hd : ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    (hxd : ⁅x, d⁆ ∈ center (SpecialLinearGroup (Fin n) F)) :
    ∃ ζ : F, ∀ i j, (x : Matrix (Fin n) (Fin n) F) i j * (d : Matrix (Fin n) (Fin n) F) j j =
      ζ * ((d : Matrix (Fin n) (Fin n) F) i i * (x : Matrix (Fin n) (Fin n) F) i j) := by
  obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxd
  refine ⟨ζ, fun i j => ?_⟩
  have h1 : x * d = ⁅x, d⁆ * (d * x) := by
    rw [commutatorElement_def]
    group
  have h2 := congrArg
    (fun A : SpecialLinearGroup (Fin n) F => (A : Matrix (Fin n) (Fin n) F) i j) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
  rw [← hζ, Matrix.scalar_apply, Matrix.diagonal_mul,
    (mul_apply_of_offDiag_eq_zero hd i j).2, (mul_apply_of_offDiag_eq_zero hd i j).1] at h2
  exact h2

theorem eq_one_of_dominant [DecidableEq F] {x s₀ : SpecialLinearGroup (Fin n) F}
    (hs₀ : ∀ i j, i ≠ j → (s₀ : Matrix (Fin n) (Fin n) F) i j = 0) {c ζ : F}
    (hdom : n < 2 * (Finset.univ.filter fun j => (s₀ : Matrix (Fin n) (Fin n) F) j j = c).card)
    (hζ : ∀ i j, (x : Matrix (Fin n) (Fin n) F) i j * (s₀ : Matrix (Fin n) (Fin n) F) j j =
      ζ * ((s₀ : Matrix (Fin n) (Fin n) F) i i * (x : Matrix (Fin n) (Fin n) F) i j)) :
    ζ = 1 := by
  set X : Matrix (Fin n) (Fin n) F := ((x : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F)
  set S : Matrix (Fin n) (Fin n) F := ((s₀ : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F)
  have hdet : X.det ≠ 0 := by
    rw [x.2]
    exact one_ne_zero
  rw [Matrix.det_apply] at hdet
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hprod : ∏ i, X (σ i) i ≠ 0 := fun h0 => hσ (by rw [h0, smul_zero])
  have hσj : ∀ j, X (σ j) j ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
  have hval : ∀ j, S j j = ζ * S (σ j) (σ j) := by
    intro j
    have h := hζ (σ j) j
    have h' : (S j j - ζ * S (σ j) (σ j)) * X (σ j) j = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (hσj j))
  by_contra hζ1
  set A := Finset.univ.filter fun j => S j j = c
  set B := Finset.univ.filter fun j => ζ * S j j = c
  have hAB : A.map σ.toEmbedding ⊆ B := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [Equiv.toEmbedding_apply, ← hval j, hj]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
    rw [hiA] at hiB
    have hc : (ζ - 1) * c = 0 := by linear_combination hiB
    have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr hζ1)
    exact diag_ne_zero_of_offDiag_eq_zero hs₀ i (hiA.trans hc0)
  have h1 : A.card ≤ B.card := by
    rw [← Finset.card_map σ.toEmbedding]
    exact Finset.card_le_card hAB
  have h2 : A.card + B.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (A ∪ B).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Finset.card_fin n
  omega

theorem mem_centralizer_of_commutator_mem_center [DecidableEq F]
    {D : Set (SpecialLinearGroup (Fin n) F)}
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    {s₀ : SpecialLinearGroup (Fin n) F} (hs₀ : s₀ ∈ D) {c : F}
    (hdom : n < 2 * (Finset.univ.filter fun j => (s₀ : Matrix (Fin n) (Fin n) F) j j = c).card)
    {j₀ : Fin n}
    (hj₀ : ∀ i, i ≠ j₀ →
      (s₀ : Matrix (Fin n) (Fin n) F) i i ≠ (s₀ : Matrix (Fin n) (Fin n) F) j₀ j₀)
    {x : SpecialLinearGroup (Fin n) F}
    (hx : ∀ d ∈ D, ⁅x, d⁆ ∈ center (SpecialLinearGroup (Fin n) F)) :
    x ∈ centralizer D := by
  set X : Matrix (Fin n) (Fin n) F := ((x : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F)
  obtain ⟨ζ₀, hζ₀⟩ := exists_scalar_of_commutator_mem_center (hdiag s₀ hs₀) (hx s₀ hs₀)
  have h1 := eq_one_of_dominant (hdiag s₀ hs₀) hdom hζ₀
  subst h1
  have hcol : ∀ i, i ≠ j₀ → X i j₀ = 0 := by
    intro i hi
    have h := hζ₀ i j₀
    have h' : ((s₀ : Matrix (Fin n) (Fin n) F) j₀ j₀ - (s₀ : Matrix (Fin n) (Fin n) F) i i) *
        X i j₀ = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (hj₀ i hi).symm)
  have hx₀ : X j₀ j₀ ≠ 0 := by
    intro h0
    have := det_eq_zero_of_column_eq_zero (A := X) j₀ fun i => by
      by_cases hi : i = j₀
      · rw [hi, h0]
      · exact hcol i hi
    rw [x.2] at this
    exact one_ne_zero this
  rw [mem_centralizer_iff]
  intro d hd
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_commutator_mem_center (hdiag d hd) (hx d hd)
  have hd₀ := diag_ne_zero_of_offDiag_eq_zero (hdiag d hd) j₀
  have hζ1 : ζ = 1 := by
    have h := hζ j₀ j₀
    have h' : (1 - ζ) * ((d : Matrix (Fin n) (Fin n) F) j₀ j₀ * X j₀ j₀) = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp h').resolve_right (mul_ne_zero hd₀ hx₀)
    linear_combination -this
  subst hζ1
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  rw [(mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).1,
    (mul_apply_of_offDiag_eq_zero (hdiag d hd) i j).2, hζ i j, one_mul]

theorem inf_center_eq_bot_of_le_blockSpecialLinear {I : Finset (Fin n)} {j : Fin n} (hj : j ∉ I)
    {P : Subgroup (SpecialLinearGroup (Fin n) F)} (hP : P ≤ blockSpecialLinear I) :
    P ⊓ center (SpecialLinearGroup (Fin n) F) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzP, hzZ⟩ := mem_inf.1 hz
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzZ
  have hjj := (mem_blockSpecialLinear.mp (hP hzP)) j j (Or.inl hj)
  rw [← hr, Matrix.scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
  rw [mem_bot]
  apply Subtype.ext
  rw [← hr, hjj, map_one, Matrix.SpecialLinearGroup.coe_one]

end Rigidity

section Quotient

variable {n : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

theorem range_inf_centralizer_map_eq (Φ : SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {S : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hrig : ∀ x : SpecialLinearGroup (Fin n) F,
      (∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin n) F)) →
        x ∈ centralizer (S : Set (SpecialLinearGroup (Fin n) F))) :
    Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G) =
      (centralizer (S : Set (SpecialLinearGroup (Fin n) F))).map Φ := by
  apply le_antisymm
  · rintro _ ⟨⟨x, rfl⟩, hxC⟩
    refine ⟨x, hrig x fun s hs => hker ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.1 hxC (Φ s) ⟨s, hs, rfl⟩).symm
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hx s hs]

variable [Finite G] [Finite F]

theorem natCard_perfectCore_range_inf_centralizer_map (Φ : SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {S : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hrig : ∀ x : SpecialLinearGroup (Fin n) F,
      (∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin n) F)) →
        x ∈ centralizer (S : Set (SpecialLinearGroup (Fin n) F)))
    (hP : perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin n) F))) ⊓
      center (SpecialLinearGroup (Fin n) F) = ⊥) :
    Nat.card (perfectCore (Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G))) =
      Nat.card (perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin n) F)))) := by
  set P := perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin n) F)))
  rw [range_inf_centralizer_map_eq Φ hker hrig, ← CFSG.Quasithin.map_perfectCore Φ]
  have hinj : Function.Injective (Φ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h2 : (a : SpecialLinearGroup (Fin n) F) ∈ P ⊓ center (SpecialLinearGroup (Fin n) F) :=
      ⟨a.2, hker ha⟩
    rw [hP] at h2
    exact Subtype.ext (mem_bot.1 h2)
  have hrange : (Φ.comp P.subtype).range = P.map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end Quotient

end CFSG.SeitzReduction.F4Pilot
