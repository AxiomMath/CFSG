module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRestrictionFieldTwist
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityInner
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRestrictionFieldBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

omit P in
theorem blockMatrix_mul_apply_of_not_mem {I : Finset (Fin n)} (A : Matrix I I K)
    (C : Matrix (Fin n) (Fin n) K) {p : Fin n} (hp : p ∉ I) (j : Fin n) :
    (blockMatrix I A * C) p j = C p j := by
  have h : ∀ q, blockMatrix I A p q = (1 : Matrix (Fin n) (Fin n) K) p q := fun q => by
    rw [blockMatrix_apply, dite_eq_right (fun h => hp h.1)]
  rw [mul_apply]
  simp_rw [h]
  rw [← mul_apply, Matrix.one_mul]

omit P in
theorem submatrix_blockMatrix (I : Finset (Fin n)) (A : Matrix I I K) :
    (blockMatrix I A).submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n) = A := by
  ext x y
  rw [submatrix_apply, blockMatrix_apply, dite_eq_left ⟨x.2, y.2⟩]

theorem inv_mul_mem_radical_of_eq {X N : SpecialLinearGroup (Fin n) K}
    (hX : X ∈ P.parabolic K) (hN : N ∈ P.parabolic K)
    (h : ∀ i j, P.level i = P.level j →
      (X : Matrix (Fin n) (Fin n) K) i j = (N : Matrix (Fin n) (Fin n) K) i j) :
    N⁻¹ * X ∈ P.radical K := by
  have hNi : N⁻¹ ∈ P.parabolic K := inv_mem hN
  have hT : N⁻¹ * X ∈ P.parabolic K := mul_mem hNi hX
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | heq
  · rw [hT hlt, one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hlt
  · have h1 : (1 : Matrix (Fin n) (Fin n) K) i j =
        (((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (N : Matrix (Fin n) (Fin n) K)) i j := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      rfl
    show (((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K)) i j = _
    rw [h1, P.mul_apply_of_level_eq hNi hX heq.symm, P.mul_apply_of_level_eq hNi hN heq.symm]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · rw [h l j (hl.trans heq.symm)]
    · rfl

theorem inv_blockEmbed_mul_conj_mem_radical (B : GL (Fin n) K)
    (hB : (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level)
    (Z W : SpecialLinearGroup P.free K)
    (hW : (W : Matrix P.free P.free K) =
      (B : Matrix (Fin n) (Fin n) K).submatrix Subtype.val Subtype.val *
        (Z : Matrix P.free P.free K) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix Subtype.val Subtype.val) :
    (blockEmbed P.free W)⁻¹ * slConjugation n K B (blockEmbed P.free Z) ∈ P.radical K := by
  have hBi : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hB
  have hpar : ∀ Y : SpecialLinearGroup P.free K, blockEmbed P.free Y ∈ P.parabolic K := fun Y =>
    P.blockDiag_le_parabolic (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem Y))
  set M := blockMatrix P.free (Z : Matrix P.free P.free K) with hMdef
  have hM : M.BlockTriangular P.level := hpar Z
  set X := slConjugation n K B (blockEmbed P.free Z) with hXdef
  have hXmat : (X : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (M * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [hXdef, coe_slConjugation, coe_blockEmbed, Matrix.mul_assoc]
  have hX : X ∈ P.parabolic K := by
    change (X : Matrix (Fin n) (Fin n) K).BlockTriangular P.level
    rw [hXmat]
    exact hB.mul (hM.mul hBi)
  refine P.inv_mul_mem_radical_of_eq hX (hpar W) fun i j hij => ?_
  rw [hXmat, coe_blockEmbed]
  by_cases hi : P.level i = 1
  ·
    have hiJ : i ∈ P.free := P.mem_free.2 hi
    have hjJ : j ∈ P.free := P.mem_free.2 (hij ▸ hi)
    have h1 : ((B : Matrix (Fin n) (Fin n) K) *
        (M * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).submatrix Subtype.val
          Subtype.val = (W : Matrix P.free P.free K) := by
      rw [P.submatrix_mul_free hB (hM.mul hBi), P.submatrix_mul_free hM hBi, hMdef,
        submatrix_blockMatrix, hW, Matrix.mul_assoc]
    have h2 := congrFun (congrFun h1 ⟨i, hiJ⟩) ⟨j, hjJ⟩
    rw [submatrix_apply] at h2
    rw [h2, blockMatrix_apply, dite_eq_left ⟨hiJ, hjJ⟩]
  ·
    have hiJ : i ∉ P.free := fun h => hi (P.mem_free.1 h)
    rw [P.mul_apply_of_level_eq hB (hM.mul hBi) hij]
    have hsum : (∑ l, if P.level l = P.level i then (B : Matrix (Fin n) (Fin n) K) i l *
          (M * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) l j else 0) =
        ∑ l, if P.level l = P.level i then (B : Matrix (Fin n) (Fin n) K) i l *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l j else 0 := by
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with hl
      · rw [hMdef, blockMatrix_mul_apply_of_not_mem _ _
          (fun h => hi (hl.symm.trans (P.mem_free.1 h))) j]
      · rfl
    rw [hsum, ← P.mul_apply_of_level_eq hB hBi hij, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, blockMatrix_apply, dite_eq_right (fun h => hiJ h.1)]

variable (K) in
@[expose] noncomputable def freeEquiv (hlt : P.free.card < n) :
    blockSL (K := K) P.free ≃* SpecialLinearGroup (Fin P.free.card) K :=
  (MulEquiv.subgroupCongr (blockSL_eq_range P.free)).trans
    ((MonoidHom.ofInjective (proj_comp_blockEmbed_injective (K := K) hlt)).symm.trans
      (reindexSpecialLinear P.free.equivFin))

theorem coe_freeEquiv_symm (hlt : P.free.card < n) (x : SpecialLinearGroup (Fin P.free.card) K) :
    (((P.freeEquiv K hlt).symm x : blockSL (K := K) P.free) : projectiveSL n K) =
      proj n K (blockEmbed P.free ((reindexSpecialLinear P.free.equivFin).symm x)) :=
  rfl

omit P in
theorem coe_reindexSpecialLinear_symm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (x : SpecialLinearGroup κ K) :
    (((reindexSpecialLinear e).symm x : SpecialLinearGroup ι K) : Matrix ι ι K) =
      (x : Matrix κ κ K).submatrix e e :=
  rfl

section RC

variable [Finite K] [CharP K 2]

theorem slFieldPart_congr_eq_of_twist (hq : 4 ≤ Nat.card K) (hk : 0 < k) (hm : 3 ≤ P.free.card)
    (hlt : P.free.card < n) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (blockSL (K := K) P.free))
    (hβbar : ∀ s : blockSL (K := K) P.free,
      ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K)
    (κ : blockSL (K := K) P.free ≃* SpecialLinearGroup (Fin P.free.card) K)
    (B : GL (Fin n) K) (τ : MulAut (projectiveSL n K))
    (τm : MulAut (SpecialLinearGroup (Fin P.free.card) K))
    (hβτ : β = conjAut n K B * τ) (hτQ : ∀ x ∈ P.radicalP K, τ x ∈ P.radicalP K)
    (hτS : ∀ x : SpecialLinearGroup (Fin P.free.card) K,
      τ (proj n K (blockEmbed P.free ((reindexSpecialLinear P.free.equivFin).symm x))) =
        proj n K (blockEmbed P.free ((reindexSpecialLinear P.free.equivFin).symm (τm x)))) :
    slFieldPart hm (MulAut.congr κ βbar) = slFieldPart hm τm := by
  have hJ2 : 2 ≤ P.free.card := by omega
  have hβQ : (P.radicalP K).map β.toMonoidHom = P.radicalP K :=
    P.map_radicalP_eq_of_map_eq hq hJ2 β hβ
  have hτQ' : (P.radicalP K).map τ.toMonoidHom = P.radicalP K := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective τ.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hτQ x hx
  have hβmem : ∀ x ∈ P.radicalP K, β x ∈ P.radicalP K := fun x hx => by
    rw [← hβQ]
    exact ⟨x, hx, rfl⟩
  have hβinv : ∀ x ∈ P.radicalP K, β⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [← hβQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hτinv : ∀ x ∈ P.radicalP K, τ⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [← hτQ'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hcB : conjAut n K B = β * τ⁻¹ := by rw [hβτ, mul_inv_cancel_right]
  have hB1 : ∀ x ∈ P.radicalP K, conjAut n K B x ∈ P.radicalP K := fun x hx => by
    rw [hcB, MulAut.mul_apply]
    exact hβmem _ (hτinv x hx)
  have hB2 : ∀ x ∈ P.radicalP K, conjAut n K B⁻¹ x ∈ P.radicalP K := fun x hx => by
    rw [map_inv, hcB, _root_.mul_inv_rev, inv_inv, MulAut.mul_apply]
    exact hτQ _ (hβinv x hx)
  have hBt := P.blockTriangular_of_conjAut hk B hB1 hB2
  have hBi : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hBt
  set BJ : Matrix P.free P.free K :=
    (B : Matrix (Fin n) (Fin n) K).submatrix Subtype.val Subtype.val with hBJ
  set BJ' : Matrix P.free P.free K :=
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix Subtype.val Subtype.val with hBJ'
  have hBB' : BJ * BJ' = 1 := by
    rw [hBJ, hBJ', ← P.submatrix_mul_free hBt hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      submatrix_one _ Subtype.val_injective]
  have hB'B : BJ' * BJ = 1 := by
    rw [hBJ, hBJ', ← P.submatrix_mul_free hBi hBt, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      submatrix_one _ Subtype.val_injective]
  set B'' : GL (Fin P.free.card) K :=
    ⟨BJ.submatrix P.free.equivFin.symm P.free.equivFin.symm,
      BJ'.submatrix P.free.equivFin.symm P.free.equivFin.symm,
      by rw [submatrix_mul_equiv, hBB', submatrix_one_equiv],
      by rw [submatrix_mul_equiv, hB'B, submatrix_one_equiv]⟩ with hB''
  set γ₁ : MulAut (SpecialLinearGroup (Fin P.free.card) K) :=
    slConjugation P.free.card K B'' * τm with hγ₁
  set κ₀ := P.freeEquiv K hlt with hκ₀
  set ψ : MulAut (blockSL (K := K) P.free) := MulAut.congr κ₀.symm γ₁ with hψdef
  have hψx : ∀ x, ψ (κ₀.symm x) = κ₀.symm (γ₁ x) := fun x => by
    show κ₀.symm (γ₁ (κ₀ (κ₀.symm x))) = κ₀.symm (γ₁ x)
    rw [MulEquiv.apply_symm_apply]
  have hψ : ∀ s : blockSL (K := K) P.free,
      ((ψ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K := by
    intro s
    obtain ⟨x, rfl⟩ := κ₀.symm.surjective s
    rw [hψx, hκ₀, P.coe_freeEquiv_symm, P.coe_freeEquiv_symm, hβτ,
      MulAut.mul_apply _ (conjAut n K B) τ, hτS,
      conjAut_proj, ← map_inv, ← map_mul]
    refine Subgroup.mem_map_of_mem _ (P.inv_blockEmbed_mul_conj_mem_radical B hBt _ _ ?_)
    rw [coe_reindexSpecialLinear_symm, coe_reindexSpecialLinear_symm, hγ₁, MulAut.mul_apply,
      coe_slConjugation, ← submatrix_mul_equiv _ _ _ P.free.equivFin _,
      ← submatrix_mul_equiv _ _ _ P.free.equivFin _]
    have h1 : (B'' : Matrix (Fin P.free.card) (Fin P.free.card) K).submatrix P.free.equivFin
        P.free.equivFin = BJ := by
      change (BJ.submatrix P.free.equivFin.symm P.free.equivFin.symm).submatrix P.free.equivFin
        P.free.equivFin = BJ
      rw [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
    have h2 : ((B''⁻¹ : GL (Fin P.free.card) K) :
        Matrix (Fin P.free.card) (Fin P.free.card) K).submatrix P.free.equivFin
          P.free.equivFin = BJ' := by
      change (BJ'.submatrix P.free.equivFin.symm P.free.equivFin.symm).submatrix P.free.equivFin
        P.free.equivFin = BJ'
      rw [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
    rw [h1, h2]
  have hdisj : Disjoint (P.radicalP K) (blockSL (K := K) P.free) :=
    P.disjoint_radicalP.mono_right le_sup_right
  have hβbarψ : βbar = ψ := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    have hmem : ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ *
        ((ψ s : blockSL (K := K) P.free) : projectiveSL n K) ∈ P.radicalP K := by
      have h : ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ *
          ((ψ s : blockSL (K := K) P.free) : projectiveSL n K) =
          (((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s) *
            (((ψ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s)⁻¹ := by group
      rw [h]
      exact mul_mem (hβbar s) (inv_mem (hψ s))
    have hmemS : ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ *
        ((ψ s : blockSL (K := K) P.free) : projectiveSL n K) ∈ blockSL (K := K) P.free :=
      mul_mem (inv_mem (βbar s).2) (ψ s).2
    exact inv_mul_eq_one.1 (Subgroup.disjoint_def.1 hdisj hmem hmemS)
  rw [hβbarψ, ← slFieldPart_eq_of_intertwine hm (MulEquiv.refl _) κ κ₀.symm γ₁ ψ hψx]
  have hrefl : MulAut.congr (MulEquiv.refl (SpecialLinearGroup (Fin P.free.card) K)) γ₁ = γ₁ := by
    ext x
    rfl
  rw [hrefl, hγ₁, map_mul, slFieldPart_slConjugation, one_mul]

theorem restrictionField (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (hk : 0 < k)
    (hJ : 3 ≤ P.free.card) : P.RestrictionField K hn := by
  intro β hβ βbar hβbar m hm κ
  have : Fintype K := Fintype.ofFinite K
  have hlt : P.free.card < n := by have := P.card_free; omega
  have hmJ : m = P.free.card := by
    refine eq_of_card_specialLinearGroup_eq (K := K) (by omega) (by omega) ?_
    rw [← Nat.card_congr κ.toEquiv, card_blockSL_eq hlt]
  subst hmJ
  obtain ⟨σ, A, ε, hε, hβeq⟩ := ProjectivePlane.exists_standard_form K n hn β
  rw [hβeq, linearFieldPart_eq hn hε]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [P.slFieldPart_congr_eq_of_twist hq hk hm hlt β hβ βbar hβbar κ A (fieldAut n K σ)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin P.free.card) K σ)
      (by rw [hβeq, pow_zero, mul_one]) (fun x hx => P.fieldAut_mem_radicalP σ hx)
      (fun x => by rw [fieldAut_proj_blockEmbed]; rfl), slFieldPart_slFieldAut]
  · rw [P.slFieldPart_congr_eq_of_twist hq hk hm hlt β hβ βbar hβbar κ (A * (P.outerSwapGL K)⁻¹)
      (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin P.free.card) K σ *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut P.free.card K)
      (by rw [hβeq, pow_one, map_mul, map_inv]; group) (fun x hx => P.graphTwist_mem_radicalP σ hx)
      (fun x => by rw [P.graphTwist_proj_blockEmbed, ← map_inv]; rfl),
      map_mul, slFieldPart_slFieldAut, slFieldPart_slGraphAut, mul_one]

end RC

end InvPlacement

end CFSG.SeitzReduction.LinearPilot

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)

variable {n k k' : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem fieldRigidIn_inner_of_three_le (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (P : InvPlacement n k)
    (P' : InvPlacement n k') (hP : P.elt K ≠ 1) (hP' : P'.elt K ≠ 1) (hJ : 3 ≤ P.free.card)
    (hJ' : 3 ≤ P'.free.card) :
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) :=
  fieldRigidIn_inner hq hn P P' hP hP' hJ hJ'
    (P.restrictionField hq hn (Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)) hJ)
    (P'.restrictionField hq hn (Nat.pos_of_ne_zero fun h => hP' (P'.elt_eq_one_of_eq_zero h)) hJ')

end CFSG.SeitzReduction.LinearPilot
