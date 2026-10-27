module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallSL2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRestrictionField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

variable (K) in
@[expose] noncomputable def freeEquivOf (hlt : P.free.card < n) {m : ℕ} (ε : P.free ≃ Fin m) :
    blockSL (K := K) P.free ≃* SpecialLinearGroup (Fin m) K :=
  (MulEquiv.subgroupCongr (blockSL_eq_range P.free)).trans
    ((MonoidHom.ofInjective (proj_comp_blockEmbed_injective (K := K) hlt)).symm.trans
      (reindexSpecialLinear ε))

theorem coe_freeEquivOf_symm (hlt : P.free.card < n) {m : ℕ} (ε : P.free ≃ Fin m)
    (x : SpecialLinearGroup (Fin m) K) :
    (((P.freeEquivOf K hlt ε).symm x : blockSL (K := K) P.free) : projectiveSL n K) =
      proj n K (blockEmbed P.free ((reindexSpecialLinear ε).symm x)) :=
  rfl

section RC

variable [Finite K] [CharP K 2]

theorem mulAutHom_congr_eq_of_twist (hq : 4 ≤ Nat.card K) (hk : 0 < k) (hJ2 : 2 ≤ P.free.card)
    (hlt : P.free.card < n) {m : ℕ} (ε : P.free ≃ Fin m)
    (F : MulAut (SpecialLinearGroup (Fin m) K) →* (K ≃+* K))
    (hF : ∀ A : GL (Fin m) K, F (slConjugation m K A) = 1) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (blockSL (K := K) P.free))
    (hβbar : ∀ s : blockSL (K := K) P.free,
      ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K)
    (κ : blockSL (K := K) P.free ≃* SpecialLinearGroup (Fin m) K)
    (B : GL (Fin n) K) (τ : MulAut (projectiveSL n K))
    (τm : MulAut (SpecialLinearGroup (Fin m) K))
    (hβτ : β = conjAut n K B * τ) (hτQ : ∀ x ∈ P.radicalP K, τ x ∈ P.radicalP K)
    (hτS : ∀ x : SpecialLinearGroup (Fin m) K,
      τ (proj n K (blockEmbed P.free ((reindexSpecialLinear ε).symm x))) =
        proj n K (blockEmbed P.free ((reindexSpecialLinear ε).symm (τm x)))) :
    F (MulAut.congr κ βbar) = F τm := by
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
  set B'' : GL (Fin m) K :=
    ⟨BJ.submatrix ε.symm ε.symm, BJ'.submatrix ε.symm ε.symm,
      by rw [submatrix_mul_equiv, hBB', submatrix_one_equiv],
      by rw [submatrix_mul_equiv, hB'B, submatrix_one_equiv]⟩ with hB''
  set γ₁ : MulAut (SpecialLinearGroup (Fin m) K) := slConjugation m K B'' * τm with hγ₁
  set κ₀ := P.freeEquivOf K hlt ε with hκ₀
  set ψ : MulAut (blockSL (K := K) P.free) := MulAut.congr κ₀.symm γ₁ with hψdef
  have hψx : ∀ x, ψ (κ₀.symm x) = κ₀.symm (γ₁ x) := fun x => by
    show κ₀.symm (γ₁ (κ₀ (κ₀.symm x))) = κ₀.symm (γ₁ x)
    rw [MulEquiv.apply_symm_apply]
  have hψ : ∀ s : blockSL (K := K) P.free,
      ((ψ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K := by
    intro s
    obtain ⟨x, rfl⟩ := κ₀.symm.surjective s
    rw [hψx, hκ₀, P.coe_freeEquivOf_symm, P.coe_freeEquivOf_symm, hβτ,
      MulAut.mul_apply _ (conjAut n K B) τ, hτS,
      conjAut_proj, ← map_inv, ← map_mul]
    refine Subgroup.mem_map_of_mem _ (P.inv_blockEmbed_mul_conj_mem_radical B hBt _ _ ?_)
    rw [coe_reindexSpecialLinear_symm, coe_reindexSpecialLinear_symm, hγ₁, MulAut.mul_apply,
      coe_slConjugation, ← submatrix_mul_equiv _ _ _ ε _, ← submatrix_mul_equiv _ _ _ ε _]
    have h1 : (B'' : Matrix (Fin m) (Fin m) K).submatrix ε ε = BJ := by
      change (BJ.submatrix ε.symm ε.symm).submatrix ε ε = BJ
      rw [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
    have h2 : ((B''⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).submatrix ε ε = BJ' := by
      change (BJ'.submatrix ε.symm ε.symm).submatrix ε ε = BJ'
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
  rw [hβbarψ, ← mulAutHom_congr_eq_of_intertwine F (fun a b => ringEquiv_mul_comm _ _)
    (MulEquiv.refl _) κ κ₀.symm γ₁ ψ hψx]
  have hrefl : MulAut.congr (MulEquiv.refl (SpecialLinearGroup (Fin m) K)) γ₁ = γ₁ := by
    ext x
    rfl
  rw [hrefl, hγ₁, map_mul, hF, one_mul]

theorem sl2FieldPart_eq_of_card_free_eq_two (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (hk : 0 < k)
    (hJ : P.free.card = 2) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (blockSL (K := K) P.free))
    (hβbar : ∀ s : blockSL (K := K) P.free,
      ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K)
    (κ : blockSL (K := K) P.free ≃* SpecialLinearGroup (Fin 2) K) :
    sl2FieldPart K (MulAut.congr κ βbar) = linearFieldPart K hn β := by
  have hlt : P.free.card < n := by have := P.card_free; omega
  set ε : P.free ≃ Fin 2 := P.free.equivFin.trans (finCongr hJ) with hε
  obtain ⟨σ, A, e, he, hβeq⟩ := ProjectivePlane.exists_standard_form K n hn β
  rw [hβeq, linearFieldPart_eq hn he]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [P.mulAutHom_congr_eq_of_twist hq hk (by omega) hlt ε (sl2FieldPart K)
      (sl2FieldPart_slConjugation K) β hβ βbar hβbar κ A (fieldAut n K σ)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ)
      (by rw [hβeq, pow_zero, mul_one]) (fun x hx => P.fieldAut_mem_radicalP σ hx)
      (fun x => by rw [fieldAut_proj_blockEmbed]; rfl), sl2FieldPart_slFieldAut]
  · rw [P.mulAutHom_congr_eq_of_twist hq hk (by omega) hlt ε (sl2FieldPart K)
      (sl2FieldPart_slConjugation K) β hβ βbar hβbar κ (A * (P.outerSwapGL K)⁻¹)
      (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 2 K)
      (by rw [hβeq, pow_one, map_mul, map_inv]; group)
      (fun x hx => P.graphTwist_mem_radicalP σ hx)
      (fun x => by rw [P.graphTwist_proj_blockEmbed, ← map_inv]; rfl),
      map_mul, sl2FieldPart_slFieldAut, sl2FieldPart_slGraphAut, mul_one]

end RC

end InvPlacement

end CFSG.SeitzReduction.LinearPilot

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore)

variable {n k k' : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem fieldRigidIn_inner_of_card_free_eq_two (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (P : InvPlacement n k) (P' : InvPlacement n k') (hP : P.elt K ≠ 1) (hP' : P'.elt K ≠ 1)
    (hJ : P.free.card = 2) (hJ' : P'.free.card = 2) :
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  have hk' : 0 < k' := Nat.pos_of_ne_zero fun h => hP' (P'.elt_eq_one_of_eq_zero h)
  have hJ2 : 2 ≤ P.free.card := hJ.ge
  have hJ'2 : 2 ≤ P'.free.card := hJ'.ge
  have hc₁ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₁).map (MulAut.conj γ).toMonoidHom = (X.map β₁.toMonoidHom).map φ₁ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₁ x).symm
  have hc₂ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₂).map (MulAut.conj γ).toMonoidHom = (X.map β₂.toMonoidHom).map φ₂ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₂ x).symm
  have hβ₁Λ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β₁.toMonoidHom = perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have hβ₂Λ : (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))).map
      β₂.toMonoidHom = perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K))) := by
    apply Subgroup.map_injective hφ₂
    rw [← hc₂, ← hX, hc₁, hβ₁Λ]
  have hQ := map_radicalP_eq hq hφ₁ hφ₂ P P' hJ2 hJ'2 hX
  obtain ⟨-, hSN, hQS, hQS', hSS'⟩ := complements_map_blockSL hq hφ₁ hφ₂ P P' hJ2 hJ'2 hX
  obtain ⟨-, hS'N, -, -, -⟩ := complements_map_blockSL hq hφ₂ hφ₁ P' P hJ'2 hJ2 hX.symm
  rw [hQ] at hS'N
  have hγQ : ((P.radicalP K).map φ₁).map (MulAut.conj γ).toMonoidHom =
      (P.radicalP K).map φ₁ := by
    rw [hc₁, P.map_radicalP_eq_of_map_eq hq hJ2 β₁ hβ₁Λ]
  have hγM : ((P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P.free).map φ₁).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P.free).map φ₁ := by
    rw [← Subgroup.map_sup, hc₁, P.map_radicalP_sup_blockSL_eq_of_map_eq hq hJ2 β₁ hβ₁Λ]
  have hγM' : ((P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P'.free).map φ₂).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P'.free).map φ₂ := by
    rw [← hSS']
    exact hγM
  obtain ⟨γ₁, hγ₁⟩ := exists_mulAut_complement hSN hQS γ hγQ hγM
  obtain ⟨γ₂, hγ₂⟩ := exists_mulAut_complement hS'N hQS' γ hγQ hγM'
  have hint := complement_intertwine hSN hQS hQS' hSS' hγQ γ₁ γ₂ hγ₁ hγ₂
  have hlt : P.free.card < n := by have := P.card_free; omega
  have hlt' : P'.free.card < n := by have := P'.card_free; omega
  obtain ⟨κ₁⟩ := blockSL_mulEquiv (K := K) hlt
  obtain ⟨κ₂⟩ := blockSL_mulEquiv (K := K) hlt'
  set κ₁' := κ₁.trans (reindexSpecialLinear (K := K) (finCongr hJ)) with hκ₁'
  set κ₂' := κ₂.trans (reindexSpecialLinear (K := K) (finCongr hJ')) with hκ₂'
  set e₁ := (blockSL (K := K) P.free).equivMapOfInjective φ₁ hφ₁ with he₁
  set e₂ := (blockSL (K := K) P'.free).equivMapOfInjective φ₂ hφ₂ with he₂
  set βbar₁ : MulAut (blockSL (K := K) P.free) := e₁.trans (γ₁.trans e₁.symm) with hβbar₁
  set βbar₂ : MulAut (blockSL (K := K) P'.free) := e₂.trans (γ₂.trans e₂.symm) with hβbar₂
  have hcond₁ : ∀ s : blockSL (K := K) P.free,
      ((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β₁ s ∈ P.radicalP K := by
    intro s
    have he : φ₁ ((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K) =
        ((γ₁ (e₁ s) : (blockSL (K := K) P.free).map φ₁) : Γ) := by
      have : e₁ (βbar₁ s) = γ₁ (e₁ s) := by
        rw [hβbar₁, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₁ (((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β₁ s) ∈
        (P.radicalP K).map φ₁ := by
      rw [map_mul, map_inv, he, h₁]
      exact hγ₁ (e₁ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₁ hqe]
    exact hq'
  have hcond₂ : ∀ s : blockSL (K := K) P'.free,
      ((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K)⁻¹ * β₂ s ∈ P'.radicalP K := by
    intro s
    have he : φ₂ ((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K) =
        ((γ₂ (e₂ s) : (blockSL (K := K) P'.free).map φ₂) : Γ) := by
      have : e₂ (βbar₂ s) = γ₂ (e₂ s) := by
        rw [hβbar₂, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₂ (((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K)⁻¹ * β₂ s) ∈
        (P'.radicalP K).map φ₂ := by
      rw [map_mul, map_inv, he, h₂, hQ]
      exact hγ₂ (e₂ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₂ hqe]
    exact hq'
  have hF₁ := P.sl2FieldPart_eq_of_card_free_eq_two hq hn hk hJ β₁ hβ₁Λ βbar₁ hcond₁ κ₁'
  have hF₂ := P'.sl2FieldPart_eq_of_card_free_eq_two hq hn hk' hJ' β₂ hβ₂Λ βbar₂ hcond₂ κ₂'
  have hT := mulAutHom_congr_eq_of_intertwine (sl2FieldPart K) (sl2FieldPart_mul_comm K)
    (e₁.symm.trans κ₁') (e₂.symm.trans κ₂') (EPilot.mulEquivOfComplements hSN hQS hQS' hSS')
    γ₁ γ₂ hint
  have hA : MulAut.congr κ₁' βbar₁ = MulAut.congr (e₁.symm.trans κ₁') γ₁ := by
    ext A
    rfl
  have hB : MulAut.congr κ₂' βbar₂ = MulAut.congr (e₂.symm.trans κ₂') γ₂ := by
    ext A
    rfl
  rw [← hF₁, ← hF₂, hA, hB, hT]

theorem fieldRigidIn_inner_of_two_le_or (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (P : InvPlacement n k) (P' : InvPlacement n k') (hP : P.elt K ≠ 1) (hP' : P'.elt K ≠ 1)
    (hJ : 2 ≤ P.free.card ∨ 2 ≤ P'.free.card) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  have hk' : 0 < k' := Nat.pos_of_ne_zero fun h => hP' (P'.elt_eq_one_of_eq_zero h)
  have h2 : 2 ≤ P.free.card ∧ 2 ≤ P'.free.card := by
    rcases hJ with hJ | hJ
    · exact ⟨hJ, two_le_card_free_of_map_perfectCore_eq hq hn hφ₁ hφ₂ P P' hk hJ hX⟩
    · exact ⟨two_le_card_free_of_map_perfectCore_eq hq hn hφ₂ hφ₁ P' P hk' hJ hX.symm, hJ⟩
  have hcard := card_free_eq_of_map_perfectCore_eq hq hφ₁ hφ₂ P P' hk hk' h2.1 h2.2 hX
  rcases (by omega : P.free.card = 2 ∨ 3 ≤ P.free.card) with h | h
  · exact fieldRigidIn_inner_of_card_free_eq_two hq (Nat.le_of_succ_le hn) P P' hP hP' h
      (hcard ▸ h) Γ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  · exact fieldRigidIn_inner_of_three_le hq (Nat.le_of_succ_le hn) P P' hP hP' h (hcard ▸ h)
      Γ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂

end CFSG.SeitzReduction.LinearPilot
