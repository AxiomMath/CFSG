module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltRC

public section

namespace CFSG.SeitzReduction.LinearPilot

namespace Nonalt

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.Quasithin (perfectCore perfectCore_le map_perfectCore)

variable {n : ℕ} {K : Type} [Field K]

section General

theorem levi0_row {i : Fin n} {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ levi0 i) (j : Fin n) :
    (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  have hT : (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single i 1 = Pi.single i 1 := by
    calc (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single i 1
        = (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ
            Pi.single i 1) := by rw [hA.2]
      _ = Pi.single i 1 := by rw [mulVec_mulVec, hA.1, one_mulVec]
  have h := congrFun hT j
  rw [mulVec_single_one, col_apply, transpose_apply] at h
  rw [h, Pi.single_apply, one_apply]
  simp only [eq_comm]

theorem proj_injOn_levi0 {i : Fin n} {A B : SpecialLinearGroup (Fin n) K} (hA : A ∈ levi0 i)
    (hB : B ∈ levi0 i) (h : proj n K A = proj n K B) : A = B := by
  obtain ⟨l, -, hl⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  have hAB : A⁻¹ * B ∈ levi0 i := mul_mem (inv_mem hA) hB
  have he := hAB.2
  rw [hl, scalar_apply] at he
  have hl1 : (l : K) = 1 := by
    have h2 := congrFun he i
    rw [mulVec_diagonal, Pi.single_eq_same, mul_one] at h2
    exact h2
  have h3 : A⁻¹ * B = 1 := by
    apply Subtype.ext
    rw [hl, hl1, map_one]
    rfl
  rw [← mul_inv_cancel_left A B, h3, mul_one]

variable (K) in
@[expose] noncomputable def leviEquiv0 (i : Fin n) : levi0 (K := K) i ≃* levi (K := K) i :=
  MulEquiv.ofBijective (((proj n K).comp (levi0 (K := K) i).subtype).codRestrict (levi i)
    fun A => ⟨A, A.2, rfl⟩)
    ⟨fun A B h => Subtype.ext (proj_injOn_levi0 A.2 B.2 (congrArg Subtype.val h)),
      fun ⟨_, A, hA, rfl⟩ => ⟨⟨A, hA⟩, rfl⟩⟩

theorem map_mem_levi0 {i : Fin n} (σ : K ≃+* K) {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ levi0 i) : SpecialLinearGroup.map σ.toRingHom A ∈ levi0 i := by
  refine ⟨?_, ?_⟩
  · change ((A : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (A : Matrix (Fin n) (Fin n) K).map σ = 1
    rw [← transpose_map, ← Matrix.map_mul, hA.1]
    ext a b
    rw [Matrix.map_apply, one_apply]
    split_ifs <;> simp
  · change (A : Matrix (Fin n) (Fin n) K).map σ *ᵥ Pi.single i 1 = Pi.single i 1
    rw [mulVec_single_one]
    funext j
    have h := congrFun hA.2 j
    rw [mulVec_single_one, col_apply] at h
    rw [col_apply, Matrix.map_apply, h, Pi.single_apply]
    split_ifs <;> simp

theorem fieldAut_mem_levi {i : Fin n} (σ : K ≃+* K) {x : projectiveSL n K}
    (hx : x ∈ levi (K := K) i) : fieldAut n K σ x ∈ levi (K := K) i := by
  obtain ⟨A, hA, rfl⟩ := hx
  rw [fieldAut_proj]
  exact ⟨_, map_mem_levi0 σ hA, rfl⟩

theorem map_perfectCore_autFix_of_commute [Finite K] {α : MulAut (projectiveSL n K)}
    (hα : Commute α (dualAut n K)) :
    (perfectCore (autFixSubgroup (dualAut n K))).map α.toMonoidHom =
      perfectCore (autFixSubgroup (dualAut n K)) := by
  have hX : (autFixSubgroup (dualAut n K)).map α.toMonoidHom = autFixSubgroup (dualAut n K) := by
    have hle : ∀ β : MulAut (projectiveSL n K), Commute β (dualAut n K) →
        (autFixSubgroup (dualAut n K)).map β.toMonoidHom ≤ autFixSubgroup (dualAut n K) := by
      rintro β hβ _ ⟨x, hx, rfl⟩
      have hx' : dualAut n K x = x := hx
      change dualAut n K (β x) = β x
      rw [← MulAut.mul_apply, ← hβ.eq, MulAut.mul_apply, hx']
    refine le_antisymm (hle α hα) ?_
    intro x hx
    refine ⟨α⁻¹ x, hle α⁻¹ hα.inv_left ⟨x, hx, rfl⟩, ?_⟩
    change α (α⁻¹ x) = x
    rw [MulAut.apply_inv_self]
  rw [map_perfectCore, hX]

end General

section Four

variable (K) in
@[expose] def selS : Matrix (Fin 2) (Fin 4) K := !![0, 1, 0, 0; 0, 0, 0, 1]

variable (K) in
@[expose] def selT : Matrix (Fin 4) (Fin 2) K := !![0, 0; 1, 0; 1, 1; 0, 1]

theorem selS_mul_selT : selS K * selT K = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [selS, selT, Matrix.mul_apply, Fin.sum_univ_four]

theorem selT_transpose_mul_selT [CharP K 2] : (selT K)ᵀ * selT K = !![0, 1; 1, 0] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [selT, Matrix.mul_apply, Fin.sum_univ_four, h2]

theorem selT_selS_mulVec [CharP K 2] {y : Fin 4 → K} (h0 : y 0 = 0)
    (hs : onesVec ⬝ᵥ y = 0) : selT K *ᵥ (selS K *ᵥ y) = y := by
  have hs' : y 1 + y 2 + y 3 = 0 := by
    have := hs
    simp only [dotProduct, Fin.sum_univ_four, onesVec_apply, one_mul, h0, zero_add] at this
    exact this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext j
  fin_cases j
  · simp [selS, selT, mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two, h0]
  · simp [selS, selT, mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]
  · simp [selS, selT, mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]
    linear_combination hs' - y 2 * h2
  · simp [selS, selT, mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]

theorem selT_selS_mul_mul_selT [CharP K 2] {A : SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ levi0 (0 : Fin 4)) :
    selT K * selS K * ((A : Matrix (Fin 4) (Fin 4) K) * selT K) =
      (A : Matrix (Fin 4) (Fin 4) K) * selT K := by
  ext j c
  have hcol : ∀ X : Matrix (Fin 4) (Fin 2) K, (selT K * selS K * X) j c =
      (selT K *ᵥ (selS K *ᵥ fun k => X k c)) j := by
    intro X
    rw [mulVec_mulVec]
    rfl
  rw [hcol]
  have hy0 : (fun k => ((A : Matrix (Fin 4) (Fin 4) K) * selT K) k c) 0 = 0 := by
    change ((A : Matrix (Fin 4) (Fin 4) K) * selT K) 0 c = 0
    rw [Matrix.mul_apply, Fin.sum_univ_four, levi0_row hA, levi0_row hA, levi0_row hA,
      levi0_row hA]
    fin_cases c <;> simp [selT]
  have hys : onesVec ⬝ᵥ (fun k => ((A : Matrix (Fin 4) (Fin 4) K) * selT K) k c) = 0 := by
    have e : (fun k => ((A : Matrix (Fin 4) (Fin 4) K) * selT K) k c) =
        (A : Matrix (Fin 4) (Fin 4) K) *ᵥ fun k => selT K k c := rfl
    rw [e, onesVec_dotProduct_orth hA.1]
    fin_cases c <;> simp [selT, dotProduct, Fin.sum_univ_four, onesVec_apply,
      CharTwo.add_self_eq_zero]
  rw [selT_selS_mulVec hy0 hys]

theorem det_selS_mul_selT [CharP K 2] {A : SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ levi0 (0 : Fin 4)) :
    (selS K * (A : Matrix (Fin 4) (Fin 4) K) * selT K).det = 1 := by
  set M := selS K * (A : Matrix (Fin 4) (Fin 4) K) * selT K with hM
  have hTM : selT K * M = (A : Matrix (Fin 4) (Fin 4) K) * selT K := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (selT K), selT_selS_mul_mul_selT hA]
  have hJ : Mᵀ * !![0, 1; 1, 0] * M = !![0, 1; 1, 0] := by
    calc Mᵀ * !![0, 1; 1, 0] * M = Mᵀ * ((selT K)ᵀ * selT K) * M := by
          rw [selT_transpose_mul_selT]
      _ = (selT K * M)ᵀ * (selT K * M) := by
          rw [Matrix.transpose_mul (selT K) M]
          simp only [Matrix.mul_assoc]
      _ = ((A : Matrix (Fin 4) (Fin 4) K) * selT K)ᵀ * ((A : Matrix (Fin 4) (Fin 4) K) *
            selT K) := by rw [hTM]
      _ = (selT K)ᵀ * ((A : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K)) *
            selT K := by
          rw [Matrix.transpose_mul (A : Matrix (Fin 4) (Fin 4) K) (selT K)]
          simp only [Matrix.mul_assoc]
      _ = !![0, 1; 1, 0] := by rw [hA.1, Matrix.mul_one, selT_transpose_mul_selT]
  have h01 := congrFun (congrFun hJ 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [det_fin_two]
  linear_combination h01 - (M 0 1 * M 1 0) * h2

variable [CharP K 2]

variable (K) in
@[expose] def kappa0 : levi0 (K := K) (0 : Fin 4) →* SpecialLinearGroup (Fin 2) K where
  toFun A := ⟨selS K * ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K,
    det_selS_mul_selT A.2⟩
  map_one' := by
    apply Subtype.ext
    change selS K * ((1 : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, selS_mul_selT]
  map_mul' A B := by
    apply Subtype.ext
    change selS K * (((A : SpecialLinearGroup (Fin 4) K) * (B : SpecialLinearGroup (Fin 4) K) :
      SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K =
        (selS K * ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K) *
          (selS K * ((B : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    calc selS K * (((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((B : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * selT K
        = selS K * ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (((B : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * selT K) := by
          simp only [Matrix.mul_assoc]
      _ = selS K * ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (selT K * selS K * (((B : SpecialLinearGroup (Fin 4) K) :
              Matrix (Fin 4) (Fin 4) K) * selT K)) := by rw [selT_selS_mul_mul_selT B.2]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem kappa0_injective : Function.Injective (kappa0 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  set B : Matrix (Fin 4) (Fin 4) K := ((A : SpecialLinearGroup (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) with hB
  have hM : selS K * B * selT K = 1 := congrArg Subtype.val hA
  have hAT : B * selT K = selT K := by
    rw [← selT_selS_mul_mul_selT A.2, Matrix.mul_assoc (selT K), ← Matrix.mul_assoc (selS K),
      hM, Matrix.mul_one]
  have hw : ∀ c : Fin 2, B *ᵥ (fun k => selT K k c) = fun k => selT K k c :=
    fun c => funext fun j => congrFun (congrFun hAT j) c
  have he0 : B *ᵥ Pi.single (0 : Fin 4) (1 : K) = Pi.single 0 1 := A.2.2
  have hd : B *ᵥ onesVec = onesVec := mulVec_onesVec_orth A.2.1
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have e1 : Pi.single (1 : Fin 4) (1 : K) =
      onesVec + Pi.single 0 1 + fun k => selT K k 1 := by
    funext j
    fin_cases j <;> simp [selT, onesVec_apply, h11]
  have e2 : Pi.single (2 : Fin 4) (1 : K) = Pi.single 1 1 + fun k => selT K k 0 := by
    funext j
    fin_cases j <;> simp [selT, h11]
  have e3 : Pi.single (3 : Fin 4) (1 : K) = Pi.single 2 1 + fun k => selT K k 1 := by
    funext j
    fin_cases j <;> simp [selT, h11]
  have f1 : B *ᵥ Pi.single (1 : Fin 4) (1 : K) = Pi.single 1 1 := by
    rw [e1, mulVec_add, mulVec_add, hd, he0, hw]
  have f2 : B *ᵥ Pi.single (2 : Fin 4) (1 : K) = Pi.single 2 1 := by
    rw [e2, mulVec_add, f1, hw, ← e2]
  have f3 : B *ᵥ Pi.single (3 : Fin 4) (1 : K) = Pi.single 3 1 := by
    rw [e3, mulVec_add, f2, hw, ← e3]
  have hall : ∀ k : Fin 4, B *ᵥ Pi.single k (1 : K) = Pi.single k 1 := by
    intro k
    fin_cases k
    · exact he0
    · exact f1
    · exact f2
    · exact f3
  apply Subtype.ext
  apply Subtype.ext
  change B = 1
  ext j k
  have h := congrFun (hall k) j
  rw [mulVec_single_one, col_apply] at h
  rw [h, Pi.single_apply, one_apply]

theorem kappa0_map (σ : K ≃+* K) (A : levi0 (K := K) (0 : Fin 4)) :
    kappa0 K ⟨SpecialLinearGroup.map σ.toRingHom A, map_mem_levi0 σ A.2⟩ =
      CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K σ (kappa0 K A) := by
  apply Subtype.ext
  ext a b
  rw [CFSG.RankThree.PartOne.KCRootAxis.slFieldAut_apply]
  change (selS K * ((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ *
    selT K) a b = σ ((selS K * ((A : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) * selT K) a b)
  have hS : (selS K).map σ = selS K := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [selS]
  have hT : (selT K).map σ = selT K := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [selT]
  rw [← Matrix.map_apply (f := σ), Matrix.map_mul, Matrix.map_mul, hS, hT]

variable [Finite K]

omit [Finite K] in
theorem card_levi0_four :
    Nat.card (levi0 (K := K) (0 : Fin 4)) = Nat.card (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨e⟩ := nonempty_levi_mulEquiv_statedSp (K := K) (n := 4) (r := 1) rfl 0
  rw [Nat.card_congr (leviEquiv0 K 0).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).toEquiv]

variable (K) in
@[expose] noncomputable def kappa : levi (K := K) (0 : Fin 4) ≃* SpecialLinearGroup (Fin 2) K :=
  (leviEquiv0 K 0).symm.trans (MulEquiv.ofBijective (kappa0 K)
    (kappa0_injective.bijective_of_nat_card_le card_levi0_four.ge))

theorem kappa_fieldAut (σ : K ≃+* K) (s : levi (K := K) (0 : Fin 4)) :
    kappa K ⟨fieldAut 4 K σ s, fieldAut_mem_levi σ s.2⟩ =
      CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K σ (kappa K s) := by
  obtain ⟨A, rfl⟩ := (leviEquiv0 K 0).surjective s
  have h : (⟨fieldAut 4 K σ (leviEquiv0 K 0 A : levi (K := K) 0), fieldAut_mem_levi σ (leviEquiv0
      K 0 A).2⟩ : levi (K := K) (0 : Fin 4)) =
        leviEquiv0 K 0 ⟨SpecialLinearGroup.map σ.toRingHom A, map_mem_levi0 σ A.2⟩ := by
    apply Subtype.ext
    exact fieldAut_proj σ _
  rw [h, kappa, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply,
    kappa0_map]

omit [CharP K 2] in
theorem sl2FieldPart_slFieldAut' (σ : K ≃+* K) :
    sl2FieldPart K (CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K σ) = σ := by
  have h : CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K σ =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ := by
    ext A i j
    rfl
  rw [h, sl2FieldPart_slFieldAut]

theorem sl2FieldPart_congr_kappa {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (β : MulAut (projectiveSL 4 K)) (βbar : MulAut (levi (K := K) (0 : Fin 4)))
    (hβbar : ∀ s : levi (K := K) (0 : Fin 4),
      ((βbar s : levi (K := K) 0) : projectiveSL 4 K)⁻¹ * β s ∈ coreRadical K (0 : Fin 4)) :
    sl2FieldPart K (MulAut.congr (kappa K) βbar) = linearFieldPart K (by norm_num) β := by
  obtain ⟨M, τ, hθ⟩ :=
    CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut (MulAut.congr (kappa K) βbar)
  have hτ : sl2FieldPart K (MulAut.congr (kappa K) βbar) = τ := by
    rw [hθ, map_mul, sl2FieldPart_conj, one_mul, sl2FieldPart_slFieldAut']
  rw [hτ]
  set ℓ : levi (K := K) (0 : Fin 4) := (kappa K).symm M with hℓ
  obtain ⟨-, -, -, -, -, hLN, -⟩ := coreRadical_spec (K := K) hK hq (n := 4) (r := 1) rfl le_rfl 0
  have hβbar' : ∀ s : levi (K := K) (0 : Fin 4),
      βbar s = ℓ * ⟨fieldAut 4 K τ s, fieldAut_mem_levi τ s.2⟩ * ℓ⁻¹ := by
    intro s
    apply (kappa K).injective
    have h1 : kappa K (βbar s) = MulAut.congr (kappa K) βbar (kappa K s) := by
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h1, hθ, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, kappa_fieldAut,
      hℓ, MulEquiv.apply_symm_apply]
  have hfQ : ∀ x ∈ coreRadical K (0 : Fin 4), fieldAut 4 K τ⁻¹ x ∈ coreRadical K (0 : Fin 4) := by
    intro x hx
    have h := map_coreRadical_eq_of_map_eq (K := K) hK hq (n := 4) (r := 1) rfl le_rfl 0
      (fieldAut 4 K τ⁻¹) (map_perfectCore_autFix_of_commute
        (CFSG.ComponentClassification.UnbalancedCatalog.fieldAut_commute_dualAut τ⁻¹))
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hab : (1 : Fin 4) ≠ 2 := by decide
  have hia : (0 : Fin 4) ≠ 1 := by decide
  have hib : (0 : Fin 4) ≠ 2 := by decide
  have hαt : ∀ c : K,
      (transElt (Pi.single 1 1 + Pi.single 2 1) (onesVec_dotProduct_pairVec 1 2) c)⁻¹ *
        ((MulAut.conj (ℓ : projectiveSL 4 K) * fieldAut 4 K τ)⁻¹ * β)
          (transElt (Pi.single 1 1 + Pi.single 2 1) (onesVec_dotProduct_pairVec 1 2) c) ∈
        radical (K := K) (0 : Fin 4) := by
    intro c
    set t := transElt (Pi.single (1 : Fin 4) (1 : K) + Pi.single 2 1)
      (onesVec_dotProduct_pairVec 1 2) c with ht
    have htL : t ∈ levi (K := K) (0 : Fin 4) := transElt_mem_levi _ (by simp) c
    set q := ((βbar ⟨t, htL⟩ : levi (K := K) 0) : projectiveSL 4 K)⁻¹ * β t with hq'
    have hqQ : q ∈ coreRadical K (0 : Fin 4) := hβbar ⟨t, htL⟩
    set w := (ℓ : projectiveSL 4 K)⁻¹ * q * ℓ with hw
    have hwQ : w ∈ coreRadical K (0 : Fin 4) := by
      have hℓN := hLN (ℓ⁻¹).2
      rw [mem_normalizer_iff] at hℓN
      have := (hℓN q).1 hqQ
      simpa [hw] using this
    have hβt : β t = (ℓ : projectiveSL 4 K) * fieldAut 4 K τ t * (ℓ : projectiveSL 4 K)⁻¹ *
        (ℓ * w * (ℓ : projectiveSL 4 K)⁻¹) := by
      have e1 : β t = ((βbar ⟨t, htL⟩ : levi (K := K) 0) : projectiveSL 4 K) * q := by
        rw [hq', mul_inv_cancel_left]
      rw [e1, hβbar' ⟨t, htL⟩, hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hαt' : ((MulAut.conj (ℓ : projectiveSL 4 K) * fieldAut 4 K τ)⁻¹ * β) t =
        t * fieldAut 4 K τ⁻¹ w := by
      rw [MulAut.mul_apply, _root_.mul_inv_rev, MulAut.mul_apply, hβt, MulAut.conj_inv_apply]
      have e : (ℓ : projectiveSL 4 K)⁻¹ * ((ℓ : projectiveSL 4 K) * fieldAut 4 K τ t *
          (ℓ : projectiveSL 4 K)⁻¹ * (ℓ * w * (ℓ : projectiveSL 4 K)⁻¹)) * ℓ =
            fieldAut 4 K τ t * w := by
        group
      rw [e, map_mul, MulAut.inv_apply_self, ← map_inv]
    rw [hαt', inv_mul_cancel_left]
    exact (hfQ w hwQ).2
  have hfc := linearFieldPart_eq_one_of_mem_radical (n := 4) ⟨2, rfl⟩ (by norm_num) hab hia hib _
    hαt
  rw [map_mul, map_inv, map_mul, linearFieldPart_mulAut_conj, one_mul, linearFieldPart_fieldAut,
    inv_mul_eq_one] at hfc
  exact hfc

end Four

end Nonalt

end CFSG.SeitzReduction.LinearPilot
