module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LargeExtraspecial.A2ModSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

section OrthTransvection

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem kgl34_neg_eq_self {n : ℕ} {F : Type*} [Field F] [CharP F 2] (φ : Fin n → F) : -φ = φ := by
  funext j
  exact CharTwo.neg_eq (φ j)

theorem kgl34_tv_inv_self {n : ℕ} {F : Type*} [Field F] [CharP F 2] {v φ : Fin n → F}
    (h : φ ⬝ᵥ v = 0) :
    (CFSG.LargeExtraspecial.A2Mod.tv v φ)⁻¹ = CFSG.LargeExtraspecial.A2Mod.tv v φ := by
  rw [CFSG.LargeExtraspecial.A2Mod.tv_inv h, kgl34_neg_eq_self]

theorem kgl34_single_vecMul {n : ℕ} {F : Type*} [Field F] (N : Matrix (Fin n) (Fin n) F)
    (p : Fin n) : (Pi.single p (1 : F) : Fin n → F) ᵥ* N = fun j => N p j := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem kgl34_matrix_key {n : ℕ} {F : Type*} [Field F] (M N : Matrix (Fin n) (Fin n) F)
    (hMN : M * N = 1) (hMT : Mᵀ = M) (v φ : Fin n → F) (c : F) (hφ : φ = c • (v ᵥ* N)) :
    M * (1 + Matrix.vecMulVec φ v) * N = 1 + Matrix.vecMulVec v φ := by
  have hNt : Nᵀ * M = 1 := by
    have h := congrArg Matrix.transpose hMN
    rwa [Matrix.transpose_mul, hMT, Matrix.transpose_one] at h
  have hNs : Nᵀ = N := by
    calc Nᵀ = Nᵀ * (M * N) := by rw [hMN, mul_one]
      _ = (Nᵀ * M) * N := by rw [mul_assoc]
      _ = N := by rw [hNt, one_mul]
  have hvN : v ᵥ* N = N *ᵥ v := by
    rw [← Matrix.mulVec_transpose, hNs]
  have hMφ : M *ᵥ φ = c • v := by
    rw [hφ, Matrix.mulVec_smul, hvN, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hMN, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, hMφ, Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul, ← hφ]

theorem orth_transvection_fixed {n : ℕ} {F : Type*} [Field F] [CharP F 2] (C : GL (Fin n) F)
    (p : Fin n) (c : F)
    (hC : ∀ i j, (C : Matrix (Fin n) (Fin n) F) i j = (C : Matrix (Fin n) (Fin n) F) j i)
    (hp : ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p p = 0) :
    (conjAut n F C * dualAut n F) (proj n F (CFSG.LargeExtraspecial.A2Mod.tv (Pi.single p 1)
      (c • fun j => ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p j))) =
    proj n F (CFSG.LargeExtraspecial.A2Mod.tv (Pi.single p 1)
      (c • fun j => ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p j)) := by
  have hMN : ((C : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := Units.mul_inv C
  have hMT : (((C : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))ᵀ =
      ((C : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    ext i j
    exact hC j i
  have hφ : c • (fun j => ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p j) =
      c • ((Pi.single p (1 : F) : Fin n → F) ᵥ*
        ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
    rw [kgl34_single_vecMul]
  have hφv : (c • fun j => ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p j) ⬝ᵥ
      (Pi.single p (1 : F) : Fin n → F) = 0 := by
    rw [dotProduct_single]
    simp only [Pi.smul_apply, smul_eq_mul, hp, mul_zero, mul_one]
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  refine congrArg (proj n F) ?_
  apply Subtype.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
    Matrix.SpecialLinearGroup.coe_transpose, kgl34_tv_inv_self hφv,
    CFSG.LargeExtraspecial.A2Mod.coe_tv hφv, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]
  exact kgl34_matrix_key _ _ hMN hMT _ _ c hφ

end OrthTransvection

section SteinbergStep

open Matrix Subgroup CFSG.LargeExtraspecial.A2Mod

theorem transvection_row_mem_of_tv {n : ℕ} {F : Type*} [Field F]
    (H : Subgroup (SpecialLinearGroup (Fin n) F)) (p j₀ k : Fin n) (hpj : p ≠ j₀) (hpk : p ≠ k)
    (hjk : j₀ ≠ k) (r : Fin n → F) (hrp : r p = 0) (hrj : r j₀ ≠ 0)
    (h1 : SpecialLinearGroup.transvection hjk (1 : F) ∈ H)
    (hX : ∀ c : F, tv (Pi.single p 1) (c • r) ∈ H) (c : F) :
    SpecialLinearGroup.transvection hpk c ∈ H := by
  have hsingle : ∀ (i : Fin n) (x : F), (Pi.single i x : Fin n → F) = x • Pi.single i 1 := by
    intro i x
    funext a
    by_cases ha : a = i <;> simp [ha]
  have hg : SpecialLinearGroup.transvection hjk (1 : F) = tv (Pi.single j₀ 1) (Pi.single k 1) :=
    transvection_eq_tv hjk 1
  have hkj : (Pi.single k (1 : F) : Fin n → F) ⬝ᵥ Pi.single j₀ 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hjk.symm]
  have hkp : ∀ x : F, (Pi.single k x : Fin n → F) ⬝ᵥ Pi.single p 1 = 0 := by
    intro x
    rw [single_dotProduct, Pi.single_eq_of_ne hpk.symm, mul_zero]
  have hdp : ∀ d : F, (d • r) ⬝ᵥ Pi.single p 1 = 0 := by
    intro d
    simp [smul_dotProduct, dotProduct_single, hrp]
  have hdj : ∀ d : F, (d • r) ⬝ᵥ Pi.single j₀ 1 = d * r j₀ := by
    intro d
    simp [smul_dotProduct, dotProduct_single]
  have hgp : ((tv (Pi.single j₀ 1) (Pi.single k 1) : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) *ᵥ Pi.single p 1 = Pi.single p 1 := by
    rw [tv_mulVec hkj, hkp 1, zero_smul, add_zero]
  have hTpk : ∀ d : F, SpecialLinearGroup.transvection hpk (-(d * r j₀)) =
      tv (Pi.single p 1) (Pi.single k (-(d * r j₀))) := fun d => transvection_eq_tv' hpk _
  have hconj : ∀ d : F, SpecialLinearGroup.transvection hjk (1 : F) *
      tv (Pi.single p 1) (d • r) * (SpecialLinearGroup.transvection hjk (1 : F))⁻¹ =
      tv (Pi.single p 1) (d • r) * SpecialLinearGroup.transvection hpk (-(d * r j₀)) := by
    intro d
    rw [hg, conj_tv, hgp, hTpk d, contra_tv hkj, hdj d, tv_mul_tv_left (hdp d) (hkp _)]
    congr 1
    rw [hsingle k (-(d * r j₀)), neg_smul, sub_eq_add_neg]
  have key : ∀ d : F, SpecialLinearGroup.transvection hpk (-(d * r j₀)) ∈ H := by
    intro d
    have hT : SpecialLinearGroup.transvection hpk (-(d * r j₀)) =
        (tv (Pi.single p 1) (d • r))⁻¹ * (SpecialLinearGroup.transvection hjk (1 : F) *
          tv (Pi.single p 1) (d • r) * (SpecialLinearGroup.transvection hjk (1 : F))⁻¹) := by
      rw [hconj d, inv_mul_cancel_left]
    rw [hT]
    exact H.mul_mem (H.inv_mem (hX d)) (H.mul_mem (H.mul_mem h1 (hX d)) (H.inv_mem h1))
  have hcd : -((-c / r j₀) * r j₀) = c := by
    rw [div_mul_cancel₀ (-c) hrj, neg_neg]
  have hfin := key (-c / r j₀)
  rw [hcd] at hfin
  exact hfin

end SteinbergStep

section SteinbergGenerate

open Matrix Subgroup

open scoped commutatorElement in
theorem kgl34_commutator_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem eq_top_of_row_transvections {n : ℕ} (hn : 3 ≤ n) {F : Type*} [Field F]
    (H : Subgroup (SpecialLinearGroup (Fin n) F)) (p : Fin n)
    (h1 : ∀ a b : Fin n, ∀ hab : a ≠ b, SpecialLinearGroup.transvection hab (1 : F) ∈ H)
    (hrow : ∀ (l : Fin n) (hpl : p ≠ l) (c : F), SpecialLinearGroup.transvection hpl c ∈ H) :
    H = ⊤ := by
  have hex : ∀ a b : Fin n, ∃ l : Fin n, l ≠ a ∧ l ≠ b := by
    intro a b
    by_contra hcon
    have hcon' : ∀ l : Fin n, l ≠ a → l = b := fun l hl => by
      by_contra hlb
      exact hcon ⟨l, hl, hlb⟩
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n)) := by
      intro l _
      by_cases hla : l = a
      · rw [hla]; simp
      · rw [hcon' l hla]; simp
    have hcard := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hcore : ∀ (i j : Fin n) (hij : i ≠ j), i ≠ p → j ≠ p → ∀ c : F,
      SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij hip hjp c
    have hpj : p ≠ j := fun h => hjp h.symm
    have key := Matrix.SpecialLinearGroup.commutatorElement_transvection hip hpj hij (1 : F) c
    rw [one_mul] at key
    rw [← key]
    exact kgl34_commutator_mem H (h1 i p hip) (hrow j hpj c)
  have hall : ∀ (i j : Fin n) (hij : i ≠ j) (c : F),
      SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    by_cases hip : i = p
    · subst hip
      exact hrow j hij c
    · by_cases hjp : j = p
      · obtain ⟨l, hli, hlp⟩ := hex i p
        have hil : i ≠ l := fun h => hli h.symm
        have hA : SpecialLinearGroup.transvection hil c ∈ H := hcore i l hil hip hlp c
        have hB : SpecialLinearGroup.transvection hlp (1 : F) ∈ H := h1 l p hlp
        have key := Matrix.SpecialLinearGroup.commutatorElement_transvection hil hlp hip c (1 : F)
        rw [mul_one] at key
        subst hjp
        rw [← key]
        exact kgl34_commutator_mem H hA hB
      · exact hcore i j hij hip hjp c
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin n) (K := F), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_def]
  exact hall t.i t.j t.hij t.c

end SteinbergGenerate

section Generation

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LargeExtraspecial.A2Mod

theorem closure_eq_top_of_isotropic_coord {n : ℕ} (hn : 3 ≤ n) {F : Type*} [Field F] [CharP F 2]
    (φ : F ≃+* F) (C : GL (Fin n) F)
    (hC : ∀ i j, (C : Matrix (Fin n) (Fin n) F) i j = (C : Matrix (Fin n) (Fin n) F) j i)
    (p : Fin n) (hp : ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p p = 0) :
    Subgroup.closure ({x : projectiveSL n F | fieldAut n F φ x = x} ∪
      {x : projectiveSL n F | (conjAut n F C * dualAut n F) x = x}) = ⊤ := by
  set D : Matrix (Fin n) (Fin n) F := ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hD
  set J := Subgroup.closure ({x : projectiveSL n F | fieldAut n F φ x = x} ∪
      {x : projectiveSL n F | (conjAut n F C * dualAut n F) x = x}) with hJ
  let H : Subgroup (SpecialLinearGroup (Fin n) F) := J.comap (proj n F)
  have hmem : ∀ g : SpecialLinearGroup (Fin n) F, g ∈ H ↔ proj n F g ∈ J := fun g => Iff.rfl
  have h1 : ∀ a b : Fin n, ∀ hab : a ≠ b, SpecialLinearGroup.transvection hab (1 : F) ∈ H := by
    intro a b hab
    rw [hmem]
    apply Subgroup.subset_closure
    left
    show fieldAut n F φ (proj n F _) = proj n F _
    rw [fieldAut_proj, SpecialLinearGroup.map_transvection]
    simp
  set r : Fin n → F := fun j => D p j with hr
  have hX : ∀ c : F, tv (Pi.single p 1) (c • r) ∈ H := by
    intro c
    rw [hmem]
    apply Subgroup.subset_closure
    right
    exact orth_transvection_fixed C p c hC hp
  obtain ⟨j0, hj0⟩ : ∃ j0, D p j0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hDC : D * (C : Matrix (Fin n) (Fin n) F) = 1 := Units.inv_mul C
    have := congrFun (congrFun hDC p) p
    simp [Matrix.mul_apply, hcon] at this
  have hpj0 : p ≠ j0 := by
    rintro rfl
    exact hj0 hp
  have hrp : r p = 0 := hp
  have hex : ∀ a b : Fin n, ∃ l : Fin n, l ≠ a ∧ l ≠ b := by
    intro a b
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n)) := by
      intro l _
      by_cases hla : l = a
      · rw [hla]; simp
      · rw [hcon l hla]; simp
    have hcard := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hrow : ∀ (l : Fin n) (hpl : p ≠ l) (c : F),
      SpecialLinearGroup.transvection hpl c ∈ H := by
    intro l hpl c
    by_cases hl : l = j0
    · subst hl
      obtain ⟨k, hkp, hkl⟩ := hex p l
      have hpk : p ≠ k := fun h => hkp h.symm
      have hlk : l ≠ k := fun h => hkl h.symm
      have hA : SpecialLinearGroup.transvection hpk c ∈ H :=
        transvection_row_mem_of_tv H p l k hpl hpk hlk r hrp hj0 (h1 l k hlk) hX c
      have key := Matrix.SpecialLinearGroup.commutatorElement_transvection hpk hlk.symm hpl c
        (1 : F)
      rw [mul_one] at key
      rw [← key]
      exact kgl34_commutator_mem H hA (h1 k l hlk.symm)
    · exact transvection_row_mem_of_tv H p j0 l hpj0 hpl (fun h => hl h.symm) r hrp hj0
        (h1 j0 l (fun h => hl h.symm)) hX c
  have htop := eq_top_of_row_transvections hn H p h1 hrow
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  have hg : g ∈ H := by rw [htop]; trivial
  exact hg

end Generation

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
