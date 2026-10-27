module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharXferImg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharClass
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open scoped Matrix

@[expose] def plusPos (n : ℕ) : Fin n ⊕ Fin n → ℕ
  | Sum.inl i => i
  | Sum.inr j => 2 * n - 1 - j

@[simp] theorem plusPos_inl (n : ℕ) (i : Fin n) : plusPos n (Sum.inl i) = i := rfl

@[simp] theorem plusPos_inr (n : ℕ) (j : Fin n) : plusPos n (Sum.inr j) = 2 * n - 1 - j := rfl

section Siegel

variable {n : ℕ} {K : Type} [Field K]

@[expose] def siegelGL (C : Matrix (Fin n) (Fin n) K) : GL (Fin n ⊕ Fin n) K where
  val := Matrix.fromBlocks 1 C 0 1
  inv := Matrix.fromBlocks 1 (-C) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] theorem coe_siegelGL (C : Matrix (Fin n) (Fin n) K) :
    ((siegelGL C : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 1 C 0 1 := rfl

theorem siegelGL_mem (hn : 3 ≤ n) {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) : siegelGL C ∈ StatedOmega (StatedQuadPlus n K) := by
  refine plusMatrixUnipotent_le_derived n K hn ?_
  rw [mem_plusMatrixUnipotent]
  refine ⟨1, C, Matrix.blockTriangular_one, fun i => by simp, hC, hd, ?_⟩
  simp

@[expose] def siegel (hn : 3 ≤ n) {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) : ↥(StatedOmega (StatedQuadPlus n K)) :=
  ⟨siegelGL C, siegelGL_mem hn hC hd⟩

theorem matrixHom_siegel_sub_one (hn : 3 ≤ n) {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) :
    matrixHom (StatedOmega (StatedQuadPlus n K)) (siegel hn hC hd) - 1 =
      Matrix.fromBlocks 0 C 0 0 := by
  rw [matrixHom_apply]
  change Matrix.fromBlocks 1 C 0 1 - 1 = _
  rw [← Matrix.fromBlocks_one]
  ext (a | a) (b | b) <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem siegel_mem_Lev [Finite K] (hn : 3 ≤ n) {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ a b : Fin n, C a b ≠ 0 → (a : ℕ) + k ≤ 2 * n - 1 - b) :
    siegel hn hC hd ∈ Lev (matrixHom (StatedOmega (StatedQuadPlus n K))) (plusPos n) k hk := by
  rw [mem_Lev, matrixHom_siegel_sub_one]
  rintro (a | a) (b | b) hab
  · simp
  · by_contra hne
    have hCab : C a b ≠ 0 := by simpa using hne
    have := h a b hCab
    simp only [plusPos_inl, plusPos_inr] at hab
    omega
  · simp
  · simp

@[expose] def altE (a b : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.single a b 1 - Matrix.single b a 1

theorem altE_transpose (a b : Fin n) : (altE a b : Matrix (Fin n) (Fin n) K)ᵀ = -altE a b := by
  simp only [altE, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]

theorem altE_diag {a b : Fin n} (hab : a ≠ b) (i : Fin n) : (altE a b : Matrix (Fin n) (Fin n) K)
    i i = 0 := by
  simp only [altE, Matrix.sub_apply, Matrix.single_apply]
  by_cases h1 : a = i ∧ b = i
  · exact absurd (h1.1.trans h1.2.symm) hab
  · by_cases h2 : b = i ∧ a = i
    · exact absurd (h2.2.trans h2.1.symm) hab
    · simp [h1, h2]

theorem altE_apply_self {a b : Fin n} (hab : a ≠ b) :
    (altE a b : Matrix (Fin n) (Fin n) K) a b = 1 := by
  simp [altE, Matrix.single_apply, hab, hab.symm]

theorem altE_apply_of_ne {a b i j : Fin n} (h1 : ¬ (a = i ∧ b = j)) (h2 : ¬ (b = i ∧ a = j)) :
    (altE a b : Matrix (Fin n) (Fin n) K) i j = 0 := by
  simp only [altE, Matrix.sub_apply, Matrix.single_apply]
  simp [h1, h2]

theorem siegel_altE_mem_Lev [Finite K] (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) {k : ℕ}
    (hk : 1 ≤ k) (hle : (a : ℕ) + b + k ≤ 2 * n - 1) :
    siegel hn (altE_transpose (K := K) a b) (altE_diag hab) ∈
      Lev (matrixHom (StatedOmega (StatedQuadPlus n K))) (plusPos n) k hk := by
  refine siegel_mem_Lev hn _ _ hk fun i j hij => ?_
  by_cases h1 : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h1
    omega
  · by_cases h2 : b = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h2
      omega
    · exact absurd (altE_apply_of_ne h1 h2) hij

end Siegel

section Unitriangular

variable {n : ℕ} {K : Type} [Field K]

theorem inv_upperUni {A : GL (Fin n) K} (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular)
    (h1 : ∀ i, (A : Matrix (Fin n) (Fin n) K) i i = 1) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular ∧
      ∀ i, ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
  have h : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hup : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
    haveI : Invertible (A : Matrix (Fin n) (Fin n) K) := A.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hA
  refine ⟨hup, fun i => ?_⟩
  have e : ((A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) i i = 1 := by rw [h, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rwa [h1 i, one_mul] at e
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hlt
    · rw [hA hlt, zero_mul]
    · rw [hup hlt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Unitriangular

section Main

variable {n : ℕ} {K : Type} [Field K]

theorem plusDerivedUnipotent_le_Lev [Finite K] :
    plusDerivedUnipotent n K ≤
      Lev (matrixHom (StatedOmega (StatedQuadPlus n K))) (plusPos n) 1 le_rfl := by
  intro g hg
  rw [plusDerivedUnipotent, Subgroup.mem_subgroupOf] at hg
  obtain ⟨A, C, hA, h1, -, -, hgm⟩ := (mem_plusMatrixUnipotent n K _).1 hg
  obtain ⟨hAi, h1i⟩ := inv_upperUni hA h1
  rw [mem_Lev, matrixHom_apply, hgm]
  rintro (a | a) (b | b) hab
  · simp only [plusPos_inl] at hab
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₁]
    by_cases hba : b = a
    · subst hba
      rw [h1 b, Matrix.one_apply_eq, sub_self]
    · have hlt : b < a := lt_of_le_of_ne (by omega : (b : ℕ) ≤ a) hba
      have hne : (Sum.inl a : Fin n ⊕ Fin n) ≠ Sum.inl b := fun h =>
        hba (Sum.inl_injective h).symm
      rw [hA hlt, Matrix.one_apply_ne hne, sub_self]
  · simp only [plusPos_inl, plusPos_inr] at hab
    have := a.isLt
    have := b.isLt
    omega
  · simp
  · simp only [plusPos_inr] at hab
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₂₂]
    have hab' : (a : ℕ) ≤ b := by
      have := a.isLt
      have := b.isLt
      omega
    by_cases hba : a = b
    · subst hba
      rw [Matrix.transpose_apply, h1i a, Matrix.one_apply_eq, sub_self]
    · have hlt : a < b := lt_of_le_of_ne hab' hba
      have hne : (Sum.inr a : Fin n ⊕ Fin n) ≠ Sum.inr b := fun h => hba (Sum.inr_injective h)
      rw [Matrix.transpose_apply, hAi hlt, Matrix.one_apply_ne hne, sub_self]

theorem not_dvd_index_Lev_plus [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hn : 3 ≤ n)
    {G : Type} [Group G] (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    ¬ p ∣ ((Lev (matrixHom (StatedOmega (StatedQuadPlus n K))) (plusPos n) 1 le_rfl).map
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
        (StatedOmega (StatedQuadPlus n K)))))).index := by
  obtain ⟨S, hS⟩ := plusProjectiveUnipotent_isSylow n K p hn
  have hle : (S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) ≤
      (Lev (matrixHom (StatedOmega (StatedQuadPlus n K))) (plusPos n) 1 le_rfl).map
        (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
          (StatedOmega (StatedQuadPlus n K)))) := by
    rw [hS, plusProjectiveUnipotent]
    exact Subgroup.map_mono plusDerivedUnipotent_le_Lev
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [← Subgroup.map_map, Subgroup.index_map_of_bijective e.symm.bijective]
  exact fun h => S.not_dvd_index (h.trans hdvd)

theorem siegel_entry (hn : 3 ≤ n) {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) (a b : Fin n) :
    (matrixHom (StatedOmega (StatedQuadPlus n K)) (siegel hn hC hd) - 1) (Sum.inl a)
      (Sum.inr b) = C a b := by
  rw [matrixHom_siegel_sub_one]
  rfl

end Main

theorem rankThreeCent_pomegaPlus {p n f : ℕ} [hp : Fact p.Prime] (hn : 4 ≤ n) {G : Type}
    [Group G] [Finite G] (h : StatedClassicalModel G .POmegaPlus n p f) :
    RankThreeCent p G := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hadm.2.1 hK
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hn3 : 3 ≤ n := by omega
  let H : Subgroup (GL (Fin n ⊕ Fin n) K) := StatedOmega (StatedQuadPlus n K)
  let π : ↥H →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf H))
  have hπinj : ∀ u ∈ Lev (matrixHom H) (plusPos n) 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    refine mk_injOn_Lev H (plusPos n) u hu ?_
    exact e.symm.injective (hu1.trans (map_one e.symm).symm)
  have hidx := not_dvd_index_Lev_plus (p := p) (K := K) hn3 e
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin n, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin n, (i : ℕ) = n - 2 := ⟨⟨n - 2, by omega⟩, rfl⟩
  obtain ⟨i3, hi3⟩ : ∃ i : Fin n, (i : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := fun h' => by have := congrArg Fin.val h'; omega
  have h03 : i0 ≠ i3 := fun h' => by have := congrArg Fin.val h'; omega
  have h12 : i1 ≠ i2 := fun h' => by have := congrArg Fin.val h'; omega
  have h02 : i0 ≠ i2 := fun h' => by have := congrArg Fin.val h'; omega
  have h13 : i1 ≠ i3 := fun h' => by have := congrArg Fin.val h'; omega
  have h23 : i2 ≠ i3 := fun h' => by have := congrArg Fin.val h'; omega
  have hk : 1 ≤ n := by omega
  have h₁ := siegel_altE_mem_Lev (K := K) hn3 h03 hk (by omega)
  have h₂ := siegel_altE_mem_Lev (K := K) hn3 h12 hk (by omega)
  have hb₀ := siegel_altE_mem_Lev (K := K) hn3 h01 (by omega : 1 ≤ n + 1) (by omega)
  have hb₀1 : siegel hn3 (altE_transpose (K := K) i0 i1) (altE_diag h01) ≠ 1 := by
    intro h1
    have h2 := siegel_entry hn3 (altE_transpose (K := K) i0 i1) (altE_diag h01) i0 i1
    rw [h1, map_one, sub_self, Matrix.zero_apply, altE_apply_self h01] at h2
    exact zero_ne_one h2
  have hD : ∀ a b : Fin n ⊕ Fin n, plusPos n b < plusPos n a + 2 * n := by
    intro a b
    rcases b with b | b <;> simp only [plusPos_inl, plusPos_inr] <;> have := b.isLt <;> omega
  refine rankThreeCent_of_corner_img (ρ := matrixHom H) (pos := plusPos n) (matrixHom_injective H)
    hk hD π hπinj hidx h₁ h₂ hb₀ hb₀1 (a₁ := Sum.inl i0) (b₁ := Sum.inr i3) (a₂ := Sum.inl i1)
    (b₂ := Sum.inr i2) ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [plusPos_inl, plusPos_inr]
    omega
  · simp only [plusPos_inl, plusPos_inr]
    omega
  · rw [siegel_entry]
    exact altE_apply_self h03
  · rw [siegel_entry]
    exact altE_apply_of_ne (by rintro ⟨h', -⟩; exact h01 h')
      (by rintro ⟨h', -⟩; exact h13 h'.symm)
  · rw [siegel_entry]
    exact altE_apply_of_ne (by rintro ⟨h', -⟩; exact h01 h'.symm)
      (by rintro ⟨h', -⟩; exact h02 h'.symm)
  · rw [siegel_entry]
    exact altE_apply_self h12

theorem inOmegaPlus : InOmegaPlus := fun p n f hp _ hn G _ _ hm => by
  haveI : Fact p.Prime := ⟨hp⟩
  exact rankThreeCent_pomegaPlus hn hm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
