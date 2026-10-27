module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharLev
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSmall

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped Matrix

section Sp

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spPos (r : ℕ) : Fin r ⊕ Fin r → ℕ := fun x => (flagOrder r x : ℕ)

theorem Lev_one_eq_unipotent [Finite K] (r : ℕ) :
    Lev (matrixHom (StatedSp r K)) (spPos r) 1 le_rfl = unipotent r K := by
  ext g
  rw [mem_unipotent_iff_reindex]
  exact mem_Lev_one_iff_reindex (flagOrder r) (StatedSp r K) g

theorem Lev_one_index_not_dvd_sp {p : ℕ} [hp : Fact p.Prime] [Finite K] [CharP K p] (r : ℕ) :
    ¬ p ∣ (Lev (matrixHom (StatedSp r K)) (spPos r) 1 le_rfl).index := by
  rw [Lev_one_eq_unipotent]
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) p r
  rw [← hP]
  exact P.not_dvd_index

theorem matrixHom_upperUnipotentSp_sub_one {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) :
    matrixHom (StatedSp r K) (upperUnipotentSp r K hC) - 1 = Matrix.fromBlocks 0 C 0 0 := by
  rw [matrixHom_apply, coe_upperUnipotentSp, ← Matrix.fromBlocks_one]
  ext (a | a) (b | b) <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem upperUnipotentSp_mem_Lev [Finite K] {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) {k : ℕ}
    (hk : 1 ≤ k) (h : ∀ a b : Fin r, C a b ≠ 0 → (a : ℕ) + k ≤ 2 * r - 1 - b) :
    upperUnipotentSp r K hC ∈ Lev (matrixHom (StatedSp r K)) (spPos r) k hk := by
  rw [mem_Lev, matrixHom_upperUnipotentSp_sub_one]
  rintro (a | a) (b | b) hab
  · simp
  · by_contra hne
    have hCab : C a b ≠ 0 := by simpa using hne
    have := h a b hCab
    simp only [spPos, flagOrder_inl, flagOrder_inr] at hab
    omega
  · simp
  · simp

theorem exists_noncomm_unipotent_two [Finite K] :
    ∃ u v : StatedSp 2 K, u ∈ unipotent 2 K ∧ v ∈ unipotent 2 K ∧ u * v ≠ v * u := by
  let A : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]
  have hA : IsUnitriangular A := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢
    · fin_cases i <;> simp [A]
  obtain ⟨u, hu, hu_mat⟩ := exists_mem_unipotent (C := (0 : Matrix (Fin 2) (Fin 2) K)) hA
    (Matrix.transpose_zero)
  let C : Matrix (Fin 2) (Fin 2) K := Matrix.single 1 1 1
  have hC : Cᵀ = C := by simp [C, Matrix.transpose_single]
  have hv : upperUnipotentSp 2 K hC ∈ unipotent 2 K := by
    rw [← Lev_one_eq_unipotent]
    refine upperUnipotentSp_mem_Lev hC le_rfl fun a b hab => ?_
    by_cases h1 : (1 : Fin 2) = a ∧ (1 : Fin 2) = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · exact absurd (Matrix.single_apply_of_ne _ _ _ _ _ h1) hab
  refine ⟨u, upperUnipotentSp 2 K hC, hu, hv, fun h => ?_⟩
  have h1 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0)
      (Sum.inr 1)) h
  simp only [Subgroup.coe_mul, Units.val_mul, hu_mat, coe_upperUnipotentSp, blockMat,
    Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at h1
  simp [A, C, Matrix.single_apply] at h1


theorem pRank_le_three_psp_two_prime {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .PSp 2 p 1) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3 := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hadm.2.1 hK
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  let π : ↥H →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H))
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπinj : ∀ u ∈ Lev (matrixHom H) (spPos 2) 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    refine mk_injOn_Lev H (spPos 2) u hu ?_
    exact e.symm.injective (hu1.trans (map_one e.symm).symm)
  have hlt : ∀ x : Fin 2 ⊕ Fin 2, spPos 2 x < 4 := fun x => by
    have := (flagOrder 2 x).isLt
    simpa [spPos] using this
  obtain ⟨u, v, hu, hv, huv⟩ := exists_noncomm_unipotent_two (K := K)
  refine pRank_top_le_of_nonab π hπ (U := Lev (matrixHom H) (spPos 2) 1 le_rfl)
    (isPGroup_Lev (matrixHom_injective H) (D := 4) (fun a b => by have := hlt b; omega))
    (Lev_one_index_not_dvd_sp 2) hπinj (k := 3) ?_ (u := u) (v := v) ?_ ?_ huv
  · rw [Lev_one_eq_unipotent, card_unipotent (K := K) 2, hK]
    norm_num
  · rw [Lev_one_eq_unipotent]
    exact hu
  · rw [Lev_one_eq_unipotent]
    exact hv


end Sp


theorem rankThreeCent_psp {p r f : ℕ} [hp : Fact p.Prime] (hr : 3 ≤ r) {G : Type} [Group G]
    [Finite G] (h : StatedClassicalModel G .PSp r p f) : RankThreeCent p G := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hadm.2.1 hK
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  let H : Subgroup (GL (Fin r ⊕ Fin r) K) := StatedSp r K
  let π : ↥H →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf H))
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπinj : ∀ u ∈ Lev (matrixHom H) (spPos r) 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    refine mk_injOn_Lev H (spPos r) u hu ?_
    exact e.symm.injective (hu1.trans (map_one e.symm).symm)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin r, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin r, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin r, (i : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; omega
  have h02 : i0 ≠ i2 := fun h => by have := congrArg Fin.val h; omega
  have h12 : i1 ≠ i2 := fun h => by have := congrArg Fin.val h; omega
  set C₁ : Matrix (Fin r) (Fin r) K := Matrix.single i0 i2 1 + Matrix.single i2 i0 1 with hC₁def
  set C₂ : Matrix (Fin r) (Fin r) K := Matrix.single i1 i1 1 with hC₂def
  set C₃ : Matrix (Fin r) (Fin r) K := Matrix.single i0 i0 1 with hC₃def
  have hC₁ : C₁ᵀ = C₁ := by
    simp only [C₁, Matrix.transpose_add, Matrix.transpose_single]
    exact add_comm _ _
  have hC₂ : C₂ᵀ = C₂ := by simp [C₂, Matrix.transpose_single]
  have hC₃ : C₃ᵀ = C₃ := by simp [C₃, Matrix.transpose_single]
  have hk : 1 ≤ 2 * r - 3 := by omega
  have hentry : ∀ (C : Matrix (Fin r) (Fin r) K) (hC : Cᵀ = C) (a b : Fin r),
      (matrixHom H (upperUnipotentSp r K hC) - 1) (Sum.inl a) (Sum.inr b) = C a b := by
    intro C hC a b
    rw [matrixHom_upperUnipotentSp_sub_one]
    rfl
  have hb₀1 : upperUnipotentSp r K hC₃ ≠ 1 := by
    intro h
    have h1 := hentry C₃ hC₃ i0 i0
    rw [h, map_one, sub_self] at h1
    simp [C₃] at h1
  have hC₁mem : ∀ a b : Fin r, C₁ a b ≠ 0 → (a : ℕ) + (2 * r - 3) ≤ 2 * r - 1 - b := by
    intro a b hab
    by_cases h1 : i0 = a ∧ i2 = b
    · obtain ⟨rfl, rfl⟩ := h1
      omega
    · by_cases h2 : i2 = a ∧ i0 = b
      · obtain ⟨rfl, rfl⟩ := h2
        omega
      · exfalso
        apply hab
        simp only [C₁, Matrix.add_apply]
        rw [Matrix.single_apply_of_ne _ _ _ _ _ h1, Matrix.single_apply_of_ne _ _ _ _ _ h2,
          add_zero]
  have hC₂mem : ∀ a b : Fin r, C₂ a b ≠ 0 → (a : ℕ) + (2 * r - 3) ≤ 2 * r - 1 - b := by
    intro a b hab
    by_cases h1 : i1 = a ∧ i1 = b
    · obtain ⟨rfl, rfl⟩ := h1
      omega
    · exfalso
      apply hab
      exact Matrix.single_apply_of_ne _ _ _ _ _ h1
  have hC₃mem : ∀ a b : Fin r, C₃ a b ≠ 0 → (a : ℕ) + (2 * r - 3 + 1) ≤ 2 * r - 1 - b := by
    intro a b hab
    by_cases h1 : i0 = a ∧ i0 = b
    · obtain ⟨rfl, rfl⟩ := h1
      omega
    · exfalso
      apply hab
      exact Matrix.single_apply_of_ne _ _ _ _ _ h1
  refine rankThreeCent_of_corner (ρ := matrixHom H) (pos := spPos r) (matrixHom_injective H) hk
    (fun a b => by
      have := (flagOrder r b).isLt
      simp only [spPos]
      omega) π hπ hπinj (Lev_one_index_not_dvd_sp r)
    (g₁ := upperUnipotentSp r K hC₁) (g₂ := upperUnipotentSp r K hC₂)
    (b₀ := upperUnipotentSp r K hC₃)
    (upperUnipotentSp_mem_Lev hC₁ hk hC₁mem) (upperUnipotentSp_mem_Lev hC₂ hk hC₂mem)
    (upperUnipotentSp_mem_Lev hC₃ (by omega) hC₃mem)
    hb₀1 (a₁ := Sum.inl i0) (b₁ := Sum.inr i2) (a₂ := Sum.inl i1) (b₂ := Sum.inr i1)
    (by simp only [spPos, flagOrder_inl, flagOrder_inr]; omega)
    (by simp only [spPos, flagOrder_inl, flagOrder_inr]; omega) ?_ ?_ ?_ ?_
  · rw [hentry]
    simp [C₁, Matrix.single_apply, h02, h02.symm]
  · rw [hentry]
    simp [C₁, Matrix.single_apply, h01, h01.symm, h12, h12.symm]
  · rw [hentry]
    simp [C₂, Matrix.single_apply, h01, h01.symm, h12, h12.symm]
  · rw [hentry]
    simp [C₂, Matrix.single_apply]


theorem rankThreeCent_psp_two {p f : ℕ} [hp : Fact p.Prime] (hf : 2 ≤ f) {G : Type} [Group G]
    [Finite G] (h : StatedClassicalModel G .PSp 2 p f)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)) : RankThreeCent p G := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hadm.2.1 hK
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  let π : ↥H →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H))
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπinj : ∀ u ∈ Lev (matrixHom H) (spPos 2) 1 le_rfl, π u = 1 → u = 1 := by
    intro u hu hu1
    refine mk_injOn_Lev H (spPos 2) u hu ?_
    exact e.symm.injective (hu1.trans (map_one e.symm).symm)
  have hlt : ∀ x : Fin 2 ⊕ Fin 2, spPos 2 x < 4 := fun x => by
    have := (flagOrder 2 x).isLt
    simpa [spPos] using this
  let C : K → Matrix (Fin 2) (Fin 2) K := fun t => Matrix.single 0 0 t
  have hC : ∀ t, (C t)ᵀ = C t := fun t => by simp [C, Matrix.transpose_single]
  have hmem : ∀ t : K, upperUnipotentSp 2 K (hC t) ∈ Lev (matrixHom H) (spPos 2) 3 (by omega) := by
    intro t
    refine upperUnipotentSp_mem_Lev (hC t) (by omega) fun a b hab => ?_
    by_cases h1 : (0 : Fin 2) = a ∧ (0 : Fin 2) = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · exact absurd (Matrix.single_apply_of_ne _ _ _ _ _ h1) hab
  let g : K → ↥(Lev (matrixHom H) (spPos 2) 3 (by omega)) := fun t =>
    ⟨upperUnipotentSp 2 K (hC t), hmem t⟩
  have hg : Function.Injective g := by
    intro t t' htt'
    have h1 := congrArg (fun x : ↥(Lev (matrixHom H) (spPos 2) 3 (by omega)) =>
      (matrixHom H (x : ↥H) - 1) (Sum.inl 0) (Sum.inr 0)) htt'
    simp only [g, matrixHom_upperUnipotentSp_sub_one] at h1
    simpa [C] using h1
  have hcard : p ^ 2 ≤ Nat.card ↥(Lev (matrixHom H) (spPos 2) 3 (by omega)) := by
    calc p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf
      _ = Nat.card K := hK.symm
      _ ≤ _ := Nat.card_le_card_of_injective g hg
  exact rankThreeCent_of_center (ρ := matrixHom H) (pos := spPos 2) (matrixHom_injective H)
    (k := 3) (by omega) (fun a b => by have := hlt b; omega) (fun a b => by have := hlt b; omega)
    π hπ hπinj (Lev_one_index_not_dvd_sp 2) h3 hcard

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
