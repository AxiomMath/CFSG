module

public import CFSG.ClassicalInvolution.Asc77.AscT7MS
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conj_entries {j : Fin 4} {A Ai B : Matrix (Fin 4) (Fin 4) K} (hAAi : A * Ai = 1)
    (hA1 : ∀ a, a ≠ j → A a j = 0) (hA2 : ∀ a, a ≠ j → A j a = 0)
    (hAi1 : ∀ a, a ≠ j → Ai a j = 0) (hAi2 : ∀ a, a ≠ j → Ai j a = 0)
    (hB : ∀ a b, (a = j ∨ b = j) → B a b = if a = b then 1 else 0) :
    ∀ a b, (a = j ∨ b = j) → (A * B * Ai) a b = if a = b then 1 else 0 := by
  have hrowA : ∀ b, (A * Ai) j b = A j j * Ai j b := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · intro u _ hu
      rw [hA2 u hu, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcolA : ∀ a, (A * Ai) a j = A a j * Ai j j := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · intro u _ hu
      rw [hAi1 u hu, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  intro a b hab
  rcases hab with rfl | rfl
  ·
    have hAB : ∀ u, (A * B) a u = A a a * if a = u then 1 else 0 := by
      intro u
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hB a u (Or.inl rfl)]
      · intro v _ hv
        rw [hA2 v hv, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ a) hj
    have h1 : (A * B * Ai) a b = A a a * Ai a b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hAB a]
        simp
      · intro u _ hu
        rw [hAB u]
        simp [Ne.symm hu]
      · intro hj
        exact absurd (Finset.mem_univ a) hj
    rw [h1, ← hrowA b, hAAi, Matrix.one_apply]
  ·
    have hAB : ∀ v, (A * B) v b = A v b := by
      intro v
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · rw [hB b b (Or.inl rfl)]
        simp
      · intro u _ hu
        rw [hB u b (Or.inr rfl)]
        simp [hu]
      · intro hj
        exact absurd (Finset.mem_univ b) hj
    have h1 : (A * B * Ai) a b = A a b * Ai b b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · rw [hAB a]
      · intro u _ hu
        rw [hAi1 u hu, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ b) hj
    rw [h1, ← hcolA a, hAAi, Matrix.one_apply]

section Block

variable {i : ℕ} {j : Fin 4} (hi : i + 3 ≤ 4)
  (hj : ∀ a : Fin 4, a ≠ j ↔ (i ≤ a.val ∧ a.val < i + 3))

include hj in
theorem entries_blockEmb (A : Su K p f 3) :
    ∀ a b : Fin 4, (a = j ∨ b = j) →
      suMat (blockEmb K p f 4 3 i hi A) a b = if a = b then 1 else 0 := by
  intro a b hab
  rw [suMat_blockEmb]
  rcases hab with rfl | rfl
  · rw [blockMat_apply_of_not_mem_left _ (fun h => (hj a).mpr h rfl)]
    rfl
  · rw [blockMat_apply_of_not_mem_right _ _ (fun h => (hj b).mpr h rfl)]
    rfl

include hj in
theorem exists_blockEmb_of_entries (x : Su K p f 4)
    (hx : ∀ a b : Fin 4, (a = j ∨ b = j) → suMat x a b = if a = b then 1 else 0) :
    ∃ A : Su K p f 3, blockEmb K p f 4 3 i hi A = x := by
  set C : Matrix (Fin 3) (Fin 3) K :=
    Matrix.of fun a b => suMat x (blockIdx i hi a) (blockIdx i hi b) with hC
  have hxC : suMat x = blockMat 4 i C := by
    ext a b
    rw [blockMat_apply]
    by_cases hab : (i ≤ a.val ∧ a.val < i + 3) ∧ (i ≤ b.val ∧ b.val < i + 3)
    · rw [dite_eq_left hab, hC, Matrix.of_apply]
      congr 1 <;> exact Fin.ext (by simp [blockIdx_val]; omega)
    · rw [dite_eq_right hab]
      apply hx
      by_cases ha : a = j
      · exact Or.inl ha
      · right
        by_contra hb
        exact hab ⟨(hj a).mp ha, (hj b).mp hb⟩
  have hdet : C.det = 1 := by
    rw [← det_blockMat hi, ← hxC]
    exact det_suMat x
  have hunit : conjTr (unitaryInvolution K p f) C * C = 1 := by
    apply blockMat_injective (m := 4) (i := i) hi
    rw [blockMat_mul hi, ← conjTr_blockMat, ← hxC, blockMat_one]
    exact x.2.2
  refine ⟨mkSU K p f C hdet hunit, ?_⟩
  apply suMat_injective
  rw [suMat_blockEmb, suMat_mkSU, hxC]

include hj in
theorem blockEmb_normalized (h2 : (2 : K) ≠ 0) {g : Su K p f 4}
    (hg : (dMat j : Matrix (Fin 4) (Fin 4) K) * suMat g = suMat g * dMat j)
    {x : Su K p f 4} (hx : x ∈ (blockEmb K p f 4 3 i hi).range) :
    g * x * g⁻¹ ∈ (blockEmb K p f 4 3 i hi).range := by
  obtain ⟨A, rfl⟩ := hx
  have hGi : (dMat j : Matrix (Fin 4) (Fin 4) K) * suMat g⁻¹ = suMat g⁻¹ * dMat j := by
    have hGGi : suMat g * suMat g⁻¹ = 1 := suMat_mul_suMat_inv g
    have hGiG : suMat g⁻¹ * suMat g = 1 := suMat_inv_mul_suMat g
    calc dMat j * suMat g⁻¹ = (suMat g⁻¹ * suMat g) * dMat j * suMat g⁻¹ := by
          rw [hGiG, Matrix.one_mul]
      _ = suMat g⁻¹ * (suMat g * dMat j) * suMat g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = suMat g⁻¹ * (dMat j * suMat g) * suMat g⁻¹ := by rw [hg]
      _ = suMat g⁻¹ * dMat j * (suMat g * suMat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = suMat g⁻¹ * dMat j := by rw [hGGi, Matrix.mul_one]
  have hz : ∀ (M : Matrix (Fin 4) (Fin 4) K), (dMat j : Matrix (Fin 4) (Fin 4) K) * M =
      M * dMat j → (∀ a, a ≠ j → M a j = 0) ∧ (∀ a, a ≠ j → M j a = 0) := fun M hM =>
    ⟨fun a ha => entry_zero_of_comm hM (sgn_ne_of_eq_ne h2 rfl ha).symm,
      fun a ha => entry_zero_of_comm hM (sgn_ne_of_eq_ne h2 rfl ha)⟩
  obtain ⟨hA1, hA2⟩ := hz _ hg
  obtain ⟨hAi1, hAi2⟩ := hz _ hGi
  have hent := conj_entries (j := j) (suMat_mul_suMat_inv g) hA1 hA2 hAi1 hAi2
    (entries_blockEmb hi hj A)
  obtain ⟨A', hA'⟩ := exists_blockEmb_of_entries hi hj (g * blockEmb K p f 4 3 i hi A * g⁻¹)
    (by
      intro a b hab
      rw [suMat_mul, suMat_mul]
      exact hent a b hab)
  exact ⟨A', hA'⟩

end Block

section Layers

variable {i : ℕ} {j : Fin 4}

@[expose] noncomputable def layU (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] (i : ℕ) (hi : i + 3 ≤ 4) :
    Subgroup (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) :=
  (blockEmb K p f 4 3 i hi).range.map (QuotientGroup.mk' _)

@[expose] def ActsAsD (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (φ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4))) (j : Fin 4) : Prop :=
  ∀ g : Su K p f 4, φ (QuotientGroup.mk g) = QuotientGroup.mk (suConjD K p f j g)

variable (hi : i + 3 ≤ 4) (hj : ∀ a : Fin 4, a ≠ j ↔ (i ≤ a.val ∧ a.val < i + 3))

include hj in
theorem suConjD_blockEmb (A : Su K p f 3) :
    suConjD K p f j (blockEmb K p f 4 3 i hi A) = blockEmb K p f 4 3 i hi A := by
  apply suMat_injective
  rw [suMat_suConjD]
  ext a b
  rw [dMat_conj_apply]
  by_cases ha : a = j <;> by_cases hb : b = j
  · rw [entries_blockEmb hi hj A a b (Or.inl ha)]
    have hab : a = b := ha.trans hb.symm
    subst hab
    simpa using sgn_mul_self (F := K) j a
  · rw [entries_blockEmb hi hj A a b (Or.inl ha)]
    have : a ≠ b := fun h => hb (h ▸ ha)
    simp [this]
  · rw [entries_blockEmb hi hj A a b (Or.inr hb)]
    have : a ≠ b := fun h => ha (h ▸ hb)
    simp [this]
  · have e1 : (sgn j a : K) = 1 := by simp [sgn, ha]
    have e2 : (sgn j b : K) = 1 := by simp [sgn, hb]
    rw [e1, e2, one_mul, mul_one]

include hj in
theorem layU_fix {φ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4))}
    (hφ : ActsAsD K p f φ j) : ∀ q ∈ layU K p f i hi, φ q = q := by
  rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
  show φ (QuotientGroup.mk (blockEmb K p f 4 3 i hi A)) = QuotientGroup.mk _
  rw [hφ, suConjD_blockEmb hi hj]

include hj in
theorem layU_norm (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (h2 : (2 : K) ≠ 0)
    {φ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4))} (hφ : ActsAsD K p f φ j) :
    ∀ g' : Su K p f 4 ⧸ Subgroup.center (Su K p f 4), φ g' = g' → ∀ q ∈ layU K p f i hi,
      g' * q * g'⁻¹ ∈ layU K p f i hi := by
  intro g' hg' q hq'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
  obtain ⟨x, hx, rfl⟩ := hq'
  have hfix : (QuotientGroup.mk (suConjD K p f j g) :
      Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) = QuotientGroup.mk g := by
    rw [← hφ]
    exact hg'
  have hcomm := comm_of_fix_U hK hq h2 hfix
  refine ⟨g * x * g⁻¹, blockEmb_normalized hi hj h2 hcomm hx, ?_⟩
  simp

theorem isQuasisimple_su3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    CFSG.IsQuasisimple (Su K p f 3) := by
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) hK (by norm_num : 3 ≤ 3)
    (CFSG.ClassicalInvolution.Models.Transfer.pair_ne_three_two_of_five_le hq)).1
  exact isQuasisimple_of_equiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).symm h

theorem layU_open_quasisimple (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hi : i + 3 ≤ 4) : CFSG.Open.IsQuasisimple ↥(layU K p f i hi) := by
  have hq1 : CFSG.IsQuasisimple ↥(blockEmb K p f 4 3 i hi).range :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (blockEmb_injective hi))
      (isQuasisimple_su3 hK hq)
  have hq2 : CFSG.Open.IsQuasisimple ↥(blockEmb K p f 4 3 i hi).range :=
    ⟨Group.isPerfect_def.mp hq1.1, hq1.2.1⟩
  have hker : (QuotientGroup.mk' (Subgroup.center (Su K p f 4))).ker ≤
      Subgroup.center (Su K p f 4) := (QuotientGroup.ker_mk' _).le
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.isQuasisimple_map_of_ker_le_center
    (QuotientGroup.mk' _) hker hq2

theorem layU_perf (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hi : i + 3 ≤ 4) :
    layU K p f i hi ≤ ⁅layU K p f i hi, layU K p f i hi⁆ :=
  (commutator_self_of_perfect (layU_open_quasisimple hK hq hi).1).ge

theorem layU_gen (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hi : i + 3 ≤ 4) :
    ∃ 𝓗 : Set (Subgroup (Su K p f 4 ⧸ Subgroup.center (Su K p f 4))),
      (∀ H ∈ 𝓗, H ≤ layU K p f i hi ∧ CFSG.Open.IsQuasisimple ↥H ∧
        ∀ p' ∈ layU K p f i hi, ∀ h ∈ H, p' * h * p'⁻¹ ∈ H) ∧
      layU K p f i hi ≤ ⨆ H ∈ 𝓗, H := by
  refine ⟨{layU K p f i hi}, ?_, ?_⟩
  · intro H hH
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact ⟨le_rfl, layU_open_quasisimple hK hq hi, fun p' hp h hh =>
      (layU K p f i hi).mul_mem ((layU K p f i hi).mul_mem hp hh) ((layU K p f i hi).inv_mem hp)⟩
  · exact le_iSup₂_of_le (layU K p f i hi) rfl le_rfl

theorem hj_zero : ∀ a : Fin 4, a ≠ 3 ↔ (0 ≤ a.val ∧ a.val < 0 + 3) := by
  intro a
  fin_cases a <;> simp

theorem hj_one : ∀ a : Fin 4, a ≠ 0 ↔ (1 ≤ a.val ∧ a.val < 1 + 3) := by
  intro a
  fin_cases a <;> simp

theorem blk_sup_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    (blockEmb K p f 4 3 0 (by norm_num)).range ⊔ (blockEmb K p f 4 3 1 (by norm_num)).range =
      ⊤ := by
  have hq2 : p ^ f ≠ 2 := by omega
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq2 3]
  refine iSup_le fun idx => ?_
  rintro _ ⟨A, rfl⟩
  have hent : ∀ (i₀ : ℕ) (hi₀ : i₀ + 2 ≤ 4) (j₀ : Fin 4),
      (¬ (i₀ ≤ j₀.val ∧ j₀.val < i₀ + 2)) → ∀ a b : Fin 4, (a = j₀ ∨ b = j₀) →
      suMat (blockEmb K p f 4 2 i₀ hi₀ A) a b = if a = b then 1 else 0 := by
    intro i₀ hi₀ j₀ hj₀ a b hab
    rw [suMat_blockEmb]
    rcases hab with rfl | rfl
    · rw [blockMat_apply_of_not_mem_left _ hj₀]
      rfl
    · rw [blockMat_apply_of_not_mem_right _ _ hj₀]
      rfl
  fin_cases idx
  · obtain ⟨A', hA'⟩ := exists_blockEmb_of_entries (j := 3) (i := 0) (by norm_num) hj_zero
      (blockEmb K p f 4 2 0 (by norm_num) A)
      (hent 0 (by norm_num) 3 (by simp))
    exact Subgroup.mem_sup_left ⟨A', hA'⟩
  · obtain ⟨A', hA'⟩ := exists_blockEmb_of_entries (j := 3) (i := 0) (by norm_num) hj_zero
      (blockEmb K p f 4 2 1 (by norm_num) A)
      (hent 1 (by norm_num) 3 (by simp))
    exact Subgroup.mem_sup_left ⟨A', hA'⟩
  · obtain ⟨A', hA'⟩ := exists_blockEmb_of_entries (j := 0) (i := 1) (by norm_num) hj_one
      (blockEmb K p f 4 2 2 (by norm_num) A)
      (hent 2 (by norm_num) 0 (by simp))
    exact Subgroup.mem_sup_right ⟨A', hA'⟩

theorem layU_sup (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    layU K p f 0 (by norm_num) ⊔ layU K p f 1 (by norm_num) = ⊤ := by
  unfold layU
  rw [← Subgroup.map_sup, blk_sup_eq_top hK hq, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

end Layers

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
