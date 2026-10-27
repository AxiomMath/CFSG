module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuStd

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (mem_sup_of_comm sup_le_normalizer_of_comm)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer isQuasisimple_of_equiv)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conj_cases (hK : Nat.card K = (p ^ f) ^ 2) (a g s : Su K p f 4) (ha : a * a = s)
    (hs : s = 1 ∨ s = zneg K p f) (hg : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    g * a * g⁻¹ = a ∨ g * a * g⁻¹ = zneg K p f * a := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hg
  have hr' : suMat (g * a * g⁻¹ * a⁻¹) = Matrix.scalar (Fin 4) (r : K) := hr
  have hy : suMat (g * a * g⁻¹) = (r : K) • suMat a := by
    have h1 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [h1, suMat_mul, hr', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hzc : g * s * g⁻¹ = s := by
    have hsc : s ∈ Subgroup.center (Su K p f 4) := by
      rcases hs with rfl | rfl
      · exact Subgroup.one_mem _
      · exact zneg_mem_center
    rw [Subgroup.mem_center_iff.mp hsc g]
    group
  have hyy : (g * a * g⁻¹) * (g * a * g⁻¹) = s := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = s := by rw [ha, hzc]
  have hms : ((r : K) * r) • suMat s = suMat s := by
    have h1 := congrArg suMat hyy
    rw [suMat_mul, hy, Matrix.smul_mul, Matrix.mul_smul, ← suMat_mul, ha, smul_smul] at h1
    exact h1
  have hr2 : (r : K) * r = 1 := by
    have h00 : suMat s 0 0 ≠ 0 := by
      rcases hs with rfl | rfl
      · simp [suMat_one]
      · rw [suMat_zneg]
        simp
    have := congrFun (congrFun hms 0) 0
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ h00 (this.trans (one_mul _).symm)
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · left
    apply suMat_injective
    rw [hy, hr1, one_smul]
  · right
    apply suMat_injective
    rw [hy, hr1, neg_one_smul, suMat_mul, suMat_zneg, neg_one_mul]

theorem R0_eq (h2 : (2 : K) ≠ 0) : R0 K p f = longRootGroupSU K p f (suMat (x0 K p f)) := by
  rw [x0, suMat_rootInvSU]
  exact range_blockEmb_eq_longRootGroupSU h2 (j := 0) (by norm_num)

theorem suMat_zneg_mul_x0 : suMat (zneg K p f * x0 K p f) = negBlock K 4 2 := by
  rw [suMat_mul, suMat_zneg, suMat_x0, negBlock_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem R0'_eq (h2 : (2 : K) ≠ 0) :
    R0' K p f = longRootGroupSU K p f (suMat (zneg K p f * x0 K p f)) := by
  rw [suMat_zneg_mul_x0]
  exact range_blockEmb_eq_longRootGroupSU h2 (j := 2) (by norm_num)

theorem map_conj_fix (h2 : (2 : K) ≠ 0) {g : Su K p f 4} (hg : g * x0 K p f * g⁻¹ = x0 K p f) :
    (R0 K p f).map (MulAut.conj g).toMonoidHom = R0 K p f ∧
      (R0' K p f).map (MulAut.conj g).toMonoidHom = R0' K p f := by
  refine ⟨?_, ?_⟩
  · rw [R0_eq h2, ← longRootGroupSU_conj, ← suMat_mul, ← suMat_mul, hg]
  · have : g * (zneg K p f * x0 K p f) * g⁻¹ = zneg K p f * x0 K p f := by
      calc g * (zneg K p f * x0 K p f) * g⁻¹
          = (g * zneg K p f * g⁻¹) * (g * x0 K p f * g⁻¹) := by group
        _ = zneg K p f * x0 K p f := by rw [zneg_conj, hg]
    rw [R0'_eq h2, ← longRootGroupSU_conj, ← suMat_mul, ← suMat_mul, this]

theorem map_conj_swap (h2 : (2 : K) ≠ 0) {g : Su K p f 4}
    (hg : g * x0 K p f * g⁻¹ = zneg K p f * x0 K p f) :
    (R0 K p f).map (MulAut.conj g).toMonoidHom = R0' K p f ∧
      (R0' K p f).map (MulAut.conj g).toMonoidHom = R0 K p f := by
  refine ⟨?_, ?_⟩
  · rw [R0_eq h2, ← longRootGroupSU_conj, ← suMat_mul, ← suMat_mul, hg, R0'_eq h2]
  · have : g * (zneg K p f * x0 K p f) * g⁻¹ = x0 K p f := by
      calc g * (zneg K p f * x0 K p f) * g⁻¹
          = (g * zneg K p f * g⁻¹) * (g * x0 K p f * g⁻¹) := by group
        _ = zneg K p f * (zneg K p f * x0 K p f) := by rw [zneg_conj, hg]
        _ = x0 K p f := by rw [← mul_assoc, zneg_mul_self, one_mul]
    rw [R0'_eq h2, ← longRootGroupSU_conj, ← suMat_mul, ← suMat_mul, this, R0_eq h2]

theorem negOneSU_mul_jSU : negOneSU K p f * jSU K p f = (jSU K p f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, jSU_mul_self, negOneSU_mul_self]

theorem slayer_x0 (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) (hq : 5 ≤ p ^ f) :
    SLayer (x0 K p f) (R0 K p f ⊔ R0' K p f) := by
  have hq2 : CFSG.IsQuasisimple (Su K p f 2) := isQuasisimple_su2 hK hq
  have : Group.IsPerfect (Su K p f 2) := hq2.1
  have hperf0 : Group.IsPerfect (R0 K p f) :=
    Group.IsPerfect.range (blockEmb K p f 4 2 0 (by norm_num))
  have hperf2 : Group.IsPerfect (R0' K p f) :=
    Group.IsPerfect.range (blockEmb K p f 4 2 2 (by norm_num))
  have hq0 : CFSG.IsQuasisimple ↥(R0 K p f) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := p) (f := f)
      (m := 4) (k := 2) (i := 0) (by norm_num))) hq2
  have hq2' : CFSG.IsQuasisimple ↥(R0' K p f) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := p) (f := f)
      (m := 4) (k := 2) (i := 2) (by norm_num))) hq2
  have hn0 := sup_le_normalizer_of_comm (A := R0 K p f) (B := R0' K p f) fun a ha b hb =>
    R0_comm_R0' ha hb
  have hn2 := sup_le_normalizer_of_comm (A := R0' K p f) (B := R0 K p f) fun a ha b hb =>
    (R0_comm_R0' hb ha).symm
  rw [sup_comm] at hn2
  have hx0c : ∀ A : Su K p f 2, blockEmb K p f 4 2 0 (by norm_num) A * x0 K p f =
      x0 K p f * blockEmb K p f 4 2 0 (by norm_num) A := fun A => by
    rw [x0, rootInvSU, ← map_mul, ← map_mul, negOneSU_comm]
  have hx0c' : ∀ B : Su K p f 2, blockEmb K p f 4 2 2 (by norm_num) B * x0 K p f =
      x0 K p f * blockEmb K p f 4 2 2 (by norm_num) B := fun B => by
    rw [x0, rootInvSU]
    exact (blockEmb_comm _ B).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p' hp
    have : R0 K p f ⊔ R0' K p f ≤ Subgroup.centralizer ({x0 K p f} : Set (Su K p f 4)) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hx0c A
      · rintro _ ⟨B, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hx0c' B
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hp)
  · intro g hg p' hp
    have hmem : g * p' * g⁻¹ ∈ (R0 K p f ⊔ R0' K p f).map (MulAut.conj g).toMonoidHom :=
      ⟨p', hp, rfl⟩
    rw [Subgroup.map_sup] at hmem
    rcases conj_cases hK (x0 K p f) g 1 x0_mul_self (Or.inl rfl) hg with h | h
    · obtain ⟨e1, e2⟩ := map_conj_fix h2 h
      rwa [e1, e2] at hmem
    · obtain ⟨e1, e2⟩ := map_conj_swap h2 h
      rwa [e1, e2, sup_comm] at hmem
  · refine sup_le ?_ ?_
    · exact (Subgroup.commutator_eq_self (H := R0 K p f)).symm.le.trans
        (Subgroup.commutator_mono le_sup_left le_sup_left)
    · exact (Subgroup.commutator_eq_self (H := R0' K p f)).symm.le.trans
        (Subgroup.commutator_mono le_sup_right le_sup_right)
  · refine ⟨{R0 K p f, R0' K p f}, ?_, ?_⟩
    · intro H hH
      rcases hH with rfl | hH
      · exact ⟨le_sup_left, hq0, fun p' hp h hh =>
          (Subgroup.mem_normalizer_iff.mp (hn0 hp) h).mp hh⟩
      · rw [Set.mem_singleton_iff] at hH
        subst hH
        exact ⟨le_sup_right, hq2', fun p' hp h hh =>
          (Subgroup.mem_normalizer_iff.mp (hn2 hp) h).mp hh⟩
    · exact sup_le (le_iSup₂_of_le (R0 K p f) (Set.mem_insert _ _) le_rfl)
        (le_iSup₂_of_le (R0' K p f) (Set.mem_insert_of_mem _ rfl) le_rfl)

theorem classify_w (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {w : Su K p f 4}
    (hw : w ∈ R0 K p f ⊔ R0' K p f) (hw2 : w * w ∈ Subgroup.center (Su K p f 4)) :
    w = 1 ∨ w = x0 K p f ∨ w = zneg K p f * x0 K p f ∨ w = zneg K p f ∨
      ∃ h ∈ R0 K p f ⊔ R0' K p f, w = h * u0 K p f * h⁻¹ := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_comm (fun a ha b hb => R0_comm_R0' ha hb) hw
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  have hwb : w = blk K p f A B := hab.symm
  subst hwb
  rw [blk_mul] at hw2
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hw2
  have hμ' : suMat (blk K p f (A * A) (B * B)) = Matrix.scalar (Fin 4) (μ : K) := hμ
  rw [suMat_blk] at hμ'
  have f00 := congrFun (congrFun hμ' 0) 0
  have f01 := congrFun (congrFun hμ' 0) 1
  have f10 := congrFun (congrFun hμ' 1) 0
  have f11 := congrFun (congrFun hμ' 1) 1
  have g22 := congrFun (congrFun hμ' 2) 2
  have g23 := congrFun (congrFun hμ' 2) 3
  have g32 := congrFun (congrFun hμ' 3) 2
  have g33 := congrFun (congrFun hμ' 3) 3
  simp [Matrix.scalar_apply] at f00 f01 f10 f11 g22 g23 g32 g33
  have hrr : suMat A * suMat A = (μ : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← suMat_mul]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using f00
    · simpa using f01
    · simpa using f10
    · simpa using f11
  have hrr' : suMat B * suMat B = (μ : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← suMat_mul]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using g22
    · simpa using g23
    · simpa using g32
    · simpa using g33
  have hone : ∀ C : Su K p f 2, suMat C = 1 → C = 1 := fun C h => suMat_injective (by
    rw [h, suMat_one])
  have hneg : ∀ C : Su K p f 2, suMat C = -1 → C = negOneSU K p f := fun C h => suMat_injective (by
    rw [h, suMat_negOneSU])
  rcases su2_sq_cases h2 A hrr with ⟨hμ1, hr1 | hr1⟩ | ⟨hμ1, hr1⟩ <;>
    rcases su2_sq_cases h2 B hrr' with ⟨hμ1', hr1' | hr1'⟩ | ⟨hμ1', hr1'⟩
  · left
    rw [hone A hr1, hone B hr1', blk_one]
  · right; right; left
    rw [hone A hr1, hneg B hr1', zneg_mul_x0]
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · right; left
    rw [hneg A hr1, hone B hr1', x0_eq_blk]
  · right; right; right; left
    rw [hneg A hr1, hneg B hr1', zneg_eq_blk]
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · have hA2 : A * A = negOneSU K p f := suMat_injective (by rw [suMat_mul, hr1, suMat_negOneSU])
    have hB2 : B * B = negOneSU K p f := suMat_injective (by rw [suMat_mul, hr1', suMat_negOneSU])
    obtain ⟨h₁, hh₁⟩ := exists_conj_jSU hK h2 hA2
    obtain ⟨h₂, hh₂⟩ := exists_conj_jSU hK h2 hB2
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨blk K p f h₁ h₂, blk_mem _ _, ?_⟩)))
    rw [u0_eq_blk, blk_inv, blk_mul, blk_mul, hh₁, hh₂]

theorem exists_conj_t0 (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) :
    ∃ g' : Su K p f 4, g' * u0 K p f * g'⁻¹ = t0 K p f ∧ g' * x0 K p f * g'⁻¹ = x0 K p f := by
  have hj : (jSU K p f)⁻¹ * (jSU K p f)⁻¹ = negOneSU K p f := by
    rw [← _root_.mul_inv_rev, jSU_mul_self, inv_eq_of_mul_eq_one_right negOneSU_mul_self]
  obtain ⟨h, hh⟩ := exists_conj_jSU hK h2 hj
  refine ⟨blk K p f h 1, ?_, ?_⟩
  · rw [u0_eq_blk, blk_inv, blk_mul, blk_mul, hh, t0, x0_eq_blk, u0_eq_blk, blk_mul,
      negOneSU_mul_jSU]
    simp
  · rw [x0_eq_blk, blk_inv, blk_mul, blk_mul]
    have : h * negOneSU K p f * h⁻¹ = negOneSU K p f := by
      rw [negOneSU_comm h]
      group
    rw [this]
    simp

theorem u0_not_central (hK : Nat.card K = (p ^ f) ^ 2) :
    u0 K p f ∉ Subgroup.center (Su K p f 4) := by
  intro h
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) h
  have hr' : suMat (u0 K p f) = Matrix.scalar (Fin 4) (r : K) := hr
  have e := congrFun (congrFun hr' 0) 1
  rw [suMat_u0] at e
  simp [Matrix.scalar_apply] at e

theorem t0_not_central (hK : Nat.card K = (p ^ f) ^ 2) :
    t0 K p f ∉ Subgroup.center (Su K p f 4) := by
  intro h
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) h
  have hr' : suMat (t0 K p f) = Matrix.scalar (Fin 4) (r : K) := hr
  have e := congrFun (congrFun hr' 0) 1
  rw [t0, suMat_mul, suMat_x0, suMat_u0] at e
  simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_four] at e

theorem x0_not_central (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) :
    x0 K p f ∉ Subgroup.center (Su K p f 4) := by
  intro h
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) h
  have hr' : suMat (x0 K p f) = Matrix.scalar (Fin 4) (r : K) := hr
  have e0 := congrFun (congrFun hr' 0) 0
  have e2 := congrFun (congrFun hr' 2) 2
  rw [suMat_x0] at e0 e2
  simp [Matrix.scalar_apply] at e0 e2
  apply h2
  linear_combination e2 - e0

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
