module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_elationGenerators_iff {L : Submodule K (Fin n → K)}
    {A : Matrix.SpecialLinearGroup (Fin n) K} :
    A ∈ elationGenerators L ↔ (∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ L) ∧
      ∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
  simp only [mem_elationGenerators, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem mem_elationGenerators_of_mem {L : Submodule K (Fin n → K)}
    {A : Matrix.SpecialLinearGroup (Fin n) K} (hA : A ∈ elationSubgroup L) :
    A ∈ elationGenerators L := by
  refine Subgroup.closure_induction (p := fun A _ => A ∈ elationGenerators L) (fun _ h => h)
    (one_mem_elationGenerators L) (fun A B _ _ hA hB => ?_) (fun A _ hA => ?_) hA
  · rw [mem_elationGenerators_iff] at hA hB ⊢
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
        show (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) - v =
          ((A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) -
            (B : Matrix (Fin n) (Fin n) K) *ᵥ v) +
            ((B : Matrix (Fin n) (Fin n) K) *ᵥ v - v) by abel]
      exact L.add_mem (hA.1 _) (hB.1 v)
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB.2 v hv, hA.2 v hv]
  · rw [mem_elationGenerators_iff] at hA ⊢
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := L.neg_mem (hA.1 (((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v))
      rwa [mulVec_inv_mulVec, neg_sub] at this
    · conv_lhs => rw [← hA.2 v hv]
      exact inv_mulVec_mulVec A v

theorem pow_mulVec_of_mem_elationGenerators {L : Submodule K (Fin n → K)}
    {A : Matrix.SpecialLinearGroup (Fin n) K} (hA : A ∈ elationGenerators L) (k : ℕ)
    (v : Fin n → K) :
    ((A : Matrix (Fin n) (Fin n) K) ^ k) *ᵥ v =
      v + (k : K) • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by
  rw [mem_elationGenerators_iff] at hA
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      hA.2 _ (hA.1 v), Nat.cast_succ]
    module

theorem isPGroup_elationSubgroup (p : ℕ) [CharP K p] (L : Submodule K (Fin n → K)) :
    IsPGroup p (elationSubgroup L) := by
  intro A
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  ext i j
  have := congrFun (pow_mulVec_of_mem_elationGenerators (mem_elationGenerators_of_mem A.2) p
    (Pi.single j 1)) i
  rw [CharP.cast_eq_zero, zero_smul, add_zero] at this
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem conj_mem_elationGenerators {L : Submodule K (Fin n → K)}
    {g A : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ stabilizer L)
    (hA : A ∈ elationGenerators L) :
    g * A * g⁻¹ ∈ elationGenerators L := by
  rw [mem_elationGenerators_iff] at hA ⊢
  have hgL : ∀ w ∈ L, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ L := fun w hw =>
    (mem_stabilizer.mp hg) ▸ ⟨w, hw, rfl⟩
  have hg'L : ∀ w ∈ L,
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ L :=
    fun w hw => (mem_stabilizer.mp (inv_mem hg)) ▸ ⟨w, hw, rfl⟩
  have hgg := mulVec_inv_mulVec g
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e := Matrix.mulVec_sub (g : Matrix (Fin n) (Fin n) K)
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v))
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
    rw [hgg] at e
    rw [← e]
    exact hgL _ (hA.1 _)
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA.2 _ (hg'L v hv), hgg]

theorem stabilizer_le_normalizer_elationSubgroup (L : Submodule K (Fin n → K)) :
    stabilizer L ≤
      Subgroup.normalizer (elationSubgroup L : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro A
  refine ⟨fun hA => mem_elationSubgroup_of_mem (conj_mem_elationGenerators hg
    (mem_elationGenerators_of_mem hA)), fun hA => ?_⟩
  have := conj_mem_elationGenerators (inv_mem hg) (mem_elationGenerators_of_mem hA)
  rw [inv_inv, show g⁻¹ * (g * A * g⁻¹) * g = A by group] at this
  exact mem_elationSubgroup_of_mem this

theorem mem_of_forall_mem_elationSubgroup {L : Submodule K (Fin n → K)} (hL : L ≠ ⊥)
    {v : Fin n → K} (hv : ∀ A ∈ elationSubgroup L, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = v) :
    v ∈ L := by
  classical
  by_contra hvL
  obtain ⟨φ, hφv, hLφ⟩ := Submodule.exists_le_ker_of_notMem hvL
  obtain ⟨ℓ, hℓL, hℓ0⟩ := (Submodule.ne_bot_iff L).mp hL
  set r : Fin n → K := fun j => φ (Pi.single j 1) with hr
  have hφ : ∀ w, φ w = r ⬝ᵥ w := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ φ w, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm, hr]
    congr 2
    funext k
    simp [Pi.single_apply, eq_comm]
  have hφL : ∀ w ∈ L, φ w = 0 := fun w hw => hLφ hw
  set M : Matrix (Fin n) (Fin n) K := 1 + vecMulVec ℓ r with hM
  have hMv : ∀ w, M *ᵥ w = w + φ w • ℓ := fun w => by
    rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, hφ, op_smul_eq_smul]
  have hdet : M.det = 1 := by
    rw [hM, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, ← hφ, hφL ℓ hℓL,
      add_zero]
  have hA : (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin n) K) ∈ elationGenerators L := by
    refine mem_elationGenerators_iff.mpr ⟨fun w => ?_, fun w hw => ?_⟩
    · change M *ᵥ w - w ∈ L
      rw [hMv, add_sub_cancel_left]
      exact L.smul_mem _ hℓL
    · change M *ᵥ w = w
      rw [hMv, hφL w hw, zero_smul, add_zero]
  have := hv _ (mem_elationSubgroup_of_mem hA)
  change M *ᵥ v = v at this
  rw [hMv, add_eq_left] at this
  exact hφv ((smul_eq_zero.mp this).resolve_right hℓ0)

theorem elationSubgroup_le_stabilizer (L : Submodule K (Fin n → K)) :
    elationSubgroup L ≤ stabilizer L := fun A hA => mem_stabilizer_of_map_le (by
  rintro _ ⟨w, hw, rfl⟩
  change (A : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ L
  rw [(mem_elationGenerators_iff.mp (mem_elationGenerators_of_mem hA)).2 w hw]
  exact hw)

def fixedSubspace (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) :
    Submodule K (Fin n → K) where
  carrier := {v | ∀ g ∈ X, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := fun ha hb g hg => by rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => Matrix.mulVec_zero _
  smul_mem' := fun c v hv g hg => by rw [Matrix.mulVec_smul, hv g hg]

theorem mem_fixedSubspace {X : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)} {v : Fin n → K} :
    v ∈ fixedSubspace X ↔ ∀ g ∈ X, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  Iff.rfl

theorem fixedSubspace_ne_bot [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 1 ≤ n)
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)} (hX : IsPGroup p X) :
    fixedSubspace X ≠ ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hpK : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← CharP.cast_eq_zero_iff K p]
    exact FiniteField.cast_card_eq_zero K
  have hdvd : p ∣ Nat.card (Fin n → K) := by
    rw [Nat.card_fun, Nat.card_fin]
    exact dvd_pow hpK (by omega)
  obtain ⟨b, hb, hb0⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin n → K) hdvd
    (a := 0) (MulAction.mem_fixedPoints.mpr fun g => Matrix.mulVec_zero _)
  rw [Submodule.ne_bot_iff]
  exact ⟨b, fun g hg => MulAction.mem_fixedPoints.mp hb ⟨g, hg⟩, hb0.symm⟩

end CFSG.AGLEmbedding.LinearThreeKit
