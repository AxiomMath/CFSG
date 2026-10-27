module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag
open Matrix

theorem exists_eq_weight_of_isotropic {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {n : ℕ} {ι : Type} {X : ι → GL (Fin n) K} {R : GL (Fin n) K}
    (hR : R ∈ primeFormUnitary h (idGram K n)) {d : ι → Fin n → K}
    (hd : ∀ a, ((R * X a * R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (d a))
    {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥) (hiso : W ≤ W.orthogonalBilin (idForm h n))
    (hWX : ∀ a, ∀ w ∈ W, ((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    ∃ i j, i ≠ j ∧ ∀ a, d a i = d a j := by
  classical
  have hRX : ∀ a w, (R : Matrix (Fin n) (Fin n) K) *ᵥ
      (((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      diagonal (d a) *ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) := by
    intro a w
    rw [← hd a, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec,
      Matrix.mul_assoc _ _ (R : Matrix (Fin n) (Fin n) K), Units.inv_mul, Matrix.mul_one]
  have hinj : ∀ u : Fin n → K, (R : Matrix (Fin n) (Fin n) K) *ᵥ u = 0 → u = 0 := fun u hu => by
    have e := congrArg (fun v => ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) hu
    simpa [mulVec_mulVec, Units.inv_mul] using e
  have hex : ∃ k, ∃ w ∈ W, w ≠ 0 ∧
      (Finset.univ.filter fun l => ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) l ≠ 0).card = k := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨_, w, hw, hw0, rfl⟩
  obtain ⟨w, hw, hw0, hk⟩ := Nat.find_spec hex
  have hv0 : (R : Matrix (Fin n) (Fin n) K) *ᵥ w ≠ 0 := fun h0 => hw0 (hinj w h0)
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) l₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv0 (funext hall)
  have hsupp : ∀ a l, ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) l ≠ 0 → d a l = d a l₀ := by
    intro a l hl
    by_contra hne
    have huW : ((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w - d a l₀ • w ∈ W :=
      W.sub_mem (hWX a w hw) (W.smul_mem _ hw)
    have hRu : ∀ m, ((R : Matrix (Fin n) (Fin n) K) *ᵥ
        (((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w - d a l₀ • w)) m =
        (d a m - d a l₀) * ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) m := fun m => by
      rw [mulVec_sub, mulVec_smul, hRX, Pi.sub_apply, mulVec_diagonal, Pi.smul_apply,
        smul_eq_mul, sub_mul]
    have hu0 : ((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w - d a l₀ • w ≠ 0 := by
      intro h0
      have := hRu l
      rw [h0, mulVec_zero, Pi.zero_apply] at this
      exact mul_ne_zero (sub_ne_zero.2 hne) hl (this.symm)
    have hlt : (Finset.univ.filter fun m => ((R : Matrix (Fin n) (Fin n) K) *ᵥ
        (((X a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w - d a l₀ • w)) m ≠ 0).card <
        Nat.find hex := by
      rw [← hk]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun m hm => ?_).2
        ⟨l₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl₀⟩, fun hm => ?_⟩)
      · rw [Finset.mem_filter, hRu] at hm
        exact Finset.mem_filter.2 ⟨hm.1, right_ne_zero_of_mul hm.2⟩
      · rw [Finset.mem_filter, hRu, sub_self, zero_mul] at hm
        exact hm.2 rfl
    exact Nat.find_min hex hlt ⟨_, huW, hu0, rfl⟩
  by_cases hone : ∃ j, j ≠ l₀ ∧ ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) j ≠ 0
  · obtain ⟨j, hj, hvj⟩ := hone
    exact ⟨j, l₀, hj, fun a => hsupp a j hvj⟩
  exfalso
  push Not at hone
  have h1 : idForm h n w w = 0 := hiso hw w hw
  have h2 : idForm h n ((R : Matrix (Fin n) (Fin n) K) *ᵥ w)
      ((R : Matrix (Fin n) (Fin n) K) *ᵥ w) = idForm h n w w :=
    (mem_sesqUnitaryGroup.mp (toLinU_mem ⟨R, hR⟩)) w w
  rw [h1, gramForm_apply, idGram, Units.val_one, one_mulVec, dotProduct,
    Finset.sum_eq_single l₀ (fun b _ hb => by rw [hone b hb, mul_zero])
      (fun h0 => absurd (Finset.mem_univ l₀) h0)] at h2
  exact mul_ne_zero ((map_ne_zero h.bar).2 hl₀) hl₀ h2

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
