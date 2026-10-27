module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisPhan

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem eq_top_of_shift_of_heisB12_le (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    {Q : Subgroup (unitarySU ℓ f K 3)} {s : unitarySU ℓ f K 3}
    (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS) (hsc : s ∈ Q)
    (hB : heisB12 ℓ f K ≤ Q) : Q = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  let ε : Su K ℓ f 3 ≃* unitarySU ℓ f K 3 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3)
  have hε : ∀ x : Su K ℓ f 3, ((ε x : unitarySU ℓ f K 3) : GL (Fin 3) K) = (x : GL (Fin 3) K) :=
    fun x => rfl
  have hmem2 : ∀ x : Su K ℓ f 2, ((x : GL (Fin 2) K)) ∈ unitarySU ℓ f K 2 := fun x => by
    exact (Subgroup.ext_iff.1 (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2)
      (x : GL (Fin 2) K)).1 x.2
  have h0 : ∀ x : Su K ℓ f 2, ε (blockEmb2 K ℓ f 2 0 x) ∈ Q := fun x => by
    apply hB
    rw [mem_heisB12]
    refine ⟨(x : GL (Fin 2) K), hmem2 x, ?_⟩
    rw [hε, blockEmb2, coe_coe_blockEmb]
    change blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [blockMat_zero_eq]
    rfl
  have h1 : ∀ x : Su K ℓ f 2, ε (blockEmb2 K ℓ f 2 1 x) ∈ Q := fun x => by
    have e : ε (blockEmb2 K ℓ f 2 1 x) = s * ε (blockEmb2 K ℓ f 2 0 x) * s⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      have hs' : (((s⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          hSᵀ := by
        rw [val_inv_eq_star h s, hs]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hS]
      rw [hε, blockEmb2, coe_coe_blockEmb, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, hs', hs, hε, blockEmb2, coe_coe_blockEmb]
      change blockMat 3 1 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        hS * blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * hSᵀ
      rw [blockMat_one_eq, blockMat_zero_eq]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsc (h0 x)) (Subgroup.inv_mem _ hsc)
  have hgen : ⨆ i : Fin 2, (ε.toMonoidHom.comp (blockEmb2 K ℓ f 2 i)).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) hK hq 2
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [MonoidHom.range_comp] using h2
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun i => ?_
  rintro _ ⟨x, rfl⟩
  fin_cases i
  · exact h0 x
  · exact h1 x

end CFSG.LieType.SeitzGeneration
