module

public import CFSG.LieType.Ree.SuzukiNormInversion
public import CFSG.LieType.Ree.SuzukiOvoidTorus

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable (a : ℕ) (K : Type) [Field K]

@[expose] noncomputable def suzukiWElt : suzukiGroup a K :=
  ⟨⟨suzukiW K, suzukiW K, suzukiW_mul_self K, suzukiW_mul_self K⟩,
    Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem coe_suzukiWElt :
    (((suzukiWElt a K : suzukiGroup a K) : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = suzukiW K :=
  rfl

theorem suzukiW_mulVec (x : Fin 4 → K) : suzukiW K *ᵥ x = ![x 3, x 2, x 1, x 0] := by
  ext i
  fin_cases i <;> simp [suzukiW, mulVec, dotProduct, Fin.sum_univ_four]

variable {K}

theorem suzuki_ovoid_weyl_action
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiWElt a K • suzukiInfty K = suzukiLine a K 0 0 ∧
    suzukiWElt a K • suzukiLine a K 0 0 = suzukiInfty K ∧
    ∀ u v : K, (u, v) ≠ (0, 0) → suzukiWElt a K • suzukiLine a K u v =
      suzukiLine a K (v / suzukiN a u v) (u / suzukiN a u v) := by
  have hN0 : suzukiN a (0 : K) 0 = 0 := ((suzuki_norm_nonzero a K hK 0 0).2 ⟨rfl, rfl⟩)
  refine ⟨suzuki_smul_mk_eq a _ _ _ 1 ?_, suzuki_smul_mk_eq a _ _ _ 1 ?_, fun u v huv => ?_⟩
  · rw [coe_suzukiWElt, suzukiW_mulVec]
    ext i
    fin_cases i <;> simp [hN0]
  · rw [coe_suzukiWElt, suzukiW_mulVec]
    ext i
    fin_cases i <;> simp [hN0]
  · have ht : suzukiN a u v ≠ 0 := fun h => huv (Prod.ext
      ((suzuki_norm_nonzero a K hK u v).1 h).1 ((suzuki_norm_nonzero a K hK u v).1 h).2)
    have hinv := (suzuki_norm_inversion a hK).2 u v huv
    refine suzuki_smul_mk_eq a _ _ _ (Units.mk0 _ ht) ?_
    rw [coe_suzukiWElt, suzukiW_mulVec]
    ext i
    fin_cases i <;> simp [hinv, Units.smul_def, mul_div_cancel₀ _ ht, ht]

end CFSG.LieType.Ree
