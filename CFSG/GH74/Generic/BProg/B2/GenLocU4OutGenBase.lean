module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic
public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K] {p f : ℕ}

@[expose] noncomputable def suOf (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    ↥(StatedSU 4 q K) :=
  ⟨⟨M, (M.map (· ^ q))ᵀ, mul_eq_one_comm.1 hM, hM⟩, Subgroup.subset_closure ⟨hdet, hM⟩⟩

theorem coe_suOf (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    (((suOf q M hM hdet : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M := rfl

theorem coe_inv_suOf (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    ((((suOf q M hM hdet : ↥(StatedSU 4 q K)) : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (M.map (· ^ q))ᵀ :=
  Units.inv_eq_of_mul_eq_one_left hM

theorem exists_norm_neg_one [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ ξ : K, ξ ^ (p ^ f) * ξ = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hfix : unitaryInvolution K p f (-1) = -1 := by
    rw [map_neg, map_one]
  obtain ⟨l, hl⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix (neg_ne_zero.2 one_ne_zero)
  exact ⟨l, by rw [unitaryInvolution_apply] at hl; exact hl⟩

theorem commute_diag_of_block {q : ℕ} (i : ℕ) (d : Fin 4 → K)
    (hd : ∀ a b : Fin 4, (i ≤ a.val ∧ a.val < i + 2) → (i ≤ b.val ∧ b.val < i + 2) → d a = d b)
    (g : ↥(StatedSU 4 q K)) (hg : GenLocU4Gen.InBlock q (1 : GL (Fin 4) K) i g) :
    Matrix.diagonal d * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d := by
  obtain ⟨B, -, -, hB⟩ := hg
  have hg1 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = CFSG.ClassicalInvolution.Phan.blockMat 4 i B := by
    simpa using hB
  rw [hg1]
  exact GenLocDiagU.blockMat_commute_diag hd B

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
