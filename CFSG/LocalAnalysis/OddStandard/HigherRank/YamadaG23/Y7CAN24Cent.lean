module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24El
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24H1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

theorem n24_cent_norm (c : GL (Fin 6) (ZMod 2)) (hc : c * z₀ = z₀ * c)
    (hn : ∀ d ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range,
      c * d * c⁻¹ ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range) : c ∈ B₀ := by
  obtain ⟨P, Q, rfl⟩ := exists_n24El_of_comm c hc
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin 3) (Fin 3) (ZMod 2),
      m = ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Q := ⟨_, rfl⟩
  have hQ : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m = Q := by
    rw [hm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcP : n24El P Q = dg P * n24El 1 m := by
    rw [dg_eq_n24El, n24El_mul, hQ]
    simp
  have hu_mem : ∀ d ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range,
      n24El 1 m * d * (n24El 1 m)⁻¹ ∈
        (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range := by
    intro d hd
    have h1 := hn d hd
    rw [hcP] at h1
    have e : n24El 1 m * d * (n24El 1 m)⁻¹ =
        (dg P)⁻¹ * (dg P * n24El 1 m * d * (dg P * n24El 1 m)⁻¹) * dg P := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨P, rfl⟩) h1) ⟨P, rfl⟩
  have hcomm : ∀ A : GL (Fin 3) (ZMod 2),
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m = m * (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro A
    obtain ⟨A', hA'⟩ := hu_mem (dg A) ⟨A, rfl⟩
    have e : n24El 1 m * dg A * (n24El 1 m)⁻¹ = n24El A
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m +
          m * (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
      rw [dg_eq_n24El, n24El_inv, n24El_mul, n24El_mul]
      simp
    rw [e, dg_eq_n24El] at hA'
    exact n24_eq_of_add_eq_zero (n24El_inj.1 hA').2.symm
  have hfix : ∀ A : GL (Fin 3) (ZMod 2), n24Cj A m = m := by
    intro A
    unfold n24Cj
    rw [hcomm A, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hcP]
  rcases n24_commutant m (hfix n24A) (hfix n24B) with h0 | h1
  · rw [h0, n24El_one, mul_one]
    exact mem_B₀_iff_dg.2 ⟨P, Or.inl rfl⟩
  · rw [h1, ← z0_eq_n24El]
    exact mem_B₀_iff_dg.2 ⟨P, Or.inr rfl⟩

end CFSG.OddStandard.HigherRank.YamadaG23
